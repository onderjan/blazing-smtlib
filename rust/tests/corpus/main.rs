//! Corpus-wide sweeps: every `.smt2` file under the corpus root is processed
//! in parallel.
//!
//! Expects the SMT-LIB corpus under `benchmarks/2025` in the repository root;
//! set the environment variable `SMT_BENCHMARKS_DIR` to use a corpus root
//! elsewhere. Both sweeps are ignored by default.
//!
//! `parse_corpus` parses every file and reports the failures:
//! `cargo test --release parse_corpus -- --ignored`.
//!
//! `trace_corpus` parses every file with a handler that hashes every callback
//! it receives (see `trace_hash.rs` beside this file), producing one line per file, so
//! that two revisions of the parser can be compared on the whole corpus:
//! `cargo test --release trace_corpus -- --ignored`. Environment variables:
//!
//! - `SMT_TRACE_OUT`: path of a file to write the lines to, sorted by path:
//!   the hash as 16 hex digits, or `ERR: ` and the error description for a
//!   file that does not parse, then a tab, then the path relative to the
//!   corpus root.
//! - `SMT_TRACE_BASE`: path of such a file written by a previous run; the
//!   test then fails if any file's line differs, or if the sets of files
//!   differ, and prints examples of each kind of difference.
//!
//! Without either variable the test only prints the digest of all lines,
//! which is enough for a quick same-or-different check between two runs.

mod trace_hash;

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::panic::AssertUnwindSafe;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use rayon::ThreadPoolBuilder;
use rayon::prelude::*;
use smt_parser_rs::{
    CheckStandardSyntax, NonstandardCommandError,
    read::{SmtReadError, SmtReadErrorKind, read_smt_file},
};
use trace_hash::TraceHash;

/// How often the progress ticker prints, and also the in-flight time
/// after which a file is considered long-running and worth naming.
const TICK: Duration = Duration::from_secs(10);

/// Examples printed per class of failure or difference.
const EXAMPLES: usize = 3;

/// Collects the `.smt2` files under the root with their sizes,
/// returning the files and the total size.
fn collect_smt2_files(root: &Path) -> (Vec<(PathBuf, u64)>, u64) {
    let mut out = Vec::new();
    let mut total_bytes = 0;
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let entries = match fs::read_dir(&dir) {
            Ok(e) => e,
            Err(_) => continue,
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|ext| ext == "smt2") {
                let size = entry.metadata().map_or(0, |metadata| metadata.len());
                total_bytes += size;
                out.push((path, size));
            }
        }
    }
    (out, total_bytes)
}

#[derive(Debug)]
struct FailureRecord {
    path: PathBuf,
    error: String,
}

fn parse_file(path: &Path) -> Result<(), SmtReadError<NonstandardCommandError>> {
    read_smt_file(&mut CheckStandardSyntax, path)?;
    Ok(())
}

/// Parses the file with the hashing handler, returning the digest.
fn trace_file(path: &Path) -> Result<u64, SmtReadError<NonstandardCommandError>> {
    let mut handler = TraceHash::new();
    read_smt_file(&mut handler, path)?;
    Ok(handler.digest())
}

thread_local! {
    /// Location of the last panic on this thread, captured by the silencing
    /// panic hook: the payload seen by `catch_unwind` carries only the
    /// message, the location is only available inside the hook.
    static LAST_PANIC_LOCATION: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// Runs the file processor, turning read errors and panics into descriptions.
fn try_run_file<T>(
    path: &Path,
    run: impl FnOnce(&Path) -> Result<T, SmtReadError<NonstandardCommandError>>,
) -> Result<T, String> {
    // guard from panics and return an error instead; the hook installed by
    // the sweep silences the default printing and captures the location
    let result = std::panic::catch_unwind(AssertUnwindSafe(|| run(path)));

    match result {
        Ok(Ok(value)) => Ok(value),
        Ok(Err(e)) => match e.kind() {
            SmtReadErrorKind::Lexer(err) => Err(format!("Lexer error: {:?}", err)),
            SmtReadErrorKind::Parser(err) => Err(format!("Parser error: {:?}", err)),
            SmtReadErrorKind::Io(err) => Err(format!("Read error: {:?}", err)),
            SmtReadErrorKind::Handler(err) => Err(format!("Nonstandard command: {:?}", err.0)),
        },
        Err(cause) => {
            let msg = match cause.downcast_ref::<&'static str>() {
                Some(s) => *s,
                None => match cause.downcast_ref::<String>() {
                    Some(s) => &s[..],
                    None => "(not a string)",
                },
            };
            Err(match LAST_PANIC_LOCATION.with(|l| l.borrow_mut().take()) {
                Some(location) => format!("Panic: {} at {}", msg, location),
                None => format!("Panic: {}", msg),
            })
        }
    }
}

fn gigabytes(bytes: u64) -> f64 {
    bytes as f64 / 1e9
}

/// The corpus root and its files.
struct Corpus {
    root: PathBuf,
    files: Vec<(PathBuf, u64)>,
    total_bytes: u64,
}

impl Corpus {
    fn locate() -> Self {
        let root = match std::env::var_os("SMT_BENCHMARKS_DIR") {
            Some(dir) => PathBuf::from(dir),
            None => Path::new(env!("CARGO_MANIFEST_DIR")).join("../benchmarks/2025"),
        };
        assert!(
            root.exists(),
            "benchmark corpus not found at {}; unpack the SMT-LIB corpus there \
             or set SMT_BENCHMARKS_DIR to its root",
            root.display()
        );
        let (files, total_bytes) = collect_smt2_files(&root);
        assert!(!files.is_empty(), "expected .smt2 files under {:?}", root);
        Self {
            root,
            files,
            total_bytes,
        }
    }

    /// Paths are reported relative to the corpus root for readability.
    fn relative(&self, path: &Path) -> String {
        path.strip_prefix(&self.root)
            .unwrap_or(path)
            .display()
            .to_string()
    }

    /// Runs the processor over every file in parallel with a progress
    /// ticker, returning the results of the files that succeeded and the
    /// failures of those that did not.
    fn sweep<T: Send>(
        &self,
        run: impl Fn(&Path) -> Result<T, String> + Sync,
    ) -> (Vec<(PathBuf, T)>, Vec<FailureRecord>) {
        let num_files = self.files.len();
        eprintln!(
            "Processing {} .smt2 files ({:.1} GB)",
            num_files,
            gigabytes(self.total_bytes)
        );

        let processed_files = AtomicUsize::new(0);
        let processed_bytes = AtomicU64::new(0);
        let results = Mutex::new(Vec::<(PathBuf, T)>::new());
        let failures = Mutex::new(Vec::<FailureRecord>::new());
        // files currently being processed, so stalls on giant files can be named
        let in_flight: Mutex<HashMap<&Path, Instant>> = Mutex::new(HashMap::new());
        let done = AtomicBool::new(false);

        let start = Instant::now();

        // stop panics from printing individually, but capture the location,
        // which the payload later caught by try_run_file does not carry
        let previous_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(|info| {
            let location = info.location().map(|location| location.to_string());
            LAST_PANIC_LOCATION.with(|l| *l.borrow_mut() = location);
        }));

        let pool = ThreadPoolBuilder::new()
            .thread_name(|i| format!("processing-thread-{}", i))
            .build()
            .unwrap();

        std::thread::scope(|scope| {
            // progress ticker: prints on wall-clock time, not on file completions,
            // so progress stays visible while every worker sits on a giant file
            scope.spawn(|| {
                let mut last_print = Instant::now();
                while !done.load(Ordering::Relaxed) {
                    std::thread::sleep(Duration::from_secs(1));
                    if last_print.elapsed() < TICK || done.load(Ordering::Relaxed) {
                        continue;
                    }
                    last_print = Instant::now();

                    let files_done = processed_files.load(Ordering::Relaxed);
                    let bytes_done = processed_bytes.load(Ordering::Relaxed);
                    let num_failures = failures.lock().unwrap().len();
                    let elapsed = start.elapsed().as_secs_f64();
                    eprintln!(
                        "{:>5.0}s: {:.1}% of files ({}/{}), {:.1}% of bytes ({:.1}/{:.1} GB), \
                         {} failures, {:.0} MB/s",
                        elapsed,
                        100.0 * files_done as f64 / num_files as f64,
                        files_done,
                        num_files,
                        100.0 * bytes_done as f64 / self.total_bytes as f64,
                        gigabytes(bytes_done),
                        gigabytes(self.total_bytes),
                        num_failures,
                        bytes_done as f64 / 1e6 / elapsed,
                    );

                    let in_flight = in_flight.lock().unwrap();
                    if let Some((path, started)) =
                        in_flight.iter().min_by_key(|(_, started)| **started)
                        && started.elapsed() >= TICK
                    {
                        eprintln!(
                            "  longest in flight: {} ({:.0}s)",
                            self.relative(path),
                            started.elapsed().as_secs_f64()
                        );
                    }
                }
            });

            pool.install(|| {
                self.files.par_iter().for_each(|(path, size)| {
                    in_flight.lock().unwrap().insert(path, Instant::now());
                    let result = run(path);
                    in_flight.lock().unwrap().remove(path.as_path());

                    match result {
                        Ok(value) => results.lock().unwrap().push((path.clone(), value)),
                        Err(error) => failures.lock().unwrap().push(FailureRecord {
                            path: path.clone(),
                            error,
                        }),
                    }
                    processed_files.fetch_add(1, Ordering::Relaxed);
                    processed_bytes.fetch_add(*size, Ordering::Relaxed);
                });
            });

            done.store(true, Ordering::Relaxed);
        });

        std::panic::set_hook(previous_hook);

        let elapsed = start.elapsed().as_secs_f64();
        eprintln!(
            "Processed {} files ({:.1} GB) in {:.1}s ({:.0} MB/s)",
            num_files,
            gigabytes(self.total_bytes),
            elapsed,
            self.total_bytes as f64 / 1e6 / elapsed,
        );

        let mut failures = failures.into_inner().unwrap();
        failures.sort_by(|a, b| a.path.cmp(&b.path));
        (results.into_inner().unwrap(), failures)
    }

    /// Prints the failures grouped into classes by their error description,
    /// keeping a few deterministic example paths for each.
    fn report_failures(&self, failures: &[FailureRecord]) {
        if failures.is_empty() {
            eprintln!("No failures");
            return;
        }
        let mut classes: BTreeMap<&str, (usize, Vec<&Path>)> = BTreeMap::new();
        for f in failures {
            let (count, examples) = classes.entry(f.error.as_str()).or_default();
            *count += 1;
            if examples.len() < EXAMPLES {
                examples.push(&f.path);
            }
        }
        let mut classes: Vec<_> = classes.into_iter().collect();
        classes.sort_by_key(|(_, (count, _))| std::cmp::Reverse(*count));

        eprintln!(
            "Number of failures: {} in {} classes:",
            failures.len(),
            classes.len()
        );
        for (error, (count, examples)) in classes {
            eprintln!("{count:8}  {error}");
            for example in examples {
                eprintln!("          e.g. {}", self.relative(example));
            }
        }
    }
}

#[test]
#[ignore]
fn parse_corpus() {
    let corpus = Corpus::locate();
    let (_, failures) = corpus.sweep(|path| try_run_file(path, parse_file));
    corpus.report_failures(&failures);
    if !failures.is_empty() {
        panic!("{} failures parsing the corpus", failures.len());
    }
}

/// Reads a trace file into a map from relative path to line content.
fn read_trace(path: &Path) -> BTreeMap<String, String> {
    let content = fs::read_to_string(path)
        .unwrap_or_else(|err| panic!("cannot read trace file {}: {}", path.display(), err));
    content
        .lines()
        .map(|line| {
            let (content, path) = line
                .rsplit_once('\t')
                .unwrap_or_else(|| panic!("trace line without a tab: {line:?}"));
            (path.to_string(), content.to_string())
        })
        .collect()
}

#[test]
#[ignore]
fn trace_corpus() {
    let corpus = Corpus::locate();
    let (results, failures) = corpus.sweep(|path| try_run_file(path, trace_file));
    corpus.report_failures(&failures);

    // one line per file: the digest, or the error description
    let mut lines: BTreeMap<String, String> = results
        .iter()
        .map(|(path, digest)| (corpus.relative(path), format!("{digest:016x}")))
        .collect();
    for failure in &failures {
        lines.insert(
            corpus.relative(&failure.path),
            format!("ERR: {}", failure.error),
        );
    }

    // the digest of all lines identifies the whole run
    let mut overall = TraceHash::new();
    let mut text = String::new();
    for (path, content) in &lines {
        text.push_str(content);
        text.push('\t');
        text.push_str(path);
        text.push('\n');
    }
    overall.fold(text.as_bytes());
    eprintln!(
        "Trace of {} files: overall digest {:016x}",
        lines.len(),
        overall.digest()
    );

    if let Some(out) = std::env::var_os("SMT_TRACE_OUT") {
        let out = PathBuf::from(out);
        fs::write(&out, &text)
            .unwrap_or_else(|err| panic!("cannot write trace file {}: {}", out.display(), err));
        eprintln!("Trace written to {}", out.display());
    }

    let Some(base) = std::env::var_os("SMT_TRACE_BASE") else {
        return;
    };
    let base = PathBuf::from(base);
    let baseline = read_trace(&base);
    eprintln!(
        "Comparing against {} ({} files)",
        base.display(),
        baseline.len()
    );

    let mut missing_in_base = Vec::new();
    let mut missing_in_current = Vec::new();
    let mut different = Vec::new();
    for (path, content) in &lines {
        match baseline.get(path) {
            None => missing_in_base.push(path),
            Some(base_content) if base_content != content => {
                different.push((path, base_content, content))
            }
            Some(_) => {}
        }
    }
    for path in baseline.keys() {
        if !lines.contains_key(path) {
            missing_in_current.push(path);
        }
    }

    let num_differences = missing_in_base.len() + missing_in_current.len() + different.len();
    if num_differences == 0 {
        eprintln!("No differences from the baseline");
        return;
    }
    eprintln!(
        "{} files differ from the baseline: {} only in this run, {} only in the baseline, \
         {} with different content",
        num_differences,
        missing_in_base.len(),
        missing_in_current.len(),
        different.len()
    );
    for path in missing_in_base.iter().take(EXAMPLES) {
        eprintln!("  only in this run: {path}");
    }
    for path in missing_in_current.iter().take(EXAMPLES) {
        eprintln!("  only in the baseline: {path}");
    }
    for (path, base_content, content) in different.iter().take(EXAMPLES) {
        eprintln!("  {path}\n    baseline: {base_content}\n    this run: {content}");
    }
    panic!("{} files differ from the baseline trace", num_differences);
}

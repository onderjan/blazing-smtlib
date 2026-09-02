//! Corpus-wide parse sweep: parses every `.smt2` file under the corpus root
//! in parallel and reports the failures.
//!
//! Expects the SMT-LIB corpus under `benchmarks/2025` in the repository root;
//! set the environment variable `SMT_BENCHMARKS_DIR` to use a corpus root
//! elsewhere. Ignored by default; run with
//! `cargo test --release parse_corpus -- --ignored`.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::fs;
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

/// How often the progress ticker prints, and also the in-flight time
/// after which a file is considered long-running and worth naming.
const TICK: Duration = Duration::from_secs(10);

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

thread_local! {
    /// Location of the last panic on this thread, captured by the silencing
    /// panic hook: the payload seen by `catch_unwind` carries only the
    /// message, the location is only available inside the hook.
    static LAST_PANIC_LOCATION: RefCell<Option<String>> = const { RefCell::new(None) };
}

fn try_parse_file(path: &Path) -> Result<(), String> {
    // guard from panics and return an error instead; the hook installed by
    // the test silences the default printing and captures the location
    let result = std::panic::catch_unwind(|| parse_file(path));

    match result {
        Ok(Ok(())) => Ok(()),
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

#[test]
#[ignore]
fn parse_corpus() {
    let benchmarks = match std::env::var_os("SMT_BENCHMARKS_DIR") {
        Some(dir) => PathBuf::from(dir),
        None => Path::new(env!("CARGO_MANIFEST_DIR")).join("benchmarks/2025"),
    };
    assert!(
        benchmarks.exists(),
        "benchmark corpus not found at {}; unpack the SMT-LIB corpus there \
         or set SMT_BENCHMARKS_DIR to its root",
        benchmarks.display()
    );
    // paths are reported relative to the corpus root for readability
    let relative = |path: &'_ Path| -> String {
        path.strip_prefix(&benchmarks).unwrap_or(path).display().to_string()
    };

    let (files, total_bytes) = collect_smt2_files(&benchmarks);
    let num_files = files.len();
    assert!(num_files > 0, "expected .smt2 files under {:?}", benchmarks);
    eprintln!(
        "Processing {} .smt2 files ({:.1} GB)",
        num_files,
        gigabytes(total_bytes)
    );

    let processed_files = AtomicUsize::new(0);
    let processed_bytes = AtomicU64::new(0);
    let failures = Mutex::new(Vec::<FailureRecord>::new());
    // files currently being parsed, so stalls on giant files can be named
    let in_flight: Mutex<HashMap<&Path, Instant>> = Mutex::new(HashMap::new());
    let done = AtomicBool::new(false);

    let start = Instant::now();

    // stop panics from printing individually, but capture the location,
    // which the payload later caught by try_parse_file does not carry
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
                    100.0 * bytes_done as f64 / total_bytes as f64,
                    gigabytes(bytes_done),
                    gigabytes(total_bytes),
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
                        relative(path),
                        started.elapsed().as_secs_f64()
                    );
                }
            }
        });

        pool.install(|| {
            files.par_iter().for_each(|(path, size)| {
                in_flight.lock().unwrap().insert(path, Instant::now());
                let result = try_parse_file(path);
                in_flight.lock().unwrap().remove(path.as_path());

                if let Err(error) = result {
                    failures.lock().unwrap().push(FailureRecord {
                        path: path.clone(),
                        error,
                    });
                }
                processed_files.fetch_add(1, Ordering::Relaxed);
                processed_bytes.fetch_add(*size, Ordering::Relaxed);
            });
        });

        done.store(true, Ordering::Relaxed);
    });

    std::panic::set_hook(previous_hook);

    let elapsed = start.elapsed().as_secs_f64();
    let mut failures = failures.into_inner().unwrap();

    eprintln!(
        "Processed {} files ({:.1} GB) in {:.1}s ({:.0} MB/s)",
        num_files,
        gigabytes(total_bytes),
        elapsed,
        total_bytes as f64 / 1e6 / elapsed,
    );

    if failures.is_empty() {
        eprintln!("No failures");
    } else {
        // group the failures into classes by their error description,
        // keeping a few deterministic example paths for each
        failures.sort_by(|a, b| a.path.cmp(&b.path));
        let mut classes: BTreeMap<&str, (usize, Vec<&Path>)> = BTreeMap::new();
        for f in &failures {
            let (count, examples) = classes.entry(f.error.as_str()).or_default();
            *count += 1;
            if examples.len() < 3 {
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
                eprintln!("          e.g. {}", relative(example));
            }
        }
        panic!("{} failures parsing the corpus", failures.len());
    }
}

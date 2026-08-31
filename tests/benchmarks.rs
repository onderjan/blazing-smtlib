use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

use rayon::ThreadPoolBuilder;
use smt_parser_rs::{
    CheckStandardSyntax,
    read::{SmtReadError, SmtReadErrorKind, read_smt_file},
};

fn collect_smt2_files(root: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
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
                out.push(path);
            }
        }
    }
    out
}

#[derive(Debug)]
struct FailureRecord {
    path: PathBuf,
    error: String,
}

fn parse_file(path: &Path) -> Result<(), SmtReadError<CheckStandardSyntax>> {
    read_smt_file(&mut CheckStandardSyntax, path)?;
    Ok(())
}

fn try_parse_file(path: &Path) -> Result<(), String> {
    // try to guard from panics and return an error instead

    let result = std::panic::catch_unwind(|| parse_file(path));

    match result {
        Ok(Ok(_ast)) => Ok(()),
        Ok(Err(e)) => match e.into_kind() {
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
            Err(format!("Panic: {}", msg))
        }
    }
}

#[test]
#[ignore]
fn parse_benchmarks() {
    let benchmarks = std::env::var("SMT_BENCHMARKS_DIR")
        .expect("Set SMT_BENCHMARKS_DIR to point at a directory of .smt2 files");
    let benchmarks = PathBuf::from(benchmarks);

    let files = collect_smt2_files(&benchmarks);
    let num_files = files.len();
    assert!(num_files > 0, "Expected .smt2 files under {:?}", benchmarks);
    eprintln!("Found {} .smt2 files", num_files);

    let processed = AtomicUsize::new(0);
    let failures = Mutex::new(Vec::<FailureRecord>::new());

    eprintln!("Processing {} files", num_files);

    let start = Instant::now();

    // stop panics from printing by adding a hook, this could be done more elegantly
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));

    let pool = ThreadPoolBuilder::new()
        .thread_name(|i| format!("processing-thread-{}", i))
        .build()
        .unwrap();

    use rayon::prelude::*;
    pool.in_place_scope(|_scope| {
        files
            .par_iter()
            .for_each(|path| match try_parse_file(path) {
                Ok(()) => {
                    let num_processed = processed.fetch_add(1, Ordering::Relaxed) + 1;
                    if num_processed != 0 && num_processed.is_multiple_of(1000) {
                        let elapsed = start.elapsed();
                        let num_failures = failures.lock().unwrap().len();
                        eprintln!(
                            "Processed {}/{} files ({:.2}%) in {:.2}s, num failures: {}",
                            num_processed,
                            num_files,
                            100.0 * num_processed as f64 / num_files as f64,
                            elapsed.as_secs_f64(),
                            num_failures
                        );
                    }
                }
                Err(error) => {
                    failures.lock().unwrap().push(FailureRecord {
                        path: path.clone(),
                        error,
                    });
                }
            });
    });

    std::panic::set_hook(previous_hook);

    let elapsed = start.elapsed();
    let failures = failures.into_inner().unwrap();

    eprintln!(
        "Processed {num_files} files in {:.2}s",
        elapsed.as_secs_f64(),
    );

    if failures.is_empty() {
        eprintln!("No failures");
    } else {
        eprintln!("Number of failures: {}", failures.len());
        eprintln!("First {} failures:", failures.len().min(30));
        for f in failures.iter().take(30) {
            eprintln!("\t{}: {}", f.path.display(), f.error);
        }
        panic!("{} failures parsing benchmarks", failures.len());
    }
}

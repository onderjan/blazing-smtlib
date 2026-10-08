//! Parse-throughput benchmark over pinned SMT-LIB benchmark files.
//!
//! Expects the SMT-LIB corpus under `../benchmarks/2025` in the current
//! directory, which is the repository root under `cargo bench` (tracks
//! unpacked as `non-incremental/<LOGIC>/...` and `incremental/<LOGIC>/...`);
//! set the environment variable `SMT_BENCHMARKS_DIR` to use a corpus root
//! elsewhere. Each file is loaded into memory first, so the numbers measure
//! lexing and parsing only, not disk I/O.
//!
//! Run with `cargo bench --bench parse`. Each file is measured in two modes:
//! lexing only (tokens are discarded by a counting handler) and the full
//! lex-and-parse pipeline. The table reports each mode as throughput in
//! MB/s and as nanoseconds per token: the parser's cost is per token, and
//! bytes per token varies fivefold between files, so MB/s alone hides
//! per-token changes. What the files consist of, and what parsing them
//! allocates, is printed by the `census` bench.
//!
//! Environment variables:
//!
//! - `SMT_BENCH_MODE`: `lex`, `full`, or `both` (default) selects the
//!   measured modes, e.g. to attribute a profile to a single mode.
//! - `SMT_BENCH_FILES`: comma-separated labels (see [`common::FILES`])
//!   restricting the measured files, in the order given.
//! - `SMT_BENCH_ITERATIONS`: timed runs per file and mode (default
//!   [`DEFAULT_ITERATIONS`]); a warm-up run is always added.
//! - `SMT_BENCH_FORMAT`: `table` (default) prints the human-readable table,
//!   `raw` prints one tab-separated line per file and mode with the label,
//!   mode, byte size, and every timed run in seconds, and `list` prints the
//!   selected labels one per line without measuring anything. The `raw` and
//!   `list` formats are the protocol used by the `compare` bench driver.
//!
//! Measured throughput is not the same between runs: expect a few percent of
//! run-to-run drift between two invocations of identical code. To compare
//! two revisions, use `cargo bench --bench compare`, which interleaves the
//! two builds file by file.

mod common;

use std::convert::Infallible;
use std::ops::ControlFlow;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

use blazing_smtlib::{
    lexer::SmtLexer,
    token::{SmtBatchCursor, SmtConsume, SmtVersion},
};

/// Default timed runs per file and mode; an additional first (warm-up) run
/// is discarded.
const DEFAULT_ITERATIONS: usize = 5;

/// Token consumer that only counts tokens, so timed lexing includes no parsing.
struct DiscardTokens {
    tokens: usize,
}

impl SmtConsume for DiscardTokens {
    type Result = ();
    type Error = Infallible;
    const IS_CONCRETE: bool = false;

    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        while cursor.next().is_some() {
            self.tokens += 1;
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Lexes the in-memory file, discarding tokens, and returns the token count.
fn lex_from_memory(data: &[u8], path: &Path) -> usize {
    let mut handler = DiscardTokens { tokens: 0 };
    let mut lexer = SmtLexer::new(&mut handler, SmtVersion::V2_7);
    if let Err(err) = lexer.lex_all(data) {
        panic!("benchmark file {} must lex, got {:?}", path.display(), err);
    }
    handler.tokens
}

/// Minimum total duration of the discarded warm-up runs.
///
/// One run of a large file is enough to warm the caches and the clock up,
/// but a small file takes a few milliseconds per run, and the first runs of
/// a fresh process then measure the frequency ramp instead of the parser.
const WARM_UP_SECONDS: f64 = 0.1;

/// Times the closure over discarded warm-up runs (at least one, and at
/// least [`WARM_UP_SECONDS`] in total) and `iterations` timed runs,
/// returning the run times in seconds in measurement order.
fn time_runs(iterations: usize, mut run: impl FnMut()) -> Vec<f64> {
    let warm_up_start = Instant::now();
    loop {
        run();
        if warm_up_start.elapsed().as_secs_f64() >= WARM_UP_SECONDS {
            break;
        }
    }
    let mut times = Vec::with_capacity(iterations);
    for _ in 0..iterations {
        let start = Instant::now();
        run();
        times.push(start.elapsed().as_secs_f64());
    }
    times
}

/// Minimum and median of the run times, in seconds.
fn min_and_median(times: &[f64]) -> (f64, f64) {
    let mut sorted = times.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).expect("times must not be NaN"));
    (sorted[0], sorted[sorted.len() / 2])
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Lex,
    Full,
}

impl Mode {
    fn name(self) -> &'static str {
        match self {
            Mode::Lex => "lex",
            Mode::Full => "full",
        }
    }
}

enum Format {
    Table,
    Raw,
    List,
}

fn main() -> ExitCode {
    let benchmarks_dir = common::benchmarks_dir();

    let mode = std::env::var("SMT_BENCH_MODE").unwrap_or_default();
    let modes: &[Mode] = match mode.as_str() {
        "" | "both" => &[Mode::Lex, Mode::Full],
        "lex" => &[Mode::Lex],
        "full" => &[Mode::Full],
        other => {
            eprintln!(
                "Unknown SMT_BENCH_MODE {:?}; use \"lex\", \"full\", or \"both\"",
                other
            );
            return ExitCode::FAILURE;
        }
    };

    let format = std::env::var("SMT_BENCH_FORMAT").unwrap_or_default();
    let format = match format.as_str() {
        "" | "table" => Format::Table,
        "raw" => Format::Raw,
        "list" => Format::List,
        other => {
            eprintln!(
                "Unknown SMT_BENCH_FORMAT {:?}; use \"table\", \"raw\", or \"list\"",
                other
            );
            return ExitCode::FAILURE;
        }
    };

    let iterations = match std::env::var("SMT_BENCH_ITERATIONS") {
        Ok(value) => match value.parse::<usize>() {
            Ok(iterations) if iterations > 0 => iterations,
            _ => {
                eprintln!(
                    "Invalid SMT_BENCH_ITERATIONS {:?}; use a positive number",
                    value
                );
                return ExitCode::FAILURE;
            }
        },
        Err(_) => DEFAULT_ITERATIONS,
    };

    let files = match common::selected_files() {
        Ok(files) => files,
        Err(message) => {
            eprintln!("{message}");
            return ExitCode::FAILURE;
        }
    };

    if let Format::List = format {
        for (label, _) in &files {
            println!("{label}");
        }
        return ExitCode::SUCCESS;
    }

    if !benchmarks_dir.exists() {
        eprintln!(
            "Benchmark corpus not found at {}; unpack the SMT-LIB corpus there \
             or set SMT_BENCHMARKS_DIR to its root",
            benchmarks_dir.display()
        );
        return ExitCode::FAILURE;
    }

    let label_width = files
        .iter()
        .map(|(label, _)| label.len())
        .max()
        .unwrap_or(0);

    for (label, relative) in &files {
        let path: PathBuf = benchmarks_dir.join(relative);
        let data = match std::fs::read(&path) {
            Ok(data) => data,
            Err(err) => {
                eprintln!("Cannot read benchmark file {}: {}", path.display(), err);
                return ExitCode::FAILURE;
            }
        };
        let megabytes = data.len() as f64 / 1_000_000.0;
        // the token count turns run times into nanoseconds per token
        let tokens = lex_from_memory(&data, &path).max(1) as f64;

        if let Format::Table = format {
            print!("{:<label_width$}  {:>7.2} MB", label, megabytes);
        }

        for &mode in modes {
            let times = time_runs(iterations, || match mode {
                Mode::Lex => {
                    lex_from_memory(&data, &path);
                }
                Mode::Full => common::parse_from_memory(&data, &path),
            });

            match format {
                Format::Table => {
                    let (min, median) = min_and_median(&times);
                    print!(
                        "  {} {:>6.1}/{:>6.1} MB/s {:>5.2} ns/tok",
                        mode.name(),
                        megabytes / min,
                        megabytes / median,
                        min * 1e9 / tokens
                    );
                }
                Format::Raw => {
                    print!("{}\t{}\t{}\t", label, mode.name(), data.len());
                    for (i, time) in times.iter().enumerate() {
                        if i > 0 {
                            print!(" ");
                        }
                        print!("{:e}", time);
                    }
                    println!();
                }
                Format::List => unreachable!("the list format does not measure"),
            }
        }

        if let Format::Table = format {
            println!();
        }
    }

    if let Format::Table = format {
        println!("(throughput as min/median over {iterations} runs; ns/tok from the min)");
    }

    ExitCode::SUCCESS
}

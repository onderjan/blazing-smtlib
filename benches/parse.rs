//! Parse-throughput benchmark over pinned SMT-LIB benchmark files.
//!
//! Expects the SMT-LIB corpus under `benchmarks/2025` in the repository root
//! (tracks unpacked as `non-incremental/<LOGIC>/...`); set the environment
//! variable `SMT_BENCHMARKS_DIR` to use a corpus root elsewhere. Each file is
//! loaded into memory first, so the numbers measure lexing and parsing only,
//! not disk I/O.
//!
//! Run with `cargo bench`. Each file is measured in two modes: lexing only
//! (tokens are discarded by a counting handler) and the full lex-and-parse
//! pipeline. Set the environment variable `SMT_BENCH_MODE` to `lex` or `full`
//! to run just one mode, e.g. to attribute a profile to a single mode.

use std::convert::Infallible;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

use smt_parser_rs::{
    CheckStandardSyntax,
    read::{
        SmtReadErrorKind,
        lexer::{Lexer, TokenHandler},
        read_smt,
    },
    token::Token,
};

/// Benchmarked files, relative to the corpus root.
///
/// Chosen to span different QF_BV families (and thus different mixes of
/// symbols, literals, and term shapes) at sizes big enough for stable timing
/// yet small enough to keep a full run in seconds. Throughput was measured to
/// be independent of file size, so mid-size files stand in for the giant ones.
const FILES: &[&str] = &[
    // small file: dominated by per-command and small-term overhead
    "non-incremental/QF_BV/bmc-bv-svcomp14/modulus_true.c.21.smt2",
    // BMC software unrolling
    "non-incremental/QF_BV/bmc-bv-svcomp14/soft_float_1_true.c.cil.c.17.smt2",
    // multiple constant multiplication encodings
    "non-incremental/QF_BV/mcm/186.smt2",
    // answer set programming translations
    "non-incremental/QF_BV/asp/Labyrinth/laby_18_18_13.lp.smt2",
    // symbolic execution queries
    "non-incremental/QF_BV/uclid/catchconv/catchconv-15803.smt2",
];

/// Timed runs per file and mode; an additional first (warm-up) run is discarded.
const ITERATIONS: usize = 5;

/// Token handler that only counts tokens, so timed lexing includes no parsing.
struct DiscardTokens {
    tokens: usize,
}

impl TokenHandler for DiscardTokens {
    type Error = Infallible;

    fn handle_token(&mut self, _token: Token) -> Result<(), Self::Error> {
        self.tokens += 1;
        Ok(())
    }
}

/// Lexes the in-memory file, discarding tokens, and returns the token count.
fn lex_from_memory(data: &[u8], path: &Path) -> usize {
    let mut handler = DiscardTokens { tokens: 0 };
    let mut lexer = Lexer::new(&mut handler);
    for &c in data {
        if let Err(err) = lexer.lex_next(c) {
            panic!("benchmark file {} must lex, got {:?}", path.display(), err);
        }
    }
    if let Err(err) = lexer.lex_eof() {
        panic!("benchmark file {} must lex, got {:?}", path.display(), err);
    }
    handler.tokens
}

fn parse_from_memory(data: &[u8], path: &Path) {
    if let Err(err) = read_smt(&mut CheckStandardSyntax, data) {
        let span = err.span();
        let description = match err.kind() {
            SmtReadErrorKind::Lexer(err) => format!("lexer error: {:?}", err),
            SmtReadErrorKind::Parser(err) => format!("parser error: {:?}", err),
            SmtReadErrorKind::Io(err) => format!("read error: {:?}", err),
            SmtReadErrorKind::Handler(err) => format!("nonstandard command: {:?}", err.0),
        };
        panic!(
            "benchmark file {} must parse, got {} at {:?}",
            path.display(),
            description,
            span
        );
    }
}

/// Times the closure over a discarded warm-up run and [`ITERATIONS`] timed
/// runs, returning the minimum and median times in seconds.
fn time_runs(mut run: impl FnMut()) -> (f64, f64) {
    run();
    let mut times = Vec::with_capacity(ITERATIONS);
    for _ in 0..ITERATIONS {
        let start = Instant::now();
        run();
        times.push(start.elapsed().as_secs_f64());
    }
    times.sort_by(|a, b| a.partial_cmp(b).expect("times must not be NaN"));
    (times[0], times[times.len() / 2])
}

fn main() -> ExitCode {
    let benchmarks_dir = match std::env::var_os("SMT_BENCHMARKS_DIR") {
        Some(dir) => PathBuf::from(dir),
        None => Path::new(env!("CARGO_MANIFEST_DIR")).join("benchmarks/2025"),
    };
    if !benchmarks_dir.exists() {
        eprintln!(
            "Benchmark corpus not found at {}; unpack the SMT-LIB corpus there \
             or set SMT_BENCHMARKS_DIR to its root",
            benchmarks_dir.display()
        );
        return ExitCode::FAILURE;
    }

    let mode = std::env::var("SMT_BENCH_MODE").unwrap_or_default();
    let (run_lex, run_full) = match mode.as_str() {
        "" | "both" => (true, true),
        "lex" => (true, false),
        "full" => (false, true),
        other => {
            eprintln!("Unknown SMT_BENCH_MODE {:?}; use \"lex\" or \"full\"", other);
            return ExitCode::FAILURE;
        }
    };

    let name_width = FILES
        .iter()
        .map(|relative| relative.len())
        .max()
        .expect("file list must not be empty");

    for relative in FILES {
        let path: PathBuf = benchmarks_dir.join(relative);
        let data = match std::fs::read(&path) {
            Ok(data) => data,
            Err(err) => {
                eprintln!("Cannot read benchmark file {}: {}", path.display(), err);
                return ExitCode::FAILURE;
            }
        };
        let megabytes = data.len() as f64 / 1_000_000.0;

        print!("{:<name_width$}  {:>7.2} MB", relative, megabytes);

        if run_lex {
            let (min, median) = time_runs(|| {
                lex_from_memory(&data, &path);
            });
            print!("  lex {:>6.1}/{:>6.1} MB/s", megabytes / min, megabytes / median);
        }

        if run_full {
            let (min, median) = time_runs(|| parse_from_memory(&data, &path));
            print!("  full {:>6.1}/{:>6.1} MB/s", megabytes / min, megabytes / median);
        }

        println!();
    }

    println!("(throughput as min/median over {ITERATIONS} runs)");

    ExitCode::SUCCESS
}

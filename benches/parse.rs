//! Parse-throughput benchmark over pinned SMT-LIB benchmark files.
//!
//! Expects the benchmark corpus to be reachable through the `benchmarks`
//! directory in the repository root (e.g. `benchmarks/QF_BV` as a symlink to
//! an SMT-LIB QF_BV checkout). Each file is loaded into memory first, so the
//! numbers measure lexing and parsing only, not disk I/O.
//!
//! Run with `cargo bench`.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

use smt_parser_rs::{
    CheckStandardSyntax,
    read::{SmtReadErrorKind, read_smt},
};

/// Benchmarked files, relative to the `benchmarks` directory.
///
/// Chosen to span different QF_BV families (and thus different mixes of
/// symbols, literals, and term shapes) at sizes big enough for stable timing
/// yet small enough to keep a full run in seconds. Throughput was measured to
/// be independent of file size, so mid-size files stand in for the giant ones.
const FILES: &[&str] = &[
    // small file: dominated by per-command and small-term overhead
    "QF_BV/bmc-bv-svcomp14/modulus_true.c.21.smt2",
    // BMC software unrolling
    "QF_BV/bmc-bv-svcomp14/soft_float_1_true.c.cil.c.17.smt2",
    // multiple constant multiplication encodings
    "QF_BV/mcm/186.smt2",
    // answer set programming translations
    "QF_BV/asp/Labyrinth/laby_18_18_13.lp.smt2",
    // symbolic execution queries
    "QF_BV/uclid/catchconv/catchconv-15803.smt2",
];

/// Timed parses per file; the first (warm-up) parse is discarded.
const ITERATIONS: usize = 5;

fn parse_from_memory(data: &[u8], path: &Path) {
    if let Err(err) = read_smt(&mut CheckStandardSyntax, data) {
        let span = err.span();
        let description = match err.into_kind() {
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

fn main() -> ExitCode {
    let benchmarks_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("benchmarks");
    if !benchmarks_dir.exists() {
        eprintln!(
            "Benchmark corpus not found at {}; make it available there, \
             e.g. as a symlink: benchmarks/QF_BV -> <SMT-LIB QF_BV directory>",
            benchmarks_dir.display()
        );
        return ExitCode::FAILURE;
    }

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

        // warm-up parse, not timed
        parse_from_memory(&data, &path);

        let mut times = Vec::with_capacity(ITERATIONS);
        for _ in 0..ITERATIONS {
            let start = Instant::now();
            parse_from_memory(&data, &path);
            times.push(start.elapsed().as_secs_f64());
        }
        times.sort_by(|a, b| a.partial_cmp(b).expect("times must not be NaN"));
        let min = times[0];
        let median = times[times.len() / 2];

        println!(
            "{:<name_width$}  {:>7.2} MB  min {:>6.1} MB/s  median {:>6.1} MB/s",
            relative,
            megabytes,
            megabytes / min,
            megabytes / median,
        );
    }

    ExitCode::SUCCESS
}

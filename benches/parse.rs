//! Parse-throughput benchmark over pinned SMT-LIB benchmark files.
//!
//! Expects the SMT-LIB corpus under `benchmarks/2025` in the current
//! directory, which is the repository root under `cargo bench` (tracks
//! unpacked as `non-incremental/<LOGIC>/...` and `incremental/<LOGIC>/...`);
//! set the environment variable `SMT_BENCHMARKS_DIR` to use a corpus root
//! elsewhere. Each file is loaded into memory first, so the numbers measure
//! lexing and parsing only, not disk I/O.
//!
//! Run with `cargo bench --bench parse`. Each file is measured in two modes:
//! lexing only (tokens are discarded by a counting handler) and the full
//! lex-and-parse pipeline.
//!
//! Environment variables:
//!
//! - `SMT_BENCH_MODE`: `lex`, `full`, or `both` (default) selects the
//!   measured modes, e.g. to attribute a profile to a single mode.
//! - `SMT_BENCH_FILES`: comma-separated labels (see [`FILES`]) restricting
//!   the measured files, in the order given.
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

/// A benchmarked file: a short label used in output and for selection,
/// and its path relative to the corpus root.
struct BenchFile {
    label: &'static str,
    path: &'static str,
}

const fn file(label: &'static str, path: &'static str) -> BenchFile {
    BenchFile { label, path }
}

/// Benchmarked files.
///
/// The QF_BV files span different families (and thus different mixes of
/// symbols, literals, and term shapes) at sizes big enough for stable timing
/// yet small enough to keep a full run in seconds. Throughput was measured to
/// be independent of file size, so mid-size files stand in for the giant
/// ones. The remaining files each cover a syntactic path the QF_BV files do
/// not exercise: quantifiers and datatypes, string literals, many tiny
/// commands, incremental scripts, and let-heavy terms.
const FILES: &[BenchFile] = &[
    // small file: dominated by per-command and small-term overhead
    file(
        "qf_bv/modulus_true.21",
        "non-incremental/QF_BV/bmc-bv-svcomp14/modulus_true.c.21.smt2",
    ),
    // BMC software unrolling
    file(
        "qf_bv/soft_float_1.17",
        "non-incremental/QF_BV/bmc-bv-svcomp14/soft_float_1_true.c.cil.c.17.smt2",
    ),
    // multiple constant multiplication encodings: deep bit-vector arithmetic,
    // very short tokens, the highest per-application cost in the set
    file("qf_bv/mcm-186", "non-incremental/QF_BV/mcm/186.smt2"),
    // answer set programming translations
    file(
        "qf_bv/laby_18_18_13",
        "non-incremental/QF_BV/asp/Labyrinth/laby_18_18_13.lp.smt2",
    ),
    // symbolic execution queries
    file(
        "qf_bv/catchconv-15803",
        "non-incremental/QF_BV/uclid/catchconv/catchconv-15803.smt2",
    ),
    // Verus verification conditions: thousands of quantified assertions
    // with patterns, let terms, and datatype declarations
    file(
        "ufdtlia/verus-zookeeper-7",
        "non-incremental/UFDTLIA/20241211-verus/anvil/\
         zookeeper-smt-zookeeper_controller__proof__helper_invariants__proof.7.smt2",
    ),
    // concolic execution over strings: tens of thousands of string literals
    // in a few dozen huge commands
    file(
        "qf_slia/ip_int_from_string-460",
        "non-incremental/QF_SLIA/2019-full_str_int/py-conbyte_z3str/\
         lib_int-ipaddress__ip_int_from_string/460.smt2",
    ),
    // Petri net decomposition: about 150 thousand one-line assertions,
    // so per-command overhead dominates
    file(
        "qf_ufdt/vlsat3_k44",
        "non-incremental/QF_UFDT/20210312-Bouvier/vlsat3_k44.smt2",
    ),
    // k-induction software verification: incremental script of over
    // 200 thousand small define-fun commands with push and pop
    file(
        "inc-qf_abv/cpachecker-rtl8192e",
        "incremental/QF_ABV/20190307-CPAchecker_kInduction-SoSy_Lab/\
         32_7a_cilled_linux-3.8-rc1-32_7a-drivers--staging--rtl8192e--rtl8192e--\
         r8192e_pci.ko-ldv_main7_sequence_infinite_withcheck_stateful.cil.out_smt-query.0.smt2",
    ),
    // Kind model checker: incremental script whose assertions are dominated
    // by let bindings
    file(
        "inc-qf_uflia/kind-microwave11",
        "incremental/QF_UFLIA/kind/microwave11.ec.smt2",
    ),
];

/// Default timed runs per file and mode; an additional first (warm-up) run
/// is discarded.
const DEFAULT_ITERATIONS: usize = 5;

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
    if let Err(err) = lexer.lex_all(data) {
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
    let benchmarks_dir = match std::env::var_os("SMT_BENCHMARKS_DIR") {
        Some(dir) => PathBuf::from(dir),
        // relative to the current directory, which cargo sets to the package
        // root; an embedded absolute path would make the code layout, and so
        // the measured throughput, depend on where the package is checked out
        None => PathBuf::from("benchmarks/2025"),
    };

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

    let files: Vec<&BenchFile> = match std::env::var("SMT_BENCH_FILES") {
        Ok(labels) => {
            let mut files = Vec::new();
            for label in labels.split(',').map(str::trim).filter(|s| !s.is_empty()) {
                match FILES.iter().find(|file| file.label == label) {
                    Some(file) => files.push(file),
                    None => {
                        eprintln!(
                            "Unknown benchmark file label {:?} in SMT_BENCH_FILES",
                            label
                        );
                        return ExitCode::FAILURE;
                    }
                }
            }
            files
        }
        Err(_) => FILES.iter().collect(),
    };

    if let Format::List = format {
        for file in &files {
            println!("{}", file.label);
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

    let label_width = files.iter().map(|file| file.label.len()).max().unwrap_or(0);

    for file in &files {
        let path: PathBuf = benchmarks_dir.join(file.path);
        let data = match std::fs::read(&path) {
            Ok(data) => data,
            Err(err) => {
                eprintln!("Cannot read benchmark file {}: {}", path.display(), err);
                return ExitCode::FAILURE;
            }
        };
        let megabytes = data.len() as f64 / 1_000_000.0;

        if let Format::Table = format {
            print!("{:<label_width$}  {:>7.2} MB", file.label, megabytes);
        }

        for &mode in modes {
            let times = time_runs(iterations, || match mode {
                Mode::Lex => {
                    lex_from_memory(&data, &path);
                }
                Mode::Full => parse_from_memory(&data, &path),
            });

            match format {
                Format::Table => {
                    let (min, median) = min_and_median(&times);
                    print!(
                        "  {} {:>6.1}/{:>6.1} MB/s",
                        mode.name(),
                        megabytes / min,
                        megabytes / median
                    );
                }
                Format::Raw => {
                    print!("{}\t{}\t{}\t", file.label, mode.name(), data.len());
                    for (i, time) in times.iter().enumerate() {
                        if i > 0 {
                            print!(" ");
                        }
                        print!("{:e}", time);
                    }
                    println!();
                }
                Format::List => unreachable!("list format returns before measuring"),
            }
        }

        if let Format::Table = format {
            println!();
        }
    }

    if let Format::Table = format {
        println!("(throughput as min/median over {iterations} runs)");
    }

    ExitCode::SUCCESS
}

//! Interleaved throughput comparison of two revisions of the parser.
//!
//! Run-to-run drift of the `parse` bench (thermal state, background load,
//! frequency scaling) is a few percent, which hides small changes when a
//! baseline and a head are benchmarked one after the other. This driver
//! instead builds the `parse` bench for both revisions and runs the two
//! binaries alternately, file by file and round by round, so that drift
//! affects both sides equally and the ratio between them is meaningful.
//!
//! Usage (arguments after `--` go to this driver):
//!
//! ```text
//! cargo bench --bench compare -- <baseline> [<head>] [options]
//! ```
//!
//! Each side is either a git revision or the path of an already built `parse`
//! bench binary (anything that is an existing file is taken as a binary),
//! which allows measuring experimental builds made outside the repository.
//! Revisions are anything `git rev-parse` accepts. A revision is checked out
//! into a detached worktree under `target/compare/<commit>` and built there;
//! worktrees are reused between invocations and can be removed with
//! `git worktree remove` (after a `cargo clean` has deleted them,
//! `git worktree prune` drops the stale registrations). Without a head the
//! head is the current working tree, uncommitted changes included, so the
//! usual workflow is `cargo bench --bench compare -- HEAD` after editing. The
//! untracked `Cargo.lock` and the current `benches/parse.rs` (with the
//! `benches/common` module it shares with the census bench) are copied into
//! each worktree, so both sides run the same measurement code against their
//! own library; this requires the baseline to still offer the small API the
//! bench uses.
//!
//! Options:
//!
//! - `--rounds N`: alternations per file and mode (default 5). Each round
//!   runs both sides once, in alternating order.
//! - `--iterations N`: timed runs per side and round (default 2), preceded
//!   by a warm-up run. Every process measures one file in one mode.
//! - `--files a,b,...`: labels from `benches/parse.rs` (default: all).
//! - `--mode lex|full|both`: measured modes (default `both`).
//!
//! Output is one row per file and mode with the best throughput of each side
//! over all its runs, the median of the per-round ratios of best times (as
//! head over baseline throughput), and the range of those per-round ratios,
//! which shows whether a difference is larger than the drift within the run.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

const DEFAULT_ROUNDS: usize = 5;
const DEFAULT_ITERATIONS: usize = 2;

struct Options {
    baseline: String,
    head: Option<String>,
    rounds: usize,
    iterations: usize,
    files: Option<String>,
    mode: String,
}

fn usage() -> String {
    "usage: cargo bench --bench compare -- <baseline> [<head>] \
     [--rounds N] [--iterations N] [--files a,b,...] [--mode lex|full|both]"
        .to_string()
}

fn parse_options(args: impl Iterator<Item = String>) -> Result<Options, String> {
    let mut revisions = Vec::new();
    let mut rounds = DEFAULT_ROUNDS;
    let mut iterations = DEFAULT_ITERATIONS;
    let mut files = None;
    let mut mode = "both".to_string();

    let mut args = args;
    while let Some(arg) = args.next() {
        let mut value = |name: &str| {
            args.next()
                .ok_or_else(|| format!("{name} needs a value\n{}", usage()))
        };
        match arg.as_str() {
            "--rounds" => {
                rounds = parse_positive(&value("--rounds")?, "--rounds")?;
            }
            "--iterations" => {
                iterations = parse_positive(&value("--iterations")?, "--iterations")?;
            }
            "--files" => files = Some(value("--files")?),
            "--mode" => {
                mode = value("--mode")?;
                if !matches!(mode.as_str(), "lex" | "full" | "both") {
                    return Err(format!("--mode must be lex, full, or both\n{}", usage()));
                }
            }
            // cargo bench appends --bench to the arguments of a harness-less bench
            "--bench" => {}
            "--help" | "-h" => return Err(usage()),
            other if other.starts_with("--") => {
                return Err(format!("unknown option {other}\n{}", usage()));
            }
            _ => revisions.push(arg),
        }
    }

    let mut revisions = revisions.into_iter();
    let baseline = revisions
        .next()
        .ok_or_else(|| format!("baseline revision missing\n{}", usage()))?;
    let head = revisions.next();
    if revisions.next().is_some() {
        return Err(format!("too many revisions\n{}", usage()));
    }

    Ok(Options {
        baseline,
        head,
        rounds,
        iterations,
        files,
        mode,
    })
}

fn parse_positive(value: &str, name: &str) -> Result<usize, String> {
    match value.parse::<usize>() {
        Ok(number) if number > 0 => Ok(number),
        _ => Err(format!("{name} must be a positive number, got {value:?}")),
    }
}

/// Runs a command, returning its standard output on success and a
/// description including its standard error on failure.
fn run(command: &mut Command) -> Result<String, String> {
    let output = command
        .output()
        .map_err(|err| format!("cannot run {:?}: {err}", command.get_program()))?;
    if !output.status.success() {
        return Err(format!(
            "{:?} failed with {}:\n{}",
            command.get_program(),
            output.status,
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    String::from_utf8(output.stdout)
        .map_err(|err| format!("{:?} output is not UTF-8: {err}", command.get_program()))
}

fn git(root: &Path, args: &[&str]) -> Result<String, String> {
    run(Command::new("git").arg("-C").arg(root).args(args))
}

/// One side of the comparison: a name for output and the built bench binary.
struct Side {
    name: String,
    binary: PathBuf,
}

/// Resolves a side given on the command line: the path of an existing file is
/// taken as a built `parse` bench binary, anything else as a git revision.
fn resolve_side(root: &Path, side: &str) -> Result<Side, String> {
    let path = Path::new(side);
    if path.is_file() {
        return Ok(Side {
            name: format!("binary {side}"),
            binary: path.to_path_buf(),
        });
    }
    build_revision(root, side)
}

/// Resolves the revision to a commit, checks it out into a worktree under
/// `target/compare`, and builds the `parse` bench there.
fn build_revision(root: &Path, revision: &str) -> Result<Side, String> {
    let commit = git(
        root,
        &[
            "rev-parse",
            "--verify",
            "--end-of-options",
            &format!("{revision}^{{commit}}"),
        ],
    )?;
    let commit = commit.trim().to_string();
    let short = git(root, &["rev-parse", "--short", &commit])?
        .trim()
        .to_string();

    let worktree = root.join("target").join("compare").join(&commit);
    if !worktree.exists() {
        eprintln!(
            "compare: checking out {revision} ({short}) into {}",
            worktree.display()
        );
        git(
            root,
            &[
                "worktree",
                "add",
                "--detach",
                &worktree.to_string_lossy(),
                &commit,
            ],
        )?;
    }

    // the lockfile is untracked, and the bench source must be the one whose
    // protocol this driver speaks, together with the module it shares with
    // the census bench (which a baseline may predate, hence the directory)
    for relative in ["Cargo.lock", "benches/parse.rs", "benches/common/mod.rs"] {
        let source = root.join(relative);
        if source.exists() {
            let destination = worktree.join(relative);
            if let Some(parent) = destination.parent() {
                std::fs::create_dir_all(parent)
                    .map_err(|err| format!("cannot create {}: {err}", parent.display()))?;
            }
            std::fs::copy(&source, &destination).map_err(|err| {
                format!(
                    "cannot copy {} to {}: {err}",
                    source.display(),
                    destination.display()
                )
            })?;
        }
    }

    eprintln!("compare: building {revision} ({short})");
    let binary = build_parse_bench(&worktree)?;
    Ok(Side {
        name: format!("{revision} ({short})"),
        binary,
    })
}

/// Builds the `parse` bench of the current working tree.
fn build_working_tree(root: &Path) -> Result<Side, String> {
    eprintln!("compare: building the working tree");
    let binary = build_parse_bench(root)?;
    let status = git(root, &["status", "--porcelain", "--untracked-files=no"])?;
    let name = if status.trim().is_empty() {
        "working tree (clean)".to_string()
    } else {
        "working tree (modified)".to_string()
    };
    Ok(Side { name, binary })
}

/// Builds the `parse` bench in the given package directory and returns the
/// path of the produced executable, taken from cargo's JSON messages.
fn build_parse_bench(package: &Path) -> Result<PathBuf, String> {
    let cargo = std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into());
    let output = run(Command::new(cargo).current_dir(package).args([
        "bench",
        "--bench",
        "parse",
        "--no-run",
        "--offline",
        "--message-format=json",
    ]))?;

    // without a JSON dependency, pick the executable out of the artifact
    // message for the parse bench target by plain string search
    for line in output.lines() {
        if !line.contains("\"compiler-artifact\"") || !line.contains("\"name\":\"parse\"") {
            continue;
        }
        let Some(rest) = line.split("\"executable\":\"").nth(1) else {
            continue;
        };
        let Some(path) = rest.split('"').next() else {
            continue;
        };
        return Ok(PathBuf::from(path));
    }
    Err(format!(
        "cargo did not report a parse bench executable in {}",
        package.display()
    ))
}

/// Runs one side of the comparison on one file and mode, returning the
/// file size in bytes and the timed runs in seconds.
fn measure(
    side: &Side,
    corpus: &Path,
    label: &str,
    mode: &str,
    iterations: usize,
) -> Result<(u64, Vec<f64>), String> {
    // the worktree binaries would otherwise look for the corpus in the worktree
    let output = run(Command::new(&side.binary)
        .env("SMT_BENCHMARKS_DIR", corpus)
        .env("SMT_BENCH_FORMAT", "raw")
        .env("SMT_BENCH_FILES", label)
        .env("SMT_BENCH_MODE", mode)
        .env("SMT_BENCH_ITERATIONS", iterations.to_string()))?;

    let line = output
        .lines()
        .next()
        .ok_or_else(|| format!("{} printed no measurement", side.name))?;
    let fields: Vec<&str> = line.split('\t').collect();
    let [got_label, got_mode, bytes, times] = fields[..] else {
        return Err(format!("{} printed a malformed line: {line:?}", side.name));
    };
    if got_label != label || got_mode != mode {
        return Err(format!(
            "{} measured {got_label} in mode {got_mode} instead of {label} in mode {mode}",
            side.name
        ));
    }
    let bytes: u64 = bytes
        .parse()
        .map_err(|err| format!("{} printed a bad size: {err}", side.name))?;
    let times = times
        .split(' ')
        .map(|time| {
            time.parse::<f64>()
                .map_err(|err| format!("{} printed a bad time: {err}", side.name))
        })
        .collect::<Result<Vec<f64>, String>>()?;
    Ok((bytes, times))
}

fn median(times: &[f64]) -> f64 {
    let mut sorted = times.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).expect("times must not be NaN"));
    sorted[sorted.len() / 2]
}

/// The fastest run: interference only ever makes a run slower, so the
/// minimum is the most repeatable estimate of the cost of the work itself.
fn best(times: &[f64]) -> f64 {
    times.iter().copied().fold(f64::INFINITY, f64::min)
}

/// Lists the labels selected for measurement, asking the head binary.
fn list_files(head: &Side, files: Option<&str>) -> Result<Vec<String>, String> {
    let mut command = Command::new(&head.binary);
    command.env("SMT_BENCH_FORMAT", "list");
    if let Some(files) = files {
        command.env("SMT_BENCH_FILES", files);
    }
    Ok(run(&mut command)?.lines().map(str::to_string).collect())
}

fn percent(ratio: f64) -> String {
    format!("{:+.1}%", (ratio - 1.0) * 100.0)
}

fn main() -> ExitCode {
    match main_inner() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("compare: {err}");
            ExitCode::FAILURE
        }
    }
}

fn main_inner() -> Result<(), String> {
    let options = parse_options(std::env::args().skip(1))?;
    let root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let corpus = match std::env::var_os("SMT_BENCHMARKS_DIR") {
        Some(dir) => PathBuf::from(dir),
        None => root.join("../benchmarks/2025"),
    };

    let baseline = resolve_side(root, &options.baseline)?;
    let head = match &options.head {
        Some(side) => resolve_side(root, side)?,
        None => build_working_tree(root)?,
    };

    let files = list_files(&head, options.files.as_deref())?;
    let modes: &[&str] = match options.mode.as_str() {
        "both" => &["lex", "full"],
        "lex" => &["lex"],
        "full" => &["full"],
        other => unreachable!("mode {other} was validated when parsing options"),
    };

    println!("baseline: {}", baseline.name);
    println!("head:     {}", head.name);
    println!(
        "({} rounds of {} timed runs per side, best throughput in MB/s, \
         median and range of per-round head/baseline ratios of best times)",
        options.rounds, options.iterations
    );
    println!();

    let label_width = files.iter().map(String::len).max().unwrap_or(0).max(4);
    println!(
        "{:<label_width$}  mode  {:>8}  {:>8}  {:>8}  rounds",
        "file", "baseline", "head", "head/base"
    );

    for label in &files {
        for mode in modes {
            let mut row = format!("{label:<label_width$}  {mode:<4}");
            match compare_one(&baseline, &head, &corpus, label, mode, &options) {
                Ok(result) => {
                    write!(
                        row,
                        "  {:>8.1}  {:>8.1}  {:>9}  [{} .. {}]",
                        result.baseline_mbs,
                        result.head_mbs,
                        percent(result.ratio),
                        percent(result.round_min),
                        percent(result.round_max),
                    )
                    .expect("writing to a string cannot fail");
                }
                Err(err) => {
                    write!(row, "  failed: {err}").expect("writing to a string cannot fail");
                }
            }
            println!("{row}");
        }
    }
    Ok(())
}

struct Comparison {
    baseline_mbs: f64,
    head_mbs: f64,
    /// Median of the per-round ratios of head to baseline throughput, each
    /// computed from the best time of the side within the round.
    ///
    /// Each round runs the two sides back to back, so a per-round ratio is
    /// the pairing least affected by drift, and the median of those ratios
    /// is the headline figure.
    ratio: f64,
    /// Smallest and largest per-round ratio.
    round_min: f64,
    round_max: f64,
}

fn compare_one(
    baseline: &Side,
    head: &Side,
    corpus: &Path,
    label: &str,
    mode: &str,
    options: &Options,
) -> Result<Comparison, String> {
    let mut baseline_times = Vec::new();
    let mut head_times = Vec::new();
    let mut round_ratios = Vec::new();
    let mut bytes = 0;

    for round in 0..options.rounds {
        // alternate which side goes first so that neither side always runs
        // right after the other has warmed the machine up
        let sides = if round % 2 == 0 {
            [(baseline, &mut baseline_times), (head, &mut head_times)]
        } else {
            [(head, &mut head_times), (baseline, &mut baseline_times)]
        };
        let mut round_bests = [0.0; 2];
        for (index, (side, times)) in sides.into_iter().enumerate() {
            let (size, run_times) = measure(side, corpus, label, mode, options.iterations)?;
            bytes = size;
            round_bests[index] = best(&run_times);
            times.extend(run_times);
        }
        let (baseline_best, head_best) = if round % 2 == 0 {
            (round_bests[0], round_bests[1])
        } else {
            (round_bests[1], round_bests[0])
        };
        round_ratios.push(baseline_best / head_best);
    }

    let megabytes = bytes as f64 / 1_000_000.0;
    let baseline_best = best(&baseline_times);
    let head_best = best(&head_times);
    let (round_min, round_max) = round_ratios
        .iter()
        .fold((f64::INFINITY, f64::NEG_INFINITY), |(min, max), &ratio| {
            (min.min(ratio), max.max(ratio))
        });
    Ok(Comparison {
        baseline_mbs: megabytes / baseline_best,
        head_mbs: megabytes / head_best,
        ratio: median(&round_ratios),
        round_min,
        round_max,
    })
}

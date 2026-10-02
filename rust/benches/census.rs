//! Census of the benchmark files: what each consists of, and what a full
//! parse of it allocates.
//!
//! Run with `cargo bench --bench census`. For each selected file it prints
//! the size, token count, bytes per token, and nesting depth; token counts
//! by type, reserved words, and top-level command names; and the allocations
//! of one full parse with [`blazing_smtlib::CheckStandardSyntax`]: the count,
//! the count per token, and the peak live heap. Command-line arguments name
//! additional files to describe, relative to the corpus root, which helps
//! when choosing files to add to [`common::FILES`].
//!
//! The corpus location and `SMT_BENCH_FILES` work as in the `parse` bench.
//! Allocations are counted by a global allocator, which is why this is a
//! separate binary: registering a counting allocator in the `parse` bench
//! would tax its full mode by about a tenth.

mod common;

use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::BTreeMap;
use std::convert::Infallible;
use std::ops::ControlFlow;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::atomic::{AtomicU64, Ordering};

use blazing_smtlib::{
    read::lexer::Lexer,
    token::{SmtVersion, Token, TokenCursor, TokenHandler, TokenKind},
};

/// Global allocator that counts allocations and tracks the live heap.
struct CountingAllocator;

static ALLOCATIONS: AtomicU64 = AtomicU64::new(0);
static LIVE_BYTES: AtomicU64 = AtomicU64::new(0);
static PEAK_BYTES: AtomicU64 = AtomicU64::new(0);

impl CountingAllocator {
    fn record(allocated: u64, freed: u64) {
        ALLOCATIONS.fetch_add(u64::from(allocated > 0), Ordering::Relaxed);
        let live = LIVE_BYTES.fetch_add(allocated, Ordering::Relaxed) + allocated;
        PEAK_BYTES.fetch_max(live, Ordering::Relaxed);
        LIVE_BYTES.fetch_sub(freed, Ordering::Relaxed);
    }
}

// SAFETY: every method forwards to the system allocator with the same
// arguments and only updates counters on the side
unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        Self::record(layout.size() as u64, 0);
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        Self::record(0, layout.size() as u64);
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        Self::record(new_size as u64, layout.size() as u64);
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

#[global_allocator]
static GLOBAL: CountingAllocator = CountingAllocator;

/// What a full parse of the in-memory file allocated.
struct Allocations {
    count: u64,
    peak_bytes: u64,
}

/// Parses the in-memory file, counting its allocations alone.
fn count_allocations(data: &[u8], path: &Path) -> Allocations {
    ALLOCATIONS.store(0, Ordering::Relaxed);
    LIVE_BYTES.store(0, Ordering::Relaxed);
    PEAK_BYTES.store(0, Ordering::Relaxed);
    common::parse_from_memory(data, path);
    Allocations {
        count: ALLOCATIONS.load(Ordering::Relaxed),
        peak_bytes: PEAK_BYTES.load(Ordering::Relaxed),
    }
}

/// Token handler that tallies what a file consists of.
#[derive(Default)]
struct Census {
    tokens: u64,
    /// Token counts by type name.
    types: BTreeMap<&'static str, u64>,
    /// Reserved word counts by spelling.
    reserved: BTreeMap<&'static str, u64>,
    /// Top-level command counts by name.
    commands: BTreeMap<String, u64>,
    depth: u64,
    max_depth: u64,
    /// The previous token opened a top-level command, so a symbol names it.
    expecting_command_name: bool,
}

impl TokenHandler for Census {
    type Result = ();
    type Error = Infallible;

    fn handle_tokens(
        &mut self,
        cursor: &mut TokenCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        while let Some(token) = cursor.next() {
            self.tally(token);
        }
        Ok(ControlFlow::Continue(()))
    }
}

impl Census {
    /// Tallies one token.
    fn tally(&mut self, token: Token) {
        self.tokens += 1;
        let expecting_command_name = self.expecting_command_name;
        self.expecting_command_name = false;
        let type_name = match TokenKind::from_token(token, SmtVersion::V2_7) {
            TokenKind::ParenOpen => {
                self.expecting_command_name = self.depth == 0;
                self.depth += 1;
                self.max_depth = self.max_depth.max(self.depth);
                "("
            }
            TokenKind::ParenClose => {
                self.depth = self.depth.saturating_sub(1);
                ")"
            }
            TokenKind::Numeral(_) => "numeral",
            TokenKind::Decimal(_) => "decimal",
            TokenKind::Hexadecimal(_) => "hexadecimal",
            TokenKind::Binary(_) => "binary",
            TokenKind::Symbol(name) => {
                if expecting_command_name {
                    let name = String::from_utf8_lossy(name.as_slice()).into_owned();
                    *self.commands.entry(name).or_default() += 1;
                }
                "symbol"
            }
            TokenKind::Reserved(reserved) => {
                // the standard command names are reserved words, so a command
                // is named by one; it is tallied as a command, not as a word
                if expecting_command_name && reserved.is_command_name() {
                    *self
                        .commands
                        .entry(reserved.as_str().to_owned())
                        .or_default() += 1;
                } else {
                    *self.reserved.entry(reserved.as_str()).or_default() += 1;
                }
                "reserved"
            }
            TokenKind::String(_) => "string",
            TokenKind::Keyword(_) => "keyword",
            TokenKind::EndOfFile => return,
        };
        *self.types.entry(type_name).or_default() += 1;
    }
}

/// Prints the census of the in-memory file.
fn print_census(label: &str, data: &[u8], path: &Path) {
    let mut census = Census::default();
    let mut lexer = Lexer::new(&mut census, SmtVersion::V2_7);
    if let Err(err) = lexer.lex_all(data) {
        panic!("benchmark file {} must lex, got {:?}", path.display(), err);
    }
    let tokens = census.tokens.max(1);
    println!(
        "{label}  {:.2} MB  {} tokens  {:.1} B/token  max depth {}",
        data.len() as f64 / 1_000_000.0,
        census.tokens,
        data.len() as f64 / tokens as f64,
        census.max_depth
    );
    let sections: [(&str, Vec<(String, u64)>); 3] = [
        (
            "tokens",
            census
                .types
                .iter()
                .map(|(name, count)| (name.to_string(), *count))
                .collect(),
        ),
        (
            "reserved",
            census
                .reserved
                .iter()
                .map(|(name, count)| (name.to_string(), *count))
                .collect(),
        ),
        (
            "commands",
            census
                .commands
                .iter()
                .map(|(name, count)| (name.clone(), *count))
                .collect(),
        ),
    ];
    for (title, counts) in sections {
        print!("  {title}:");
        for (name, count) in counts {
            print!("  {name} {count}");
        }
        println!();
    }
    let allocations = count_allocations(data, path);
    println!(
        "  allocations:  {} total  {:.2} per token  peak live heap {} bytes",
        allocations.count,
        allocations.count as f64 / tokens as f64,
        allocations.peak_bytes
    );
}

fn main() -> ExitCode {
    let benchmarks_dir = common::benchmarks_dir();

    let mut files = match common::selected_files() {
        Ok(files) => files,
        Err(message) => {
            eprintln!("{message}");
            return ExitCode::FAILURE;
        }
    };
    // cargo bench appends --bench to the arguments of a harness-less bench
    for argument in std::env::args().skip(1).filter(|arg| arg != "--bench") {
        files.push((argument.clone(), PathBuf::from(argument)));
    }

    if !benchmarks_dir.exists() {
        eprintln!(
            "Benchmark corpus not found at {}; unpack the SMT-LIB corpus there \
             or set SMT_BENCHMARKS_DIR to its root",
            benchmarks_dir.display()
        );
        return ExitCode::FAILURE;
    }

    for (label, relative) in &files {
        let path: PathBuf = benchmarks_dir.join(relative);
        let data = match std::fs::read(&path) {
            Ok(data) => data,
            Err(err) => {
                eprintln!("Cannot read benchmark file {}: {}", path.display(), err);
                return ExitCode::FAILURE;
            }
        };
        print_census(label, &data, &path);
    }

    ExitCode::SUCCESS
}

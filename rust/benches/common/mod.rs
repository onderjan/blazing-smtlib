//! Shared by the `parse` and `census` benches: the pinned benchmark files,
//! where the corpus is, and which files a run selects.
//!
//! The `compare` bench driver copies this module into each revision's
//! worktree together with `parse.rs`, so both sides of a comparison measure
//! the same files with the same code.

use std::path::{Path, PathBuf};

use blazing_smtlib::{
    CheckStandardSyntax,
    read::{SmtReadErrorKind, read_smt},
};

/// Parses the in-memory file with [`CheckStandardSyntax`], panicking on any
/// error: benchmark files must parse.
pub fn parse_from_memory(data: &[u8], path: &Path) {
    if let Err(err) = read_smt(&mut CheckStandardSyntax, data) {
        let span = err.span();
        let description = match err.kind() {
            SmtReadErrorKind::Lexical(err) => format!("lexer error: {:?}", err),
            SmtReadErrorKind::Syntax(err) => format!("parser error: {:?}", err),
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

/// A benchmarked file: a short label used in output and for selection,
/// and its path relative to the corpus root.
pub struct BenchFile {
    pub label: &'static str,
    pub path: &'static str,
}

const fn file(label: &'static str, path: &'static str) -> BenchFile {
    BenchFile { label, path }
}

/// Benchmarked files.
///
/// Each file was chosen for a syntactic path it exercises more than the
/// others do (see the comments; `cargo bench --bench census` prints the
/// actual counts), at a size big enough for stable timing yet small enough
/// to keep a full run around ten seconds. Throughput was measured to be
/// independent of file size, so mid-size files stand in for the giant ones.
/// Constructs that the corpus hardly contains at all in files of usable size
/// (`as`, `match`, `par`, `lambda`, `check-sat-assuming`, `get-value`,
/// `define-sort`, `define-funs-rec`, and more than a handful of datatype
/// declarations per file) are left to the tests.
pub const FILES: &[BenchFile] = &[
    // BMC software unrolling: long symbols, the deepest QF_BV terms
    file(
        "qf_bv/soft_float_1.17",
        "non-incremental/QF_BV/bmc-bv-svcomp14/soft_float_1_true.c.cil.c.17.smt2",
    ),
    // multiple constant multiplication encodings: deep bit-vector arithmetic,
    // three bytes per token, the highest per-application cost in the set
    file("qf_bv/mcm-186", "non-incremental/QF_BV/mcm/186.smt2"),
    // symbolic execution queries: over 200 thousand indexed identifiers,
    // 150 thousand small assertions and declarations
    file(
        "qf_bv/catchconv-15803",
        "non-incremental/QF_BV/uclid/catchconv/catchconv-15803.smt2",
    ),
    // Verus verification conditions: thousands of quantified assertions
    // with pattern annotations, let terms, and datatype declarations
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
    // hybrid automata encoding: the densest decimals in the corpus, in let
    // terms nested almost nine thousand levels deep
    file(
        "qf_nra/hycomp-etcs_braking",
        "non-incremental/QF_NRA/hycomp/etcs_braking_2.01.seq_lazy_lemmas_global_15.smt2",
    ),
    // temporal planning: a single assertion of let terms nested almost nine
    // thousand levels deep
    file(
        "qf_rdl/tempo-width-6",
        "non-incremental/QF_RDL/SMT-Temporal-Planning-Benchmarks/tempo-width-6.smt2",
    ),
    // symbolic execution in SSA form: over 300 thousand single-binding let
    // terms, each binding one application, chained 2500 levels deep; the
    // dominant let shape in the corpus, and the shape of its largest files
    file(
        "qf_bv/sage2-14918",
        "non-incremental/QF_BV/Sage2/bench_14918.smt2",
    ),
    // k-induction software verification: incremental script of 60 thousand
    // small define-fun commands with push
    file(
        "inc-qf_bv/cpachecker-problem12",
        "incremental/QF_BV/20190307-CPAchecker_kInduction-SoSy_Lab/\
         Problem12_label08_smt-query.0.smt2",
    ),
    // bounded model checking of weak memory models: over 200 thousand quoted
    // symbols, hexadecimal literals, over a hundred check-sat rounds
    file(
        "inc-qf_bv/dartagnan-3631839658",
        "incremental/QF_BV/20250315-BMC_WMM/dartagnan-3631839658.ll.smt2",
    ),
    // embedded floating-point code: tens of thousands of hexadecimal and
    // hundreds of binary literals in fp terms, let terms, push and pop
    file(
        "inc-qf_abvfp/vector-automotive-33c13c0e",
        "incremental/QF_ABVFP/20210211-Vector/Automotive_C/33c13c0e.smt2",
    ),
    // Kind model checker: incremental script whose assertions are dominated
    // by let bindings
    file(
        "inc-qf_uflia/kind-microwave11",
        "incremental/QF_UFLIA/kind/microwave11.ec.smt2",
    ),
    // access control policies: thousands of existential quantifiers, and a
    // set-info with attributes before each of almost eight thousand
    // check-sat rounds
    file(
        "inc-uflra/asasp-2_2_19",
        "incremental/UFLRA/asasp/hierarchy_explicit/bench_2_2_19_random10.smt2",
    ),
];

/// The corpus root: `SMT_BENCHMARKS_DIR`, or `../benchmarks/2025` relative to
/// the current directory, which cargo sets to the package root.
///
/// An embedded absolute path would make the code layout, and so the
/// measured throughput, depend on where the package is checked out.
pub fn benchmarks_dir() -> PathBuf {
    match std::env::var_os("SMT_BENCHMARKS_DIR") {
        Some(dir) => PathBuf::from(dir),
        None => PathBuf::from("../benchmarks/2025"),
    }
}

/// The files a run selects, as labels and paths relative to the corpus
/// root: those named by `SMT_BENCH_FILES` in the order given, or all of
/// [`FILES`].
pub fn selected_files() -> Result<Vec<(String, PathBuf)>, String> {
    match std::env::var("SMT_BENCH_FILES") {
        Ok(labels) => {
            let mut files = Vec::new();
            for label in labels.split(',').map(str::trim).filter(|s| !s.is_empty()) {
                match FILES.iter().find(|file| file.label == label) {
                    Some(file) => files.push((file.label.to_string(), PathBuf::from(file.path))),
                    None => {
                        return Err(format!(
                            "Unknown benchmark file label {:?} in SMT_BENCH_FILES",
                            label
                        ));
                    }
                }
            }
            Ok(files)
        }
        Err(_) => Ok(FILES
            .iter()
            .map(|file| (file.label.to_string(), PathBuf::from(file.path)))
            .collect()),
    }
}

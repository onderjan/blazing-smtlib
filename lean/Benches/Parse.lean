/-
Parse-throughput benchmark over pinned SMT-LIB benchmark files: the lexing and the full
lex-and-parse modes of `rust/benches/parse.rs`, measured the same way so that the two can be
compared.

Expects the SMT-LIB corpus under `../benchmarks/2025` relative to the current
directory, which is the repository root when run from `lean/`; set the
environment variable `SMT_BENCHMARKS_DIR` to use a corpus root elsewhere. Each
file is loaded into memory first, so the numbers measure lexing and parsing only, not disk
I/O. In the lexing mode, tokens are discarded by a counting handler; in the full mode, a
script parser runs over the tokens with a handler that keeps nothing (`SyntaxChecker`), as
the Rust benchmark's `read_smt` with `SmtSyntaxChecker` does.

Run with `lake exe bench-parse` from `lean/`. The table reports throughput in
MB/s and nanoseconds per token; nanoseconds per token count the tokens of the lexing mode in
both modes.

Environment variables, as for the Rust benchmark:

- `SMT_BENCH_MODE`: `lex`, `full`, or `both` (default) selects the measured modes.
- `SMT_BENCH_FILES`: comma-separated labels (see `files`) restricting the
  measured files, in the order given.
- `SMT_BENCH_ITERATIONS`: timed runs per file (default `defaultIterations`);
  warm-up runs are always added.
- `SMT_BENCH_FORMAT`: `table` (default) prints the human-readable table, `raw`
  prints one tab-separated line per file with the label, mode, byte size, and
  every timed run in seconds, and `list` prints the selected labels one per
  line without measuring anything.

An environment variable of its own:

- `SMT_BENCH_LEXER`: comma-separated lexers to measure, `v` or `z` (default `z`, the
  library's lexer; `v` is the naive lexer of the proofs, `BSmtLib.Lexer.Internal.VNaive`).
  The lexers apply to the lexing mode; the full mode uses the library's lexer. The timed runs
  of a file alternate between the lexers and the modes, so that a drift of the machine affects
  them alike. Each lexer gets its own line, and in `raw` format its own mode, `lex-v` or
  `lex-z`; with the default alone the mode stays `lex`, as in the Rust benchmark.
-/
module

import BSmtLib
import BSmtLib.Lexer.Internal.VNaive

open BSmtLib
open BSmtLib.Token
open BSmtLib.Lexer.Error (LexerError)
open BSmtLib.Lexer.Cursor (LexerCursor)

/- The loops over a cursor's tokens end as each step consumes a token: they descend by the
producer's consumption, which is well-founded. -/
local instance {batch : BatchTag} : WellFoundedRelation (LexerCursor batch) :=
  ⟨Cursor.Consumed, Cursor.consumed_wf⟩

/-- Default timed runs per file; additional warm-up runs are discarded. -/
def defaultIterations : Nat := 5

/-- Minimum total duration of the discarded warm-up runs, in nanoseconds. -/
def warmUpNanos : Nat := 100_000_000

/-- A benchmarked file: a short label used in output and for selection,
and its path relative to the corpus root. -/
structure BenchFile where
  label : String
  path : String

/-- Benchmarked files, the same as `FILES` in `rust/benches/common/mod.rs`,
where the choice of each is explained. -/
def files : Array BenchFile := #[
  ⟨"qf_bv/soft_float_1.17",
    "non-incremental/QF_BV/bmc-bv-svcomp14/soft_float_1_true.c.cil.c.17.smt2"⟩,
  ⟨"qf_bv/mcm-186", "non-incremental/QF_BV/mcm/186.smt2"⟩,
  ⟨"qf_bv/catchconv-15803", "non-incremental/QF_BV/uclid/catchconv/catchconv-15803.smt2"⟩,
  ⟨"ufdtlia/verus-zookeeper-7",
    "non-incremental/UFDTLIA/20241211-verus/anvil/" ++
    "zookeeper-smt-zookeeper_controller__proof__helper_invariants__proof.7.smt2"⟩,
  ⟨"qf_slia/ip_int_from_string-460",
    "non-incremental/QF_SLIA/2019-full_str_int/py-conbyte_z3str/" ++
    "lib_int-ipaddress__ip_int_from_string/460.smt2"⟩,
  ⟨"qf_ufdt/vlsat3_k44", "non-incremental/QF_UFDT/20210312-Bouvier/vlsat3_k44.smt2"⟩,
  ⟨"qf_nra/hycomp-etcs_braking",
    "non-incremental/QF_NRA/hycomp/etcs_braking_2.01.seq_lazy_lemmas_global_15.smt2"⟩,
  ⟨"qf_rdl/tempo-width-6",
    "non-incremental/QF_RDL/SMT-Temporal-Planning-Benchmarks/tempo-width-6.smt2"⟩,
  ⟨"qf_bv/sage2-14918", "non-incremental/QF_BV/Sage2/bench_14918.smt2"⟩,
  ⟨"inc-qf_bv/cpachecker-problem12",
    "incremental/QF_BV/20190307-CPAchecker_kInduction-SoSy_Lab/" ++
    "Problem12_label08_smt-query.0.smt2"⟩,
  ⟨"inc-qf_bv/dartagnan-3631839658",
    "incremental/QF_BV/20250315-BMC_WMM/dartagnan-3631839658.ll.smt2"⟩,
  ⟨"inc-qf_abvfp/vector-automotive-33c13c0e",
    "incremental/QF_ABVFP/20210211-Vector/Automotive_C/33c13c0e.smt2"⟩,
  ⟨"inc-qf_uflia/kind-microwave11", "incremental/QF_UFLIA/kind/microwave11.ec.smt2"⟩,
  ⟨"inc-uflra/asasp-2_2_19",
    "incremental/UFLRA/asasp/hierarchy_explicit/bench_2_2_19_random10.smt2"⟩
]

/-- Token handler that only counts tokens, so timed lexing includes no parsing. -/
structure DiscardTokens where
  tokens : Nat

/- LEAN: the Rust `while cursor.next().is_some()` loop, carrying the proof that the tokens were
consumed; it ends as every step consumes a token. The loop is tail recursive, so it accumulates
the proof from the origin rather than extending it on return; the first token is taken before
the loop, as consuming nothing is no `Consumed`. -/
/--
Takes every token remaining in the cursor, which has one, running `step` for each.
-/
@[specialize step]
def takeEach [Monad m] {batch : BatchTag} (step : m Unit) (cursor : LexerCursor batch)
    (h : cursor.HasNext) :
    m { c : LexerCursor batch // c.Consumed cursor } := do
  let (_, ⟨next, consumed⟩) := cursor.next h
  step
  go next consumed
where
  /-- Takes every token remaining in `current`, which has consumed from `cursor`. -/
  @[specialize step]
  go (current : LexerCursor batch) (consumed : current.Consumed cursor) :
      m { c : LexerCursor batch // c.Consumed cursor } := do
    if h : current.HasNext then
      let (_, ⟨next, taken⟩) := current.next h
      step
      go next (taken.trans consumed)
    else
      return ⟨current, consumed⟩
  termination_by current
  decreasing_by exact taken

instance : Consume DiscardTokens Unit Empty where
  isConcrete := false

instance {batch : BatchTag} : ConsumeFrom DiscardTokens (LexerCursor batch) Id where
  consume cursor h := do
    let step := modify fun (handler : DiscardTokens) => { tokens := handler.tokens + 1 }
    return (.ok .continue, ← takeEach step cursor h)

/-- The script reader of the Rust benchmark's `read_smt`: a script parser under the default
posture, over the syntax checker, lexing from the default version. -/
abbrev CheckingAdapter :=
  Parser.Adapter.ParseAdapter SyntaxChecker (Parser.Script.ScriptParser SyntaxChecker)

/-- Lexes and parses the in-memory file, failing unless it parsed without an error. -/
def parseFromMemory (data : ByteArray) (path : String) : IO Unit := do
  let adapter : CheckingAdapter :=
    Parser.Adapter.ParseAdapter.new {}
      (Parser.Script.ScriptParser.new Version.VersionPosture.default)
  match Id.run ((Lexer.new adapter default).lexAll data.toByteSlice) with
  | .ok _ => pure ()
  | .error (err, _) =>
    match err.cause with
    | .lexical kind =>
      throw <| IO.userError s!"benchmark file {path} must parse, got lexer error \
        {repr kind} at {repr err.span}"
    | .consumer error =>
      match error.cause with
      | .syntax kind =>
        throw <| IO.userError s!"benchmark file {path} must parse, got parser error {repr kind}"
      | .version kind =>
        throw <| IO.userError s!"benchmark file {path} must parse, got version error {repr kind}"
      | .handler nonstandard =>
        throw <| IO.userError s!"benchmark file {path} must parse, got nonstandard command \
          {(String.fromUTF8? nonstandard.name.asSlice.toByteArray).getD "(not UTF-8)"}"

/-- Fails unless the file lexed without an error. -/
def checkLexed (result : Except (LexerError Empty × β) α) (path : String) : IO Unit :=
  match result with
  | .ok _ => pure ()
  | .error (err, _) =>
    match err.cause with
    | .lexical kind =>
      throw <| IO.userError s!"benchmark file {path} must lex, got {repr kind} at {repr err.span}"
    | .consumer never => nomatch never

/-- A lexer of the chain from the specification to the library's lexer. -/
inductive LexerChoice where
  | v
  | z
  deriving BEq

/-- The name of the lexer, as `SMT_BENCH_LEXER` gives it. -/
def LexerChoice.name : LexerChoice → String
  | .v => "v"
  | .z => "z"

/-- The lexer of the name, if any. -/
def LexerChoice.ofName? : String → Option LexerChoice
  | "v" => some .v
  | "z" => some .z
  | _ => none

/-- Lexes the in-memory file with the lexer, discarding tokens. -/
def lexFromMemory (choice : LexerChoice) (data : ByteArray) (path : String) : IO Unit := do
  let handler : DiscardTokens := { tokens := 0 }
  let naive := Lexer.Internal.VNaive.Lexer.new handler .v2_7
  match choice with
  | .v => checkLexed (Id.run (naive.lexAll data.toByteSlice)) path
  | .z => checkLexed (Id.run ((Lexer.new handler .v2_7).lexAll data.toByteSlice)) path

/- LEAN: the lexer owns its handler and does not give it back, where the Rust benchmark lends
the handler with `&mut` and reads the count afterwards. The count is therefore taken once,
outside the timed runs, by a handler that adds to a reference. -/
/-- Token handler that counts tokens in a reference. -/
structure CountTokens where
  tokens : IO.Ref Nat

instance : Consume CountTokens Unit Empty where
  isConcrete := false

instance {batch : BatchTag} : ConsumeFrom CountTokens (LexerCursor batch) IO where
  consume cursor h := do
    let tokens := (← get).tokens
    return (.ok .continue, ← takeEach (tokens.modify (· + 1)) cursor h)

/-- Lexes the in-memory file and returns the token count. -/
def countFromMemory (data : ByteArray) (path : String) : IO Nat := do
  let tokens ← IO.mkRef 0
  let lexer := Lexer.new ({ tokens } : CountTokens) .v2_7
  let result ← lexer.lexAll data.toByteSlice
  checkLexed result path
  tokens.get

/-- Times the actions over discarded warm-up runs of each (at least one, and at least
`warmUpNanos` in total) and `iterations` timed rounds, a round running every action once in
turn. Returns the run times of each action in seconds, in measurement order. -/
def timeRuns (iterations : Nat) (runs : Array (IO Unit)) : IO (Array (Array Float)) := do
  for run in runs do
    let warmUpStart ← IO.monoNanosNow
    repeat
      run
      if (← IO.monoNanosNow) - warmUpStart ≥ warmUpNanos then
        break
  let mut times := runs.map fun _ => #[]
  for _ in [0:iterations] do
    for i in [0:runs.size] do
      let start ← IO.monoNanosNow
      runs[i]!
      let stop ← IO.monoNanosNow
      times := times.modify i (·.push ((stop - start).toFloat / 1e9))
  return times

/-- Minimum and median of the run times, in seconds. -/
def minAndMedian (times : Array Float) : Float × Float :=
  let sorted := times.qsort (· < ·)
  (sorted[0]!, sorted[sorted.size / 2]!)

/-- The number with the given count of decimals, right-aligned in the width. -/
def fixed (value : Float) (decimals width : Nat) : String :=
  let scale := (10 : Float) ^ decimals.toFloat
  let scaled := (value * scale).round.toUInt64.toNat
  let whole := toString (scaled / 10 ^ decimals)
  let fraction := toString (scaled % 10 ^ decimals)
  let fraction := "".pushn '0' (decimals - fraction.length) ++ fraction
  let text := if decimals == 0 then whole else whole ++ "." ++ fraction
  "".pushn ' ' (width - text.length) ++ text

/-- The corpus root: `SMT_BENCHMARKS_DIR`, or `../benchmarks/2025` relative to
the current directory. -/
def benchmarksDir : IO System.FilePath := do
  match ← IO.getEnv "SMT_BENCHMARKS_DIR" with
  | some dir => pure dir
  | none => pure "../benchmarks/2025"

/-- The files a run selects: those named by `SMT_BENCH_FILES` in the order
given, or all of `files`. -/
def selectedFiles : IO (Except String (Array BenchFile)) := do
  match ← IO.getEnv "SMT_BENCH_FILES" with
  | none => return .ok files
  | some labels =>
    let mut selected := #[]
    for label in labels.splitOn "," do
      let label := label.trimAscii.toString
      if label.isEmpty then
        continue
      match files.find? (·.label == label) with
      | some file => selected := selected.push file
      | none => return .error s!"Unknown benchmark file label {repr label} in SMT_BENCH_FILES"
    return .ok selected

inductive Format where
  | table
  | raw
  | list

public def main : IO UInt32 := do
  let stderr ← IO.getStderr
  let stdout ← IO.getStdout
  let benchmarksDir ← benchmarksDir

  let (lexMode, fullMode) ← match ← IO.getEnv "SMT_BENCH_MODE" with
    | none | some "" | some "both" => pure (true, true)
    | some "lex" => pure (true, false)
    | some "full" => pure (false, true)
    | some other =>
      stderr.putStrLn s!"Unknown SMT_BENCH_MODE {repr other}; use \"lex\", \"full\", or \"both\""
      return 1

  let format ← match ← IO.getEnv "SMT_BENCH_FORMAT" with
    | none | some "" | some "table" => pure Format.table
    | some "raw" => pure Format.raw
    | some "list" => pure Format.list
    | some other =>
      stderr.putStrLn s!"Unknown SMT_BENCH_FORMAT {repr other}; use \"table\", \"raw\", or \"list\""
      return 1

  let iterations ← match ← IO.getEnv "SMT_BENCH_ITERATIONS" with
    | none => pure defaultIterations
    | some value =>
      match value.toNat? with
      | some iterations =>
        if iterations > 0 then pure iterations
        else
          stderr.putStrLn s!"Invalid SMT_BENCH_ITERATIONS {repr value}; use a positive number"
          return 1
      | none =>
        stderr.putStrLn s!"Invalid SMT_BENCH_ITERATIONS {repr value}; use a positive number"
        return 1

  let files ← match ← selectedFiles with
    | .ok files => pure files
    | .error message =>
      stderr.putStrLn message
      return 1

  let lexers ← match ← IO.getEnv "SMT_BENCH_LEXER" with
    | none | some "" => pure #[LexerChoice.z]
    | some names =>
      let mut lexers := #[]
      for name in names.splitOn "," do
        let name := name.trimAscii.toString
        match LexerChoice.ofName? name with
        | some lexer => lexers := lexers.push lexer
        | none =>
          stderr.putStrLn s!"Unknown lexer {repr name} in SMT_BENCH_LEXER; use v or z"
          return 1
      pure lexers
  -- the mode names the lexer, except for the library's lexer measured alone, as in Rust
  let modeOf (lexer : LexerChoice) : String :=
    if lexers == #[.z] then "lex" else s!"lex-{lexer.name}"

  if let .list := format then
    for file in files do
      stdout.putStrLn file.label
    return 0

  if !(← benchmarksDir.pathExists) then
    stderr.putStrLn s!"Benchmark corpus not found at {benchmarksDir}; unpack the SMT-LIB corpus \
      there or set SMT_BENCHMARKS_DIR to its root"
    return 1

  let labelWidth := files.foldl (fun width file => max width file.label.length) 0

  for file in files do
    let path := benchmarksDir / file.path
    let data ← IO.FS.readBinFile path
    let megabytes := data.size.toFloat / 1_000_000.0
    -- the token count turns run times into nanoseconds per token
    let tokens := (max (← countFromMemory data path.toString) 1).toFloat

    -- the measured modes, each with its run: the lexers' in turn, then the full pipeline's
    let mut measured : Array (String × IO Unit) := #[]
    if lexMode then
      measured := measured ++ lexers.map fun lexer =>
        (modeOf lexer, lexFromMemory lexer data path.toString)
    if fullMode then
      measured := measured.push ("full", parseFromMemory data path.toString)
    let times ← timeRuns iterations (measured.map (·.2))

    for ((mode, _), times) in measured.zip times do
      match format with
      | .table =>
        let (min, median) := minAndMedian times
        stdout.putStrLn s!"{file.label.pushn ' ' (labelWidth - file.label.length)}  \
          {fixed megabytes 2 7} MB  {mode.pushn ' ' (6 - mode.length)} \
          {fixed (megabytes / min) 1 6}/{fixed (megabytes / median) 1 6} \
          MB/s {fixed (min * 1e9 / tokens) 2 5} ns/tok"
      | .raw =>
        let runs := " ".intercalate (times.toList.map toString)
        stdout.putStrLn s!"{file.label}\t{mode}\t{data.size}\t{runs}"
      | .list => pure ()
    stdout.flush

  if let .table := format then
    stdout.putStrLn s!"(throughput as min/median over {iterations} runs; ns/tok from the min)"
  return 0

/-
The script parser's `parse`, which runs the fused script reader (`BSmtLib.Parser.Internal.Fused`)
on the lexer's cursors, against the script parser's loop over single tokens
(`BSmtLib.Parser.Internal.parseByToken`), both run by the parse adapter: timing and differential
checks.

Usage, with `lake exe bench-fused-parser` from `lean/`:

- `time <reader> <runs> <file>...`: parses each file `runs` times with the reader (`lex`, the
  lexer alone; `null`, the parse adapter with a parser that does nothing; `port`, the loop over
  single tokens; `fused`, the script parser's `parse`; `read`, `Reader.readSmt`; `port-io`,
  `fused-io` with the syntax checker in `IO`; and `term-port`, `term-fused`, `term-read` with a
  syntax checker that accepts non-standard commands of one term, which the library's term parser
  parses), printing one line per file with the tokens, the bytes and the best and median time of
  a run in nanoseconds.
- `check <list> <root> <mode>`: for each path in the file `list` (relative to `root`), runs the
  loop over single tokens and the script parser's `parse` with a recording handler and compares
  the calls, the result and the
  error with its span. `mode` is `small` (the whole input, in pieces, from 2.0 and 2.5, the
  handler failing at up to 40 calls, cut at every byte, a bad byte at every byte), `whole`,
  `cuts`, `all` (as `small`, sampled) or `big` (as `all`, sampled more thinly, for large files).
-/
module

import BSmtLib

open BSmtLib
open BSmtLib.Token
open BSmtLib.Lexer.Error (LexerError)
open BSmtLib.Lexer.Cursor (LexerCursor)
open BSmtLib.Grammar (Index Ident Pattern SpecialConstant)
open BSmtLib.Span (Located)

/- The loops over a cursor's tokens end as each step consumes a token: they descend by the
producer's consumption, which is well-founded. -/
local instance {batch : BatchTag} : WellFoundedRelation (LexerCursor batch) :=
  ⟨Cursor.Consumed, Cursor.consumed_wf⟩

/-! ## The syntax checker of the benchmark: the library's `SyntaxChecker`, and one in `IO` -/

/-- The syntax checker in `IO`, as a solver's handler would run: it counts the commands in a
reference, so that the calls are not pure. -/
structure SyntaxCheckerIO where
  commands : IO.Ref Nat

instance : Handler SyntaxCheckerIO IO where
  Error := Lexicon.Value.Symbol
  SExpr := Unit
  Attribute := Unit
  «Sort» := Unit
  Term := Unit
  Scope := Unit
  setVersion _ := pure ()
  handleSort _ _ := pure ()
  handleTerm _ := pure ()
  handleSExpr _ := pure ()
  handleAttribute _ _ := pure ()
  annotateTerm _ _ := pure ()
  startLet _ := pure ()
  endLet _ _ := pure ()
  startQuantifier _ _ := pure ()
  endQuantifier _ _ _ := pure ()
  startLambda _ := pure ()
  endLambda _ _ := pure ()
  startMatch _ := pure ()
  startMatchCase _ _ := pure ()
  endMatchCase _ _ _ := pure ()
  endMatch _ _ := pure ()

/-- A command counted. -/
@[inline]
def countCommand : ExceptT Lexicon.Value.Symbol (StateT SyntaxCheckerIO IO) Unit := do
  let h ← get
  (h.commands.modify (· + 1) : IO Unit)

instance : CommandHandler SyntaxCheckerIO IO where
  NonstandardParser := Empty
  nonstandardCommand name := throw name
  commandAssert _ := countCommand
  commandCheckSat := countCommand
  commandCheckSatAssuming _ := countCommand
  commandDeclareConst _ _ := countCommand
  startDeclareDatatype _ _ := pure ()
  endDeclareDatatype _ := countCommand
  startDeclareDatatypes _ := pure ()
  startDatatypeDeclaration _ := pure ()
  endDatatypeDeclaration _ := pure ()
  endDeclareDatatypes := countCommand
  commandDeclareFun _ _ _ := countCommand
  commandDeclareSort _ _ := countCommand
  commandDeclareSortParameter _ := countCommand
  commandDefineConst _ _ _ := countCommand
  startDefineFun _ := pure ()
  endDefineFun _ := countCommand
  startDefineFunRec _ := pure ()
  endDefineFunRec _ := countCommand
  startDefineFunsRec _ := pure ()
  startRecursiveBody _ := pure ()
  endRecursiveBody _ := pure ()
  endDefineFunsRec := countCommand
  startDefineSort _ _ := pure ()
  endDefineSort _ := countCommand
  commandEcho _ := countCommand
  commandExit := countCommand
  commandGetAssertions := countCommand
  commandGetAssignment := countCommand
  commandGetInfo _ := countCommand
  commandGetModel := countCommand
  commandGetOption _ := countCommand
  commandGetProof := countCommand
  commandGetUnsatAssumptions := countCommand
  commandGetUnsatCore := countCommand
  commandGetValue _ := countCommand
  commandPop _ := countCommand
  commandPush _ := countCommand
  commandReset := countCommand
  commandResetAssertions := countCommand
  commandSetInfo _ := countCommand
  commandSetLogic _ := countCommand
  commandSetOption _ := countCommand

/-- A parser that takes every token and does nothing: the floor of the parse adapter. -/
structure NullParser where

instance :
    Parser.Internal.ParseByToken NullParser SyntaxChecker Id NonstandardCommandError Unit where
  arrive _ _ := pure ()
  step _ p token := match token with
    | .endOfInput => pure (.done ())
    | _ => pure (.more p)
  reset p := p

instance : Parser.Parse NullParser SyntaxChecker Id NonstandardCommandError Unit where
  parse := Parser.Internal.parseByToken

/-- The script parser parsing by its loop over single tokens, never by the fused reader. -/
structure PortParser (H : Type) {m : Type → Type} [CommandHandler H m] where
  inner : Parser.ScriptParser H

/-- The script parser, parsing by its loop over single tokens. -/
def PortParser.new {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m]
    (posture : Version.VersionPosture) : PortParser H :=
  ⟨Parser.ScriptParser.new (H := H) posture⟩

instance {H : Type} {m : Type → Type} [Monad m] [CommandHandler H m] :
    Parser.Parse (PortParser H) H m (Handler.Error H) Unit where
  parse parser state cursor := do
    let (answer, inner, state, next) ← Parser.Internal.parseByToken parser.inner state cursor
    return (answer, ⟨inner⟩, state, next)

/-! ## A syntax checker that accepts non-standard commands of one term -/

/-- The syntax checker of the benchmark, accepting every non-standard command whose payload is
one term, which its parser parses with the library's term parser. -/
structure TermCommandChecker where

instance : Handler TermCommandChecker Id where
  Error := NonstandardCommandError
  SExpr := Unit
  Attribute := Unit
  «Sort» := Unit
  Term := Unit
  Scope := Unit
  setVersion _ := pure ()
  handleSort _ _ := pure ()
  handleTerm _ := pure ()
  handleSExpr _ := pure ()
  handleAttribute _ _ := pure ()
  annotateTerm _ _ := pure ()
  startLet _ := pure ()
  endLet _ _ := pure ()
  startQuantifier _ _ := pure ()
  endQuantifier _ _ _ := pure ()
  startLambda _ := pure ()
  endLambda _ _ := pure ()
  startMatch _ := pure ()
  startMatchCase _ _ := pure ()
  endMatchCase _ _ _ := pure ()
  endMatch _ _ := pure ()

/-- The rule of a non-standard command of one term. -/
structure TermRule where

instance : Parser.CommandRule TermRule TermCommandChecker where
  Parser := Parser.ClosedParser TermCommandChecker (Parser.TermParser TermCommandChecker)
  Result := Unit
  handle self _ := pure self

instance : CommandHandler TermCommandChecker Id where
  NonstandardParser := Parser.CommandPayloadParser TermCommandChecker TermRule
  nonstandardCommand _ := return .new {} (.new .new)
  commandAssert _ := pure ()
  commandCheckSat := pure ()
  commandCheckSatAssuming _ := pure ()
  commandDeclareConst _ _ := pure ()
  startDeclareDatatype _ _ := pure ()
  endDeclareDatatype _ := pure ()
  startDeclareDatatypes _ := pure ()
  startDatatypeDeclaration _ := pure ()
  endDatatypeDeclaration _ := pure ()
  endDeclareDatatypes := pure ()
  commandDeclareFun _ _ _ := pure ()
  commandDeclareSort _ _ := pure ()
  commandDeclareSortParameter _ := pure ()
  commandDefineConst _ _ _ := pure ()
  startDefineFun _ := pure ()
  endDefineFun _ := pure ()
  startDefineFunRec _ := pure ()
  endDefineFunRec _ := pure ()
  startDefineFunsRec _ := pure ()
  startRecursiveBody _ := pure ()
  endRecursiveBody _ := pure ()
  endDefineFunsRec := pure ()
  startDefineSort _ _ := pure ()
  endDefineSort _ := pure ()
  commandEcho _ := pure ()
  commandExit := pure ()
  commandGetAssertions := pure ()
  commandGetAssignment := pure ()
  commandGetInfo _ := pure ()
  commandGetModel := pure ()
  commandGetOption _ := pure ()
  commandGetProof := pure ()
  commandGetUnsatAssumptions := pure ()
  commandGetUnsatCore := pure ()
  commandGetValue _ := pure ()
  commandPop _ := pure ()
  commandPush _ := pure ()
  commandReset := pure ()
  commandResetAssertions := pure ()
  commandSetInfo _ := pure ()
  commandSetLogic _ := pure ()
  commandSetOption _ := pure ()

/-- Token handler that only counts tokens. -/
structure CountTokens where
  tokens : Nat

instance : Consume CountTokens Unit Empty where
  isConcrete := false

/-- Takes every token of the cursor, counting. -/
def countRest {batch : BatchTag} (origin : LexerCursor batch) (n : Nat) (cursor : LexerCursor batch)
    (consumed : cursor.Consumed origin) : Nat × { c : LexerCursor batch // c.Consumed origin } :=
  if h : cursor.HasNext then
    let (_, ⟨next, taken⟩) := cursor.next h
    countRest origin (n + 1) next (taken.trans consumed)
  else (n, ⟨cursor, consumed⟩)
termination_by cursor
decreasing_by exact taken

instance {batch : BatchTag} : ConsumeFrom CountTokens (LexerCursor batch) Id where
  consume cursor h := do
    let (_, ⟨next, consumed⟩) := cursor.next h
    let (n, done) := countRest cursor 1 next consumed
    modify fun c => { tokens := c.tokens + n }
    return (.ok .continue, done)

/-! ## Timing -/

/-- Fails unless the result is a success. -/
def expectOk {α β : Type} (what : String) : Except α β → IO Unit
  | .ok _ => pure ()
  | .error _ => throw (IO.userError s!"{what}: the parse failed")

set_option maxHeartbeats 0 in
/-- One run of the reader on the data. -/
def runOnce (reader : String) (data : ByteArray) : IO Unit := do
  let input := data.toByteSlice
  match reader with
  | "lex" =>
    expectOk reader (Id.run ((Lexer.new ({ tokens := 0 } : CountTokens) .v2_7).lexAll input))
  | "null" =>
    let adapter := Parser.ParseAdapter.new ({} : SyntaxChecker) ({} : NullParser)
    expectOk reader (Id.run ((Lexer.new adapter default).lexAll input))
  | "port" =>
    let adapter : Parser.ParseAdapter SyntaxChecker (PortParser SyntaxChecker) :=
      Parser.ParseAdapter.new {} (PortParser.new Version.VersionPosture.default)
    expectOk reader (Id.run ((Lexer.new adapter default).lexAll input))
  | "fused" =>
    let adapter : Parser.ParseAdapter SyntaxChecker (Parser.ScriptParser SyntaxChecker) :=
      Parser.ParseAdapter.new {} (Parser.ScriptParser.new Version.VersionPosture.default)
    expectOk reader (Id.run ((Lexer.new adapter default).lexAll input))
  | "read" =>
    expectOk reader (Id.run (Reader.readSmt (n := Id) ({} : SyntaxChecker) input)).1
  | "term-port" =>
    let adapter : Parser.ParseAdapter TermCommandChecker (PortParser TermCommandChecker) :=
      Parser.ParseAdapter.new {} (PortParser.new Version.VersionPosture.default)
    expectOk reader (Id.run ((Lexer.new adapter default).lexAll input))
  | "term-fused" =>
    let adapter : Parser.ParseAdapter TermCommandChecker (Parser.ScriptParser TermCommandChecker) :=
      Parser.ParseAdapter.new {} (Parser.ScriptParser.new Version.VersionPosture.default)
    expectOk reader (Id.run ((Lexer.new adapter default).lexAll input))
  | "term-read" =>
    expectOk reader (Id.run (Reader.readSmt (n := Id) ({} : TermCommandChecker) input)).1
  | "port-io" =>
    let handler : SyntaxCheckerIO := { commands := ← IO.mkRef 0 }
    let adapter : Parser.ParseAdapter SyntaxCheckerIO (PortParser SyntaxCheckerIO) :=
      Parser.ParseAdapter.new handler (PortParser.new Version.VersionPosture.default)
    expectOk reader (← (Lexer.new adapter default).lexAll input)
  | "fused-io" =>
    let handler : SyntaxCheckerIO := { commands := ← IO.mkRef 0 }
    let adapter : Parser.ParseAdapter SyntaxCheckerIO (Parser.ScriptParser SyntaxCheckerIO) :=
      Parser.ParseAdapter.new handler (Parser.ScriptParser.new Version.VersionPosture.default)
    expectOk reader (← (Lexer.new adapter default).lexAll input)
  | other => throw (IO.userError s!"unknown reader {other}")

/-- The tokens of the data. -/
def countTokens (data : ByteArray) : Nat :=
  match Id.run ((Lexer.new ({ tokens := 0 } : CountTokens) .v2_7).lexAll data.toByteSlice) with
  | .ok (_, lexer) => lexer.consumer.tokens
  | .error _ => 0

def timeMain (reader : String) (runs : Nat) (files : List String) : IO Unit := do
  for file in files do
    let data ← IO.FS.readBinFile file
    let tokens := countTokens data
    let mut times : Array Nat := #[]
    for _ in [0:runs] do
      let start ← IO.monoNanosNow
      runOnce reader data
      let stop ← IO.monoNanosNow
      times := times.push (stop - start)
    if runs == 0 then continue
    let sorted := times.qsort (· < ·)
    let best := sorted[0]?.getD 0
    let median := sorted[sorted.size / 2]?.getD 0
    IO.println s!"{reader}\t{file}\t{tokens}\t{data.size}\t{best}\t{median}"

/-! ## The recording handler -/

/-- A handler that writes every call down in a log, and fails at the call numbered `failAt`. -/
structure Rec where
  log : IO.Ref (Array String)
  failAt : Nat

/-- The bytes of a slice, as text. -/
def showBytes (slice : ByteSlice) : String :=
  slice.toByteArray.foldl (init := "") fun s b => s.push (Char.ofNat b.toNat)

def showSym (s : Lexicon.Value.Symbol) : String :=
  "|" ++ showBytes s.asSlice ++ (if s.isQuoted then "|q" else "|")

def showIndex : Index → String
  | .numeral d => "#" ++ showBytes d.asSlice
  | .symbol s => showSym s

def showIdent (i : Ident) : String :=
  if i.indices.isEmpty then showSym i.name
  else "(_ " ++ showSym i.name ++ " " ++ " ".intercalate (i.indices.toList.map showIndex) ++ ")"

def showConst : SpecialConstant → String
  | .numeral d => "num " ++ showBytes d.asSlice
  | .decimal d => "dec " ++ showBytes d.asSlice
  | .hexadecimal d => "hex " ++ showBytes d.asSlice
  | .binary d => "bin " ++ showBytes d.asSlice
  | .string d => "str " ++ showBytes d.asSlice

def showNats (xs : Array Nat) : String := toString xs.toList

def nat (x : Nat) : String := toString x

def showPairs (xs : Array (Lexicon.Value.Symbol × Nat)) : String :=
  " ".intercalate (xs.toList.map fun (s, n) => showSym s ++ ":" ++ toString n)

def showSoW : Grammar.Nodes.SimplePattern → String
  | .symbol s => showSym s
  | .wildcard => "_"

def showPattern : Pattern → String
  | .simple s => showSoW s
  | .application app =>
    "(" ++ showSym app.constructor ++ " " ++ " ".intercalate (app.args.toList.map showSoW) ++ ")"

def showSig (s : Grammar.Multiple.FunctionSignature Nat) : String :=
  showSym s.name ++ " (" ++ showPairs s.params ++ ") " ++ toString s.resultSort

def showCons (c : Lexicon.Value.Symbol × Grammar.Multiple.SortedVars Nat) : String :=
  showSym c.1 ++ " (" ++ showPairs c.2.toArray ++ ")"

/-- Writes the call down and returns its number, or fails if it is the one to fail at. -/
@[inline]
def recCall (s : String) : ExceptT String (StateT Rec IO) Nat := do
  let r ← get
  let n ← (r.log.modifyGet fun a => (a.size, a.push s) : IO Nat)
  if n == r.failAt then throw s!"fail at {n}"
  return n

def recUnit (s : String) : ExceptT String (StateT Rec IO) Unit := do
  let _ ← recCall s

instance : Handler Rec IO where
  Error := String
  SExpr := Nat
  Attribute := Nat
  «Sort» := Nat
  Term := Nat
  Scope := Nat
  setVersion v := do
    let r ← get
    (r.log.modify (·.push s!"setVersion {repr v}") : IO Unit)
  handleSort i args := recCall s!"sort {showIdent i} {showNats args.asSlice}"
  handleTerm node := recCall (match node with
    | .specialConstant c => "term " ++ showConst c
    | .qualifiedIdent i s => s!"term id {showIdent i} {s.map fun x => nat x}"
    | .application f s args _ =>
      s!"term app {showIdent f} {s.map fun x => nat x} {showNats args.asSlice}")
  handleSExpr node := recCall (match node with
    | .specialConstant c => "sexpr " ++ showConst c
    | .symbol s => "sexpr " ++ showSym s
    | .reserved w => "sexpr reserved " ++ w.asStr
    | .keyword k => "sexpr :" ++ showBytes k.asSlice
    | .sExprs items => s!"sexpr list {showNats items.asSlice}")
  handleAttribute k v := recCall (s!"attr :{showBytes k.asSlice} " ++ match v with
    | none => "none"
    | some (.specialConstant c) => showConst c
    | some (.symbol s) => showSym s
    | some (.sExprs items) => showNats items.asSlice)
  annotateTerm t attrs := recCall s!"annotate {nat t} {showNats attrs.asSlice}"
  startLet bs := recCall s!"startLet {showPairs bs.toArray}"
  endLet s t := recCall s!"endLet {nat s} {nat t}"
  startQuantifier q vs := recCall s!"startQuantifier {q == .forall} {showPairs vs.toArray}"
  endQuantifier q s t := recCall s!"endQuantifier {q == .forall} {nat s} {nat t}"
  startLambda vs := recCall s!"startLambda {showPairs vs.toArray}"
  endLambda s t := recCall s!"endLambda {nat s} {nat t}"
  startMatch t := recUnit s!"startMatch {nat t}"
  startMatchCase t p := recCall s!"startMatchCase {nat t} {showPattern p}"
  endMatchCase s t b := recCall s!"endMatchCase {nat s} {nat t} {nat b}"
  endMatch t cs := recCall
    s!"endMatch {nat t} {" ".intercalate (cs.toArray.toList.map fun (p, b) =>
      showPattern p ++ "->" ++ nat b)}"


instance : CommandHandler Rec IO where
  NonstandardParser := Empty
  nonstandardCommand name := throw ("nonstandard " ++ showSym name)
  commandAssert t := recUnit s!"assert {nat t}"
  commandCheckSat := recUnit "check-sat"
  commandCheckSatAssuming ts := recUnit s!"check-sat-assuming {showNats ts.asSlice}"
  commandDeclareConst s t := recUnit s!"declare-const {showSym s} {nat t}"
  startDeclareDatatype s ps := recUnit
    s!"startDeclareDatatype {showSym s} {" ".intercalate (ps.toArray.toList.map showSym)}"
  endDeclareDatatype cs := recUnit
    s!"endDeclareDatatype {" ".intercalate (cs.toArray.toList.map showCons)}"
  startDeclareDatatypes ss := recUnit
    s!"startDeclareDatatypes {" ".intercalate (ss.toArray.toList.map fun (s, n) =>
      showSym s ++ showBytes n.asSlice)}"
  startDatatypeDeclaration ps := recUnit
    s!"startDatatypeDeclaration {" ".intercalate (ps.toArray.toList.map showSym)}"
  endDatatypeDeclaration cs := recUnit
    s!"endDatatypeDeclaration {" ".intercalate (cs.toArray.toList.map showCons)}"
  endDeclareDatatypes := recUnit "endDeclareDatatypes"
  commandDeclareFun s ps r := recUnit s!"declare-fun {showSym s} {showNats ps.asSlice} {nat r}"
  commandDeclareSort s n := recUnit s!"declare-sort {showSym s} {showBytes n.asSlice}"
  commandDeclareSortParameter s := recUnit s!"declare-sort-parameter {showSym s}"
  commandDefineConst s t b := recUnit s!"define-const {showSym s} {nat t} {nat b}"
  startDefineFun sig := recUnit s!"startDefineFun {showSig sig}"
  endDefineFun b := recUnit s!"endDefineFun {nat b}"
  startDefineFunRec sig := recUnit s!"startDefineFunRec {showSig sig}"
  endDefineFunRec b := recUnit s!"endDefineFunRec {nat b}"
  startDefineFunsRec sigs := recUnit
    s!"startDefineFunsRec {" ; ".intercalate (sigs.toArray.toList.map showSig)}"
  startRecursiveBody sig := recUnit s!"startRecursiveBody {showSig sig}"
  endRecursiveBody b := recUnit s!"endRecursiveBody {nat b}"
  endDefineFunsRec := recUnit "endDefineFunsRec"
  startDefineSort s ps := recUnit
    s!"startDefineSort {showSym s} {" ".intercalate (ps.toArray.toList.map showSym)}"
  endDefineSort t := recUnit s!"endDefineSort {nat t}"
  commandEcho c := recUnit s!"echo {showBytes c.asSlice}"
  commandExit := recUnit "exit"
  commandGetAssertions := recUnit "get-assertions"
  commandGetAssignment := recUnit "get-assignment"
  commandGetInfo k := recUnit s!"get-info {showBytes k.asSlice}"
  commandGetModel := recUnit "get-model"
  commandGetOption k := recUnit s!"get-option {showBytes k.asSlice}"
  commandGetProof := recUnit "get-proof"
  commandGetUnsatAssumptions := recUnit "get-unsat-assumptions"
  commandGetUnsatCore := recUnit "get-unsat-core"
  commandGetValue ts := recUnit s!"get-value {showNats ts.asSlice}"
  commandPop n := recUnit s!"pop {showBytes n.asSlice}"
  commandPush n := recUnit s!"push {showBytes n.asSlice}"
  commandReset := recUnit "reset"
  commandResetAssertions := recUnit "reset-assertions"
  commandSetInfo a := recUnit s!"set-info {nat a}"
  commandSetLogic s := recUnit s!"set-logic {showSym s}"
  commandSetOption a := recUnit s!"set-option {nat a}"

/-! ## Differential checks -/

/-- What a read gave: the calls, then the result. -/
def showResult {E R L : Type} (showE : E → String)
    (result : Except (LexerError (Parser.ParseError E) × L)
      (Option (Located R) × α)) : String :=
  match result with
  | .ok (none, _) => "ok none"
  | .ok (some located, _) => s!"ok at {repr located.location}"
  | .error (err, _) =>
    let kind := match err.kind with
      | .lexical kind => s!"lexical {repr kind}"
      | .consumer error =>
        match error.kind with
        | .syntax kind => s!"syntax {repr kind}"
        | .version kind => s!"version {repr kind}"
        | .handler e => s!"handler {showE e}"
    s!"error {kind} at {repr err.span}"

/-- Feeds the data to the lexer in pieces of `piece` bytes (all at once for 0), then the end. -/
def feed {C R E : Type} [Consume C R E] [∀ batch, ConsumeFrom C (LexerCursor batch) IO]
    (lexer : Lexer C) (data : ByteArray) (piece : Nat) :
    IO (Except (LexerError E × Unit) (Option (Located R) × Lexer C)) := do
  if piece == 0 then
    return (← lexer.lexAll data.toByteSlice).map id |>.mapError fun (e, _) => (e, ())
  let mut lexer := lexer
  let mut offset := 0
  while offset < data.size do
    let stop := min data.size (offset + piece)
    match ← lexer.lexSlice (data.toByteSlice offset stop) with
    | .ok next => lexer := next
    | .error (e, _) => return .error (e, ())
    offset := stop
  match ← lexer.lexEof with
  | .ok result => return .ok result
  | .error (e, _) => return .error (e, ())

/-- What the read gave, as text. -/
def showRead {C R : Type} [Consume C R (Parser.ParseError String)]
    [∀ batch, ConsumeFrom C (LexerCursor batch) IO] (adapter : C) (data : ByteArray)
    (version : Version) (piece : Nat) : IO String := do
  return showResult id (← feed (Lexer.new adapter version) data piece)

set_option maxHeartbeats 0 in
/-- A read of the data with the reader, the version to start from, the pieces and the call to
fail at: the log of calls and the result, as text. -/
def readWith (reader : String) (data : ByteArray) (version : Version) (piece failAt : Nat) :
    IO (Array String × String) := do
  let log ← IO.mkRef #[]
  let handler : Rec := { log, failAt }
  let posture := Version.VersionPosture.default
  let result ← match reader with
    | "port" =>
      let adapter : Parser.ParseAdapter Rec (PortParser Rec) :=
        Parser.ParseAdapter.new handler (PortParser.new posture)
      showRead adapter data version piece
    | "fused" =>
      let adapter : Parser.ParseAdapter Rec (Parser.ScriptParser Rec) :=
        Parser.ParseAdapter.new handler (Parser.ScriptParser.new posture)
      showRead adapter data version piece
    | other => throw (IO.userError s!"unknown reader {other}")
  return (← log.get, result)

/-- Compares the two readers on the data; returns a description of the first difference. -/
def compareReaders (variant : String) (data : ByteArray) (version : Version) (piece failAt : Nat) :
    IO (Option String) := do
  let (log₁, res₁) ← readWith "port" data version piece failAt
  let (log₂, res₂) ← readWith variant data version piece failAt
  if res₁ != res₂ then
    return some s!"result: port {res₁} / fast {res₂}"
  if log₁.size != log₂.size then
    return some s!"log sizes {log₁.size} / {log₂.size}"
  for (i, a, b) in (List.range log₁.size).zip (log₁.toList.zip log₂.toList) do
    if a != b then
      return some s!"call {i}: port {a} / fast {b}"
  return none

/-- The number of calls the port makes on the whole data. -/
def callCount (data : ByteArray) : IO Nat := do
  let (log, _) ← readWith "port" data .v2_7 0 0xFFFFFFFF
  return log.size

/-- Sampled offsets in the data: all for small data, about `count` spread out otherwise. -/
def offsets (size count : Nat) : List Nat :=
  if size ≤ count then List.range (size + 1)
  else (List.range (count + 1)).map fun i => i * size / count

def checkFile (variant : String) (path : String) (mode : String) : IO Bool := do
  let data ← IO.FS.readBinFile path
  let mut cases : Array (String × ByteArray × Version × Nat × Nat) := #[]
  let none' := 0xFFFFFFFF
  if mode == "whole" || mode == "all" || mode == "small" then
    for piece in [0, 1, 7, 64, 4093] do
      cases := cases.push (s!"piece {piece}", data, .v2_7, piece, none')
    cases := cases.push ("from 2.0", data, .v2_0, 0, none')
    cases := cases.push ("from 2.5", data, .v2_5, 0, none')
    let calls ← callCount data
    for k in offsets calls (if mode == "small" || mode == "all" then 40 else 6) do
      cases := cases.push (s!"fail at call {k}", data, .v2_7, 0, k)
  if mode == "cuts" || mode == "all" || mode == "small" then
    let count := if mode == "small" then 100000 else if mode == "all" then 40 else 400
    for cut in offsets data.size count do
      cases := cases.push (s!"cut at {cut}", data.extract 0 cut, .v2_7, 0, none')
    let count := if mode == "small" then 100000 else if mode == "all" then 20 else 200
    for cut in offsets data.size count do
      let bad := (data.extract 0 cut).push 0x01 ++ data.extract cut data.size
      cases := cases.push (s!"bad byte at {cut}", bad, .v2_7, 0, none')
  if mode == "big" then
    for piece in [0, 4093, 65521] do
      cases := cases.push (s!"piece {piece}", data, .v2_7, piece, none')
    cases := cases.push ("from 2.0", data, .v2_0, 0, none')
    let calls ← callCount data
    for k in offsets calls 3 do
      cases := cases.push (s!"fail at call {k}", data, .v2_7, 0, k)
    for cut in offsets data.size 8 do
      cases := cases.push (s!"cut at {cut}", data.extract 0 cut, .v2_7, 0, none')
    for cut in offsets data.size 4 do
      let bad := (data.extract 0 cut).push 0x01 ++ data.extract cut data.size
      cases := cases.push (s!"bad byte at {cut}", bad, .v2_7, 0, none')
  let mut ok := true
  for (name, input, version, piece, failAt) in cases do
    if let some diff ← compareReaders variant input version piece failAt then
      IO.println s!"DIFF {path} [{name}]: {diff}"
      ok := false
      break
  return ok

def checkMain (variant list root mode : String) : IO UInt32 := do
  let paths := (← IO.FS.lines list).filter (· != "")
  let mut failed := 0
  let mut done := 0
  for path in paths do
    let full := if root == "" then path else root ++ "/" ++ path
    if !(← checkFile variant full mode) then
      failed := failed + 1
    done := done + 1
  IO.println s!"checked {done} files ({mode}), {failed} with differences"
  return if failed == 0 then 0 else 1

public def main (args : List String) : IO UInt32 := do
  match args with
  | "time" :: reader :: runs :: files => timeMain reader (runs.toNat?.getD 1) files; return 0
  | ["check", list, root, mode] => checkMain "fused" list root mode
  | ["check", list, root, mode, variant] => checkMain variant list root mode
  | _ =>
    IO.eprintln
      "usage: bench-fused-parser time <reader> <runs> <file>... | check <list> <root> <mode>"
    return 2

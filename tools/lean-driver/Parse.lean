/-
The parser requests of the driver protocol, see the section "The parser" of
`lean/driver-protocol.md`, answered by the parsers and the reader of the Lean library through
its public interface.

The handler of a request asks the Rust side: it writes a `call` line for every call and reads the
answer before it goes on. The values it makes, and its errors, are the numbers the Rust side
answers with. The buffered reader of `all` and `read-smt` asks the Rust side for its bytes the
same way.

With the library's lexer the requests use `Reader`, `readSmt` and `readSmtFile`. The other lexers
have no reader: the driver runs them over the library's parse adapter and does what the reader
does, step for step (`Emulated`).
-/
module

public import BSmtLib
public import BSmtLib.Lexer.Internal.VNaive
public import BSmtLib.Lexer.Internal.WRustPort
public import BSmtLib.Lexer.Internal.X1BatchInCore
public import Protocol

public section

open BSmtLib
open BSmtLib.Token (Consume ConsumeFrom Cursor)
open BSmtLib.Version (VersionPosture VersionPostureBuilder)
open BSmtLib.Lexer.Cursor (LexerCursor)
open BSmtLib.Lexer (LexerError)
open BSmtLib.Parser (Parse ParseState ParseAdapter ParseError SyntaxErrorKind SyntaxExpected
  NonEmptyList VersionErrorKind ScriptParser
  CommandParser SortParser TermParser SExprParser CommandOutcome SymbolParser KeywordParser
  StringParser NumeralParser OpenParenParser CloseParenParser IdentParser QualifiedIdentParser
  ClosedAttributeParser ClosedMultipleAttributeParser PatternParser SortedVarParser PairParser
  ClosedParser ParenParser ClosedMultipleParser ParenMultipleParser)
open BSmtLib.Reader (ReadError ReadFailure BufRead BufReader readSmt readSmtFile)
open BSmtLib.Grammar
open BSmtLib.Span (Location Located)

namespace ParseRequests

/-! ## The conversation with the Rust side -/

/-- The streams over which the driver talks to the Rust side. -/
structure Remote where
  stdin : IO.FS.Stream
  stdout : IO.FS.Stream

/-- Fails the request, with the message as the text of its `fail` line. -/
def failRequest {α : Type} (message : String) : IO α :=
  throw (IO.userError message)

/-- Writes a line of the response. -/
def Remote.write (remote : Remote) (line : String) : IO Unit :=
  remote.stdout.putStr (line ++ "\n")

/-- Writes the call and reads its answer, one line. -/
def Remote.ask (remote : Remote) (call : String) : IO String := do
  remote.write s!"call {call}"
  -- the Rust side answers only once it has seen the call
  remote.stdout.flush
  let line ← remote.stdin.getLine
  if line.isEmpty then
    failRequest s!"the input ended before the answer to call {call}"
  return lineContent line

/-- Fails the request on an answer that does not fit the call. -/
def badAnswer {α : Type} (call answer : String) : IO α :=
  failRequest s!"unexpected answer {repr answer} to call {call}"

/-- The handler's error: one the Rust side answered a call with, by its number. -/
inductive RemoteError where
  | rust (id : Nat)

/-- The monad of the handler's calls. -/
abbrev HandlerM := ExceptT RemoteError (StateT Remote IO)

/-- The number in an answer. -/
def answerId (call answer word : String) : IO Nat :=
  match word.toNat? with
  | some id => pure id
  | none => badAnswer call answer

/-- A call that makes a value: the answer is `ok <id>` or `err <id>`. -/
def callValue (call : String) : HandlerM Nat := do
  let answer ← (← get).ask call
  match answer.splitOn " " with
  | ["ok", id] => answerId call answer id
  | ["err", id] => throwThe RemoteError (.rust (← answerId call answer id))
  | _ => badAnswer call answer

/-- A call that makes no value: the answer is `ok` or `err <id>`. -/
def callUnit (call : String) : HandlerM Unit := do
  let answer ← (← get).ask call
  match answer.splitOn " " with
  | ["ok"] => pure ()
  | ["err", id] => throwThe RemoteError (.rust (← answerId call answer id))
  | _ => badAnswer call answer

/-! ## The fields of the calls -/

def symbolField (symbol : Lexicon.Value.Symbol) : String :=
  (if symbol.isQuoted then "q" else "u") ++ hex symbol.asSlice

def constantField : SpecialConstant → String
  | .numeral digits => "N" ++ hex digits.asSlice
  | .decimal text => "D" ++ hex text.asSlice
  | .hexadecimal digits => "X" ++ hex digits.asSlice
  | .binary digits => "B" ++ hex digits.asSlice
  | .string content => "S" ++ hex content.asSlice

/-- The number of the items, followed by the field of each. -/
def listField {α : Type} (field : α → String) (items : Array α) : String :=
  items.foldl (fun out item => s!"{out} {field item}") (toString items.size)

def indexField : Index → String
  | .numeral digits => "n" ++ hex digits.asSlice
  | .symbol symbol => symbolField symbol

def identField (identifier : Ident) : String :=
  s!"{symbolField identifier.name} {listField indexField identifier.indices}"

def idField (id : Nat) : String :=
  toString id

def optIdField : Option Nat → String
  | none => "-"
  | some id => toString id

def idsField (ids : Array Nat) : String :=
  listField toString ids

/-- Symbols, each with the number of a value. -/
def boundField (pairs : Array (Lexicon.Value.Symbol × Nat)) : String :=
  listField (fun (symbol, id) => s!"{symbolField symbol} {id}") pairs

def symbolsField (symbols : Array Lexicon.Value.Symbol) : String :=
  listField symbolField symbols

def sowField : SimplePattern → String
  | .symbol symbol => symbolField symbol
  | .wildcard => "_"

def patternField : Pattern → String
  | .simple symbol => s!"p {sowField symbol}"
  | .application application =>
    s!"c {symbolField application.constructor} {listField sowField application.args}"

/-! The owned values that the category parsers give, written as their views are. -/

def symbolBufField (symbol : Lexicon.Value.SymbolBuf) : String :=
  symbolField symbol.view

def identBufField (identifier : Grammar.Nodes.IdentBuf) : String :=
  identField identifier.view

def sowBufField : Grammar.Nodes.SimplePatternBuf → String
  | .symbol symbol => symbolBufField symbol
  | .wildcard => "_"

def patternBufField : Grammar.Nodes.PatternBuf → String
  | .simple symbol => s!"p {sowBufField symbol}"
  | .application application =>
    s!"c {symbolBufField application.constructor} {listField sowField application.args.view}"

def quantifierField : QuantifierKind → String
  | .«forall» => "forall"
  | .«exists» => "exists"

def signatureField (signature : Grammar.Multiple.FunctionSignature Nat) : String :=
  s!"{symbolField signature.name} {boundField signature.params} {signature.resultSort}"

def constructorsField (constructors : Constructors Nat) : String :=
  listField (fun (constructor, selectors) =>
    s!"{symbolField constructor} {boundField selectors.toArray}") constructors.toArray

/-! ## The handler -/

instance : Handler Remote IO where
  Error := RemoteError
  SExpr := Nat
  Attribute := Nat
  «Sort» := Nat
  Term := Nat
  Scope := Nat
  setVersion version := do
    let call := s!"set_version {versionName version}"
    let answer ← (← get).ask call
    unless answer == "ok" do
      badAnswer call answer
  handleSort identifier sorts :=
    callValue s!"handle_sort {identField identifier} {idsField sorts.asSlice}"
  handleTerm
    | .specialConstant constant => callValue s!"handle_term c {constantField constant}"
    | .qualifiedIdent identifier sort =>
      callValue s!"handle_term i {identField identifier} {optIdField sort}"
    | .application function sort arguments _ =>
      callValue s!"handle_term a {identField function} {optIdField sort} \
        {idsField arguments.asSlice}"
  handleSExpr
    | .specialConstant constant => callValue s!"handle_s_expr c {constantField constant}"
    | .symbol symbol => callValue s!"handle_s_expr s {symbolField symbol}"
    | .reserved word => callValue s!"handle_s_expr r {word.asStr}"
    | .keyword name => callValue s!"handle_s_expr k x{hex name.asSlice}"
    | .sExprs items => callValue s!"handle_s_expr l {idsField items.asSlice}"
  handleAttribute name value :=
    let value := match value with
      | none => "-"
      | some (.specialConstant constant) => s!"c {constantField constant}"
      | some (.symbol symbol) => s!"s {symbolField symbol}"
      | some (.sExprs items) => s!"l {idsField items.asSlice}"
    callValue s!"handle_attribute x{hex name.asSlice} {value}"
  annotateTerm term attributes := callValue s!"annotate_term {term} {idsField attributes.asSlice}"
  startLet bindings := callValue s!"start_let {boundField bindings.toArray}"
  endLet scope body := callValue s!"end_let {scope} {body}"
  startQuantifier quantifier variables :=
    callValue s!"start_quantifier {quantifierField quantifier} {boundField variables.toArray}"
  endQuantifier quantifier scope body :=
    callValue s!"end_quantifier {quantifierField quantifier} {scope} {body}"
  startLambda variables := callValue s!"start_lambda {boundField variables.toArray}"
  endLambda scope body := callValue s!"end_lambda {scope} {body}"
  startMatch scrutinee := callUnit s!"start_match {scrutinee}"
  startMatchCase scrutinee pattern :=
    callValue s!"start_match_case {scrutinee} {patternField pattern}"
  endMatchCase scope scrutinee body := callValue s!"end_match_case {scope} {scrutinee} {body}"
  endMatch scrutinee cases :=
    callValue s!"end_match {scrutinee} \
      {listField (fun (pattern, body) => s!"{patternField pattern} {body}") cases.toArray}"

/-- The rule of a non-standard command that the handler accepts: one term, then the closing
parenthesis, as the Rust tests' handler accepts (`parse_backend::rust::NonstandardRule`). -/
structure NonstandardRule where

instance : Parser.CommandRule NonstandardRule Remote where
  Parser := ClosedParser Remote (TermParser Remote)
  Result := Nat
  handle self term := do
    callUnit s!"nonstandard_term {idField term}"
    return self

/-- The parser of a non-standard command's payload that the Rust side chose in its answer to
`nonstandard_command`, as the Rust tests' handler chooses (`parse_backend::rust::
NonstandardParser`). -/
inductive NonstandardParser where
  /-- One term, then the closing parenthesis. -/
  | term (parser : Parser.CommandPayloadParser Remote NonstandardRule)
  /-- The closing parenthesis, after which the parser switches the cursor to the version. -/
  | switchVersion (version : Version)
  /-- The closing parenthesis, after which the parser has the cursor discard the rest of the
  input. -/
  | discardRest

instance : Parse NonstandardParser Remote IO RemoteError Unit where
  parse self state cursor := do
    match self with
    | .term parser =>
      let (answer, parser, state, next) ← Parse.parse parser state cursor
      return (answer, .term parser, state, next)
    | .switchVersion version =>
      let (answer, _, state, next) ← Parse.parse CloseParenParser.new state cursor
      match answer with
      | .ok (.break ()) =>
        match switched : Cursor.setVersion next.1 version with
        | .ok after =>
          return (.ok (.break ()), self, state,
            ⟨after, fun has => Cursor.setVersion_consumed (next.2 has) switched⟩)
        | .error _ => return (.error (ParseError.version .unsupported), self, state, next)
      | answer => return (answer, self, state, next)
    | .discardRest =>
      let (answer, _, state, next) ← Parse.parse CloseParenParser.new state cursor
      match answer with
      | .ok (.break ()) =>
        return (.ok (.break ()), self, state,
          ⟨Cursor.discardRest next.1, fun has => Cursor.discardRest_consumed (next.2 has)⟩)
      | answer => return (answer, self, state, next)

instance : CommandHandler Remote IO where
  NonstandardParser := NonstandardParser
  nonstandardCommand symbol := do
    let call := s!"nonstandard_command {symbolField symbol}"
    let answer ← (← get).ask call
    match answer.splitOn " " with
    | ["ok"] => return .term (.new {} (.new .new))
    | ["ok", "switch", version] =>
      match readVersion version with
      | .ok version => return .switchVersion version
      | .error _ => badAnswer call answer
    | ["ok", "discard"] => return .discardRest
    | ["err", id] => throwThe RemoteError (.rust (← answerId call answer id))
    | _ => badAnswer call answer
  commandAssert term := callUnit s!"command_assert {idField term}"
  commandCheckSat := callUnit "command_check_sat"
  commandCheckSatAssuming terms := callUnit s!"command_check_sat_assuming {idsField terms.asSlice}"
  commandDeclareConst symbol sort :=
    callUnit s!"command_declare_const {symbolField symbol} {idField sort}"
  startDeclareDatatype symbol parameters :=
    callUnit s!"start_declare_datatype {symbolField symbol} {symbolsField parameters.toArray}"
  endDeclareDatatype constructors :=
    callUnit s!"end_declare_datatype {constructorsField constructors}"
  startDeclareDatatypes sorts :=
    callUnit s!"start_declare_datatypes \
      {listField (fun (symbol, arity) => s!"{symbolField symbol} x{hex arity.asSlice}")
        sorts.toArray}"
  startDatatypeDeclaration parameters :=
    callUnit s!"start_datatype_declaration {symbolsField parameters.toArray}"
  endDatatypeDeclaration constructors :=
    callUnit s!"end_datatype_declaration {constructorsField constructors}"
  endDeclareDatatypes := callUnit "end_declare_datatypes"
  commandDeclareFun symbol parameters result :=
    callUnit s!"command_declare_fun {symbolField symbol} {idsField parameters.asSlice} \
      {idField result}"
  commandDeclareSort symbol arity :=
    callUnit s!"command_declare_sort {symbolField symbol} x{hex arity.asSlice}"
  commandDeclareSortParameter symbol :=
    callUnit s!"command_declare_sort_parameter {symbolField symbol}"
  commandDefineConst symbol sort term :=
    callUnit s!"command_define_const {symbolField symbol} {idField sort} {idField term}"
  startDefineFun signature := callUnit s!"start_define_fun {signatureField signature}"
  endDefineFun body := callUnit s!"end_define_fun {idField body}"
  startDefineFunRec signature := callUnit s!"start_define_fun_rec {signatureField signature}"
  endDefineFunRec body := callUnit s!"end_define_fun_rec {idField body}"
  startDefineFunsRec signatures :=
    callUnit s!"start_define_funs_rec {listField signatureField signatures.toArray}"
  startRecursiveBody signature :=
    callUnit s!"start_recursive_body {signatureField signature}"
  endRecursiveBody body := callUnit s!"end_recursive_body {idField body}"
  endDefineFunsRec := callUnit "end_define_funs_rec"
  startDefineSort symbol parameters :=
    callUnit s!"start_define_sort {symbolField symbol} {symbolsField parameters.toArray}"
  endDefineSort sort := callUnit s!"end_define_sort {idField sort}"
  commandEcho text := callUnit s!"command_echo x{hex text.asSlice}"
  commandExit := callUnit "command_exit"
  commandGetAssertions := callUnit "command_get_assertions"
  commandGetAssignment := callUnit "command_get_assignment"
  commandGetInfo name := callUnit s!"command_get_info x{hex name.asSlice}"
  commandGetModel := callUnit "command_get_model"
  commandGetOption name := callUnit s!"command_get_option x{hex name.asSlice}"
  commandGetProof := callUnit "command_get_proof"
  commandGetUnsatAssumptions := callUnit "command_get_unsat_assumptions"
  commandGetUnsatCore := callUnit "command_get_unsat_core"
  commandGetValue terms := callUnit s!"command_get_value {idsField terms.asSlice}"
  commandPop count := callUnit s!"command_pop x{hex count.asSlice}"
  commandPush count := callUnit s!"command_push x{hex count.asSlice}"
  commandReset := callUnit "command_reset"
  commandResetAssertions := callUnit "command_reset_assertions"
  commandSetInfo attr := callUnit s!"command_set_info {idField attr}"
  commandSetLogic symbol := callUnit s!"command_set_logic {symbolField symbol}"
  commandSetOption attr := callUnit s!"command_set_option {idField attr}"

/-! ## The buffered reader -/

/- LEAN: `BufRead.consume` is pure, so it only counts. The count is reported at the next fill and
at the end of the request; what has been reported is kept in a reference, as the reader may give
back an earlier copy of the buffered reader (`Reader.readFrom` after a failed fill), whose count
has been reported already. -/
/-- The buffered reader whose bytes are on the Rust side. -/
structure RemoteBuf where
  remote : Remote
  /-- The number of bytes consumed. -/
  consumed : Nat
  /-- The number of consumed bytes reported to the Rust side. -/
  reported : IO.Ref Nat

def RemoteBuf.new (remote : Remote) : IO RemoteBuf := do
  return { remote, consumed := 0, reported := ← IO.mkRef 0 }

/-- Reports the bytes consumed since the last report, if there are any. -/
def RemoteBuf.report (self : RemoteBuf) : IO Unit := do
  let reported ← self.reported.get
  if reported < self.consumed then
    let call := s!"consume {self.consumed - reported}"
    let answer ← self.remote.ask call
    unless answer == "ok" do
      badAnswer call answer
    self.reported.set self.consumed

instance : BufRead RemoteBuf IO where
  fillBuf self := do
    self.report
    let call := "fill"
    let answer ← self.remote.ask call
    -- an operand without bytes may come with or without the space before it
    let (word, operand) ← match answer.splitOn " " with
      | [word] => pure (word, "")
      | [word, operand] => pure (word, operand)
      | _ => badAnswer call answer
    let bytes ← match unhex operand with
      | .ok bytes => pure bytes
      | .error _ => badAnswer call answer
    match word with
    | "bytes" => return .ok (bytes.toByteSlice, self)
    | "ioerr" =>
      match String.fromUTF8? bytes with
      | some message => return .error (IO.userError message)
      | none => badAnswer call answer
    | _ => badAnswer call answer
  consume self amount := { self with consumed := self.consumed + amount }

/-! ## The response lines -/

/-- The general reserved word, spelled as the Rust variant. -/
def generalReservedName : Lexicon.Reserved.GeneralReserved → String
  | .binary => "Binary"
  | .decimal => "Decimal"
  | .hexadecimal => "Hexadecimal"
  | .numeral => "Numeral"
  | .string => "String"
  | .underscore => "Underscore"
  | .exclamationMark => "ExclamationMark"
  | .as => "As"
  | .lambda => "Lambda"
  | .let => "Let"
  | .exists => "Exists"
  | .forall => "Forall"
  | .match => "Match"
  | .par => "Par"

/-- The command name, spelled as the Rust variant. -/
def commandNameReservedName : Lexicon.Reserved.CommandNameReserved → String
  | .assert => "Assert"
  | .checkSat => "CheckSat"
  | .checkSatAssuming => "CheckSatAssuming"
  | .declareConst => "DeclareConst"
  | .declareDatatype => "DeclareDatatype"
  | .declareDatatypes => "DeclareDatatypes"
  | .declareFun => "DeclareFun"
  | .declareSort => "DeclareSort"
  | .declareSortParameter => "DeclareSortParameter"
  | .defineConst => "DefineConst"
  | .defineFun => "DefineFun"
  | .defineFunRec => "DefineFunRec"
  | .defineFunsRec => "DefineFunsRec"
  | .defineSort => "DefineSort"
  | .echo => "Echo"
  | .exit => "Exit"
  | .getAssertions => "GetAssertions"
  | .getAssignment => "GetAssignment"
  | .getInfo => "GetInfo"
  | .getModel => "GetModel"
  | .getOption => "GetOption"
  | .getProof => "GetProof"
  | .getUnsatAssumptions => "GetUnsatAssumptions"
  | .getUnsatCore => "GetUnsatCore"
  | .getValue => "GetValue"
  | .pop => "Pop"
  | .push => "Push"
  | .reset => "Reset"
  | .resetAssertions => "ResetAssertions"
  | .setInfo => "SetInfo"
  | .setLogic => "SetLogic"
  | .setOption => "SetOption"

/-- The item a syntax error expected, spelled as its Rust `Debug` form without spaces. -/
def syntaxExpectedName : SyntaxExpected → String
  | .token category => s!"Token({tokenTypeName category})"
  | .reserved (.general word) => s!"Reserved(General({generalReservedName word}))"
  | .reserved (.commandName word) => s!"Reserved(CommandName({commandNameReservedName word}))"
  | .symbol => "Symbol"
  | .index => "Index"
  | .ident => "Ident"
  | .sort => "Sort"
  | .term => "Term"
  | .sExpr => "SExpr"
  | .attribute => "Attribute"
  | .operator => "Operator"
  | .commandName => "CommandName"
  | .propositionalLiteral => "PropositionalLiteral"

/-- The list that must not be empty, spelled as the Rust variant. -/
def nonEmptyListName : NonEmptyList → String
  | .identIndices => "IdentIndices"
  | .sortApplication => "SortApplication"
  | .termApplication => "TermApplication"
  | .letBindings => "LetBindings"
  | .annotation => "Annotation"
  | .quantifierVars => "QuantifierVars"
  | .lambdaVars => "LambdaVars"
  | .functionSignatures => "FunctionSignatures"
  | .datatypeIntroductions => "DatatypeIntroductions"
  | .datatypeParameters => "DatatypeParameters"
  | .datatypeConstructors => "DatatypeConstructors"
  | .patternArguments => "PatternArguments"
  | .matchCases => "MatchCases"
  | .getValueTerms => "GetValueTerms"

/-- The syntax error kind, spelled as the Rust `Debug` form of the kind without spaces. -/
def syntaxKindName : SyntaxErrorKind → String
  | .expected items => s!"Expected([{",".intercalate (items.toList.map syntaxExpectedName)}])"
  | .empty list => s!"Empty({nonEmptyListName list})"
  | .missing .functionBody => "Missing(FunctionBody)"
  | .missing .datatype => "Missing(Datatype)"

/-- The version error kind, spelled as the Rust `Debug` form of the kind. -/
def versionKindName : VersionErrorKind → String
  | .unsupported => "Unsupported"
  | .tooManyDeclarations limit => s!"TooManyDeclarations({limit})"

/-- The line of an error that ended a request. -/
def errorLine (err : ReadError RemoteError) : String :=
  let kind := match err.kind with
    | .io error => s!"io {hex (toString error).toUTF8.toByteSlice}"
    | .lexical kind => s!"lexical {errorKindName kind}"
    | .syntax kind => s!"syntax {syntaxKindName kind}"
    | .version kind => s!"version {versionKindName kind}"
    | .handler (.rust id) => s!"handler {id}"
  s!"error {location err.span.start} {location err.span.end} {kind}"

/-- The field of what the command parser finished with. -/
def commandResult : CommandOutcome → String
  | .command => "command"
  | .exit => "exit"
  | .endOfFile => "end"
  | .setVersion version => s!"set-version {versionName version}"

/-! ## The lexers -/

/-- The operations of a lexer over the consumer `C`, which stops at its first error. -/
structure LexOps (C : Type) {R E : Type} [Consume C R E] where
  Lexer : Type
  new : C → Version → Lexer
  lexSlice : Lexer → ByteSlice → IO (Except (LexerError E) Lexer)
  lexEof : Lexer → IO (Except (LexerError E) (Option (Located R) × Lexer))
  currentLocation : Lexer → Location
  version : Lexer → Version
  discardedFrom : Lexer → Option Location

/-- The operations of the chosen lexer over the consumer. -/
def lexOps (choice : LexerChoice) (C : Type) {R E : Type} [Consume C R E]
    [∀ batch, ConsumeFrom C (LexerCursor batch) IO] : LexOps C :=
  match choice with
  | .z =>
    { Lexer := BSmtLib.Lexer C
      new := BSmtLib.Lexer.new
      lexSlice := fun lexer slice => do return (← lexer.lexSlice slice).mapError (·.1)
      lexEof := fun lexer => do return (← lexer.lexEof).mapError (·.1)
      currentLocation := BSmtLib.Lexer.currentLocation
      version := BSmtLib.Lexer.version
      discardedFrom := BSmtLib.Lexer.discardedFrom }
  | .w =>
    { Lexer := Lexer.Internal.WRustPort.Lexer C
      new := Lexer.Internal.WRustPort.Lexer.new
      lexSlice := fun lexer slice => do
        return (← Lexer.Internal.WRustPort.Lexer.lexSlice lexer slice).mapError (·.1)
      lexEof := fun lexer => do
        return (← Lexer.Internal.WRustPort.Lexer.lexEof lexer).mapError (·.1)
      currentLocation := Lexer.Internal.WRustPort.Lexer.currentLocation
      version := Lexer.Internal.WRustPort.Lexer.version
      discardedFrom := Lexer.Internal.WRustPort.Lexer.discardedFrom }
  | .x1 =>
    { Lexer := Lexer.Internal.WRustPort.Lexer C
      new := Lexer.Internal.WRustPort.Lexer.new
      lexSlice := fun lexer slice => do
        return (← Lexer.Internal.X1BatchInCore.Lexer.lexSlice lexer slice).mapError (·.1)
      lexEof := fun lexer => do
        return (← Lexer.Internal.X1BatchInCore.Lexer.lexEof lexer).mapError (·.1)
      currentLocation := Lexer.Internal.WRustPort.Lexer.currentLocation
      version := Lexer.Internal.WRustPort.Lexer.version
      discardedFrom := Lexer.Internal.WRustPort.Lexer.discardedFrom }
  | .v =>
    { Lexer := Lexer.Internal.VNaive.Lexer C
      new := Lexer.Internal.VNaive.Lexer.new
      lexSlice := fun lexer slice => do
        return (← Lexer.Internal.VNaive.Lexer.lexSlice lexer slice).mapError (·.1)
      lexEof := fun lexer => do
        return (← Lexer.Internal.VNaive.Lexer.lexEof lexer).mapError (·.1)
      currentLocation := Lexer.Internal.VNaive.Lexer.currentLocation
      version := Lexer.Internal.VNaive.Lexer.version
      discardedFrom := Lexer.Internal.VNaive.Lexer.discardedFrom }

/-! ## The reader -/

/-- The operations of a reader of the type `S`, with the results it finishes with rendered as
their fields. A call that returns an error gives no reader back. -/
structure ReaderOps (S : Type) where
  readSlice : S → ByteSlice → IO (Except (ReadError RemoteError) S)
  readEof : S → IO (Except (ReadError RemoteError) (Option (Located String) × S))
  readAll : S → RemoteBuf →
    IO (Except (ReadError RemoteError) (Option (Located String) × S) × RemoteBuf)
  readFile : S → System.FilePath →
    IO (Except (ReadError RemoteError) (Option (Located String) × S))
  discardedFrom : S → Option Location
  version : S → Version

/-- The rendered result at its location. -/
def renderLocated {R : Type} (render : R → String) (result : Located R) : Located String :=
  BSmtLib.Span.Located.Internal.new (render result.value) result.location

/-- The operations of the library's reader. -/
def ReaderOps.library {P R : Type} [Parse P Remote IO RemoteError R] (render : R → String) :
    ReaderOps (Reader Remote P) where
  readSlice reader slice := do
    return (← reader.readSlice slice).mapError (·.error)
  readEof reader := do
    return ((← reader.readEof).mapError (·.error)).map fun (result, reader) =>
      (result.map (renderLocated render), reader)
  readAll reader buf := do
    let (result, buf) ← reader.readFrom buf
    return ((result.mapError (·.error)).map fun (result, reader) =>
      (result.map (renderLocated render), reader), buf)
  readFile reader path := do
    return ((← reader.readFile path).mapError (·.error)).map fun (result, reader) =>
      (result.map (renderLocated render), reader)
  discardedFrom := Reader.discardedFrom
  version := Reader.version

/-! What `Reader` does, step for step, over a lexer of the chain. -/

namespace Emulated

variable {C R E : Type} [Consume C R (ParseError E)] (ops : LexOps C)

/-- `Reader.readSlice`. -/
def readSlice (lexer : ops.Lexer) (slice : ByteSlice) :
    IO (Except (ReadError E) ops.Lexer) := do
  return (← ops.lexSlice lexer slice).mapError ReadError.ofLex

/-- `Reader.readEof`. -/
def readEof (lexer : ops.Lexer) :
    IO (Except (ReadError E) (Option (Located R) × ops.Lexer)) := do
  return (← ops.lexEof lexer).mapError ReadError.ofLex

/-- `Reader.readFrom`: `partial`, as a buffered reader may give bytes without end. -/
partial def readFrom {B : Type} [BufRead B IO] (lexer : ops.Lexer) (buf : B) :
    IO (Except (ReadError E) (Option (Located R) × ops.Lexer) × B) := do
  if (ops.discardedFrom lexer).isSome then
    -- the lexer does not care about any subsequent bytes
    return (← readEof ops lexer, buf)
  match ← BufRead.fillBuf buf with
  | .error err =>
    -- an empty span at the current location
    let span := Span.Internal.newEmpty (ops.currentLocation lexer)
    return (.error (ReadError.Internal.new (.io err) span), buf)
  | .ok (buffer, buf) =>
    if buffer.size == 0 then
      -- the end of the input
      return (← readEof ops lexer, buf)
    let startOffset := (ops.currentLocation lexer).offset
    match ← readSlice ops lexer buffer with
    | .error err => return (.error err, buf)
    | .ok lexer =>
      -- consume what the lexer took, which is less than the buffer when it discards
      let len := (ops.currentLocation lexer).offset - startOffset
      readFrom lexer (BufRead.consume (n := IO) buf len)

/-- `Reader.readFile`. -/
def readFile (lexer : ops.Lexer) (path : System.FilePath) :
    IO (Except (ReadError E) (Option (Located R) × ops.Lexer)) := do
  match ← (IO.FS.Handle.mk path .read).toBaseIO with
  | .error err => return .error (ReadError.Internal.new (.io err) Span.Internal.newZero)
  | .ok file =>
    let buf := BufReader.new (IO.FS.Stream.ofHandle file) Reader.Internal.BUF_READER_CAPACITY
    let (result, _) ← readFrom ops lexer buf
    return result

end Emulated

/-- The operations of a reader emulated over a lexer of the chain. -/
def ReaderOps.emulated {P R : Type} [Parse P Remote IO RemoteError R]
    (ops : LexOps (ParseAdapter Remote P)) (render : R → String) : ReaderOps ops.Lexer where
  readSlice := Emulated.readSlice ops
  readEof lexer := do
    return (← Emulated.readEof ops lexer).map fun (result, lexer) =>
      (result.map (renderLocated render), lexer)
  readAll lexer buf := do
    let (result, buf) ← Emulated.readFrom ops lexer buf
    return (result.map fun (result, lexer) => (result.map (renderLocated render), lexer), buf)
  readFile lexer path := do
    return (← Emulated.readFile ops lexer path).map fun (result, lexer) =>
      (result.map (renderLocated render), lexer)
  discardedFrom := ops.discardedFrom
  version := ops.version

/- LEAN: the reader's type depends on the lexer and the parser, so the driver holds it hidden
behind the operations on it. A reader that returned an error gives none back, so it is taken out
of its reference for every call and put back only when it is given back. -/
/-- The reader that the requests after `reader` act on. -/
structure Session where
  readSlice : ByteSlice → IO (Except (ReadError RemoteError) Unit)
  readEof : IO (Except (ReadError RemoteError) (Option (Located String)))
  readAll : RemoteBuf → IO (Except (ReadError RemoteError) (Option (Located String)) × RemoteBuf)
  readFile : System.FilePath → IO (Except (ReadError RemoteError) (Option (Located String)))
  discardedFrom : IO (Option Location)
  version : IO Version

/-- The session of the reader. -/
def Session.new {S : Type} (ops : ReaderOps S) (reader : S) : IO Session := do
  let held ← IO.mkRef (some reader)
  let take : IO S := do
    match ← held.modifyGet fun reader => (reader, none) with
    | some reader => pure reader
    | none => failRequest "no reader: none was created, or the last one returned an error"
  let look : IO S := do
    match ← held.get with
    | some reader => pure reader
    | none => failRequest "no reader: none was created, or the last one returned an error"
  -- puts the reader back if it was given back
  let keep {α : Type} (result : Except (ReadError RemoteError) (α × S)) :
      IO (Except (ReadError RemoteError) α) :=
    match result with
    | .ok (value, reader) => do held.set (some reader); return .ok value
    | .error err => return .error err
  return {
    readSlice := fun slice => do keep ((← ops.readSlice (← take) slice).map ((), ·))
    readEof := do keep (← ops.readEof (← take))
    readAll := fun buf => do
      let (result, buf) ← ops.readAll (← take) buf
      return (← keep result, buf)
    readFile := fun path => do keep (← ops.readFile (← take) path)
    discardedFrom := do return ops.discardedFrom (← look)
    version := do return ops.version (← look) }

/-- The parser a reader runs. -/
inductive ParserChoice where
  | script (posture : VersionPosture)
  | command
  | term
  | sort
  | sExpr

/-- The session of the library's reader with its lexer, or of a reader emulated over the parser
with another lexer. -/
def makeSession {P R : Type} [Parse P Remote IO RemoteError R] (choice : LexerChoice)
    (remote : Remote) (version : Version) (reader : Reader Remote P) (parser : P)
    (render : R → String) : IO Session :=
  match choice with
  | .z => Session.new (ReaderOps.library render) reader
  | other =>
    let ops := lexOps other (ParseAdapter Remote P)
    Session.new (ReaderOps.emulated ops render) (ops.new (ParseAdapter.new remote parser) version)

/- The sessions of the parsers are made one by one, so that the code of every lexer over each
parser is compiled in a declaration of its own. -/

def scriptSession (choice : LexerChoice) (remote : Remote) (version : Version)
    (posture : VersionPosture) : IO Session :=
  makeSession choice remote version (Reader.script remote posture version)
    (ScriptParser.new posture : ScriptParser Remote) fun () => "-"

def commandSession (choice : LexerChoice) (remote : Remote) (version : Version) : IO Session :=
  makeSession choice remote version (Reader.new remote CommandParser.new version)
    (CommandParser.new : CommandParser Remote) commandResult

def termSession (choice : LexerChoice) (remote : Remote) (version : Version) : IO Session :=
  makeSession choice remote version (Reader.new remote TermParser.new version)
    (TermParser.new : TermParser Remote) idField

def sortSession (choice : LexerChoice) (remote : Remote) (version : Version) : IO Session :=
  makeSession choice remote version (Reader.new remote SortParser.new version)
    (SortParser.new : SortParser Remote) idField

def sExprSession (choice : LexerChoice) (remote : Remote) (version : Version) : IO Session :=
  makeSession choice remote version (Reader.new remote SExprParser.new version)
    (SExprParser.new : SExprParser Remote) idField

/-- The session of a new reader of the parser, starting in the version. -/
def newSession (choice : LexerChoice) (remote : Remote) (version : Version) :
    ParserChoice → IO Session
  | .script posture => scriptSession choice remote version posture
  | .command => commandSession choice remote version
  | .term => termSession choice remote version
  | .sort => sortSession choice remote version
  | .sExpr => sExprSession choice remote version

/-! ## Driving a parser of a category -/

/-- The consumer of `drive`: a port of the consumer `Drive` of the Rust category tests. It has the
parser parse the cursor, again after each time it finished, until it has finished the wanted
number of times; then it counts the tokens that are not the end-of-file token, and breaks at the
end-of-file token. It does not tell the handler the version. -/
structure Drive (P R : Type) where
  handler : Remote
  parseState : ParseState Remote
  parser : P
  render : R → String
  /-- How many more results are wanted. -/
  remaining : Nat
  /-- The number of tokens after the last wanted result, the end-of-file token aside. -/
  unconsumed : IO.Ref Nat

instance {P R E : Type} [Parse P Remote IO E R] : Consume (Drive P R) Unit (ParseError E) where
  isConcrete := false

namespace Drive

variable {P R E Z : Type} [Parse P Remote IO E R] [Cursor Z]

/-- The first token of a producer that has one. -/
def first (cursor : Z) (h : Cursor.HasNext cursor) :
    Cursor.Token Z × { next : Z // Cursor.Consumed next cursor } :=
  match taken : Cursor.next? cursor with
  | some first => first
  | none => absurd (Cursor.next?_isSome h) (by rw [taken]; exact Bool.false_ne_true)

/-- Takes tokens of the cursor, which has one: counts one after the wanted results, or has the
parser parse the cursor. Gives the answer to the producer if the consumer stops, `none` if it goes
on. A parser that finished has its result written. -/
def take (drive : Drive P R) (cursor : Z) (h : Cursor.HasNext cursor) :
    IO (Option (Except (ParseError E) (ControlFlow Unit)) × Drive P R ×
      { next : Z // Cursor.Consumed next cursor }) := do
  if drive.remaining == 0 then
    -- count the tokens left after the wanted results, and break at the end of the input, as
    -- every consumer must
    let (token, next) := first cursor h
    if Cursor.syntax next.val token matches .endOfFile then
      return (some (.ok (.break ())), drive, next)
    drive.unconsumed.modify (· + 1)
    return (none, drive, next)
  let ((answer, parser, parseState, ⟨next, consumed⟩), handler) ←
    (Parse.parse drive.parser drive.parseState cursor).run drive.handler
  let drive := { drive with handler, parser, parseState }
  match answer with
  | .error err => return (some (.error err), drive, ⟨next, consumed h⟩)
  | .ok (.break result) =>
    handler.write s!"result {drive.render result}"
    return (none, { drive with remaining := drive.remaining - 1 }, ⟨next, consumed h⟩)
  | .ok .continue => return (none, drive, ⟨next, consumed h⟩)

/-- A producer, ordered by its consumption: the loop over its tokens descends by it. -/
structure Consuming (Z : Type) where
  cursor : Z

instance : WellFoundedRelation (Consuming Z) :=
  invImage Consuming.cursor ⟨Cursor.Consumed, Cursor.consumed_wf⟩

/-- Takes the tokens of `cursor`, which comes from `origin` with tokens consumed, while there are
any and the consumer goes on. -/
def rest (origin : Z) (drive : Drive P R) (cursor : Z) (consumed : Cursor.Consumed cursor origin) :
    IO (Except (ParseError E) (ControlFlow Unit) × Drive P R ×
      { z : Z // Cursor.Consumed z origin }) :=
  match Cursor.decideHasNext cursor with
  | .isFalse _ => return (.ok .continue, drive, ⟨cursor, consumed⟩)
  | .isTrue h => do
    match ← drive.take cursor h with
    | (some answer, drive, ⟨next, taken⟩) =>
      return (answer, drive, ⟨next, Cursor.consumed_trans taken consumed⟩)
    | (none, drive, ⟨next, taken⟩) => rest origin drive next (Cursor.consumed_trans taken consumed)
termination_by (⟨cursor⟩ : Consuming Z)
decreasing_by exact taken

end Drive

instance {P R E Z : Type} [Parse P Remote IO E R] [Cursor Z] : ConsumeFrom (Drive P R) Z IO where
  consume cursor h := do
    let drive ← get
    match ← (drive.take cursor h : IO _) with
    | (some answer, drive, next) =>
      set drive
      return (answer, next)
    | (none, drive, ⟨next, consumed⟩) =>
      let (answer, drive, done) ← (Drive.rest cursor drive next consumed : IO _)
      set drive
      return (answer, done)

/-- Applies the feeds to the lexer, as `lex` does, up to the first error, which it returns. -/
def applyFeeds {C R E : Type} [Consume C R E] (ops : LexOps C) :
    List (Option ByteArray) → ops.Lexer → IO (Option (LexerError E))
  | [], _ => return none
  | some slice :: feeds, lexer => do
    match ← ops.lexSlice lexer slice.toByteSlice with
    | .ok lexer => applyFeeds ops feeds lexer
    | .error err => return some err
  | none :: feeds, lexer => do
    match ← ops.lexEof lexer with
    | .ok (_, lexer) => applyFeeds ops feeds lexer
    | .error err => return some err

/-- Runs the parser over the feeds, with the consumer of `drive`, and writes the last line. -/
def runDrive {P R : Type} [Parse P Remote IO (Handler.Error Remote) R] (choice : LexerChoice)
    (remote : Remote) (version : Version) (count : Nat) (feeds : List (Option ByteArray))
    (parser : P) (render : R → String) : IO Unit := do
  let unconsumed ← IO.mkRef 0
  let ops := lexOps choice (Drive P R)
  let lexer := ops.new
    { handler := remote, parseState := .new, parser, render, remaining := count, unconsumed }
    version
  match ← applyFeeds ops feeds lexer with
  | some err => remote.write (errorLine (ReadError.ofLex err))
  | none => remote.write s!"ok {← unconsumed.get}"

/-- A parser that `drive` runs, as the request names it: a parser that takes no inner parser, a
pair, or a combinator of one inner parser. -/
inductive Driven where
  | simple (name : String)
  | pair (first second : Driven)
  | wrap (name : String) (inner : Driven)

/-- What a `drive` request does with the parser it names: run it, its results written by the
function. -/
abbrev WithParser :=
  {P R : Type} → [Parse P Remote IO (Handler.Error Remote) R] → P → (R → String) → IO Unit

/-- Gives the parser named by the simple name to `k`, with how its results are written. -/
def withSimple (k : WithParser) : String → IO Unit
  | "sort" => k (SortParser.new : SortParser Remote) idField
  | "s-expr" => k (SExprParser.new : SExprParser Remote) idField
  | "term" => k (TermParser.new : TermParser Remote) idField
  | "symbol" => k SymbolParser.new symbolBufField
  | "keyword" => k KeywordParser.new fun name =>
      "x" ++ hex name.asSlice
  | "string" => k StringParser.new fun content =>
      "x" ++ hex content.asSlice
  | "numeral" => k NumeralParser.new fun digits =>
      "x" ++ hex digits.asSlice
  | "open-paren" => k OpenParenParser.new fun () => "-"
  | "close-paren" => k CloseParenParser.new fun () => "-"
  | "ident" => k IdentParser.new identBufField
  | "qualified-ident" => k (QualifiedIdentParser.new : QualifiedIdentParser Remote)
      fun qualified => s!"{identBufField qualified.ident} {optIdField qualified.sort}"
  | "closed-attribute" => k (ClosedAttributeParser.new : ClosedAttributeParser Remote) idField
  | "closed-multiple-attribute" =>
    k (ClosedMultipleAttributeParser.new : ClosedMultipleAttributeParser Remote) idsField
  | "pattern" => k (PatternParser.new : PatternParser Remote) patternBufField
  | "sorted-var" => k (SortedVarParser.new : SortedVarParser Remote) fun (name, sort) =>
      s!"{symbolBufField name} {idField sort}"
  | name => failRequest s!"unsupported parser {name}"

/-- The names of the parsers that take no inner parser. -/
def simpleNames : List String :=
  ["sort", "s-expr", "term", "symbol", "keyword", "string", "numeral", "open-paren",
    "close-paren", "ident", "qualified-ident", "closed-attribute", "closed-multiple-attribute",
    "pattern", "sorted-var"]

/-- The names of the combinators of one inner parser. -/
def wrapperNames : List String :=
  ["closed", "paren", "closed-multiple", "paren-multiple"]

/--
Gives the parser to `k`, with how its results are written: those of a pair are the fields of the
first result, then those of the second; those of `closed` and `paren` the fields of the inner
result; those of `closed-multiple` and `paren-multiple` the number of the results, then the
fields of each.
-/
def Driven.with (k : WithParser) : Driven → IO Unit
  | .simple name => withSimple k name
  | .pair first second =>
    first.with fun parser₁ render₁ =>
      second.with fun parser₂ render₂ =>
        k (PairParser.new (H := Remote) parser₁ parser₂) fun (one, two) =>
          s!"{render₁ one} {render₂ two}"
  | .wrap name inner =>
    inner.with fun parser render =>
      match name with
      | "closed" => k (ClosedParser.new (H := Remote) parser) render
      | "paren" => k (ParenParser.new (H := Remote) parser) render
      | "closed-multiple" => k (ClosedMultipleParser.new (H := Remote) parser) (listField render)
      | "paren-multiple" =>
        k (ParenMultipleParser.new (H := Remote) parser)
          (listField render)
      | name => failRequest s!"unsupported parser {name}"

/-- The characters of a name of a parser up to the first `(`, `,` or `)`, and the rest. -/
def nameAt (chars : List Char) : String × List Char :=
  let name := chars.takeWhile fun c => c != '(' && c != ',' && c != ')'
  (String.ofList name, chars.drop name.length)

mutual

/-- The parser named at the start of the characters, and the characters after its name: a
simple parser by its name, or a combinator applied to its inner parsers, `name(inner,…)`. The
fuel bounds the nesting. -/
def readParser : Nat → List Char → Except String (Driven × List Char)
  | 0, _ => throw "the parser is nested too deeply"
  | fuel + 1, chars => do
    let (name, rest) := nameAt chars
    match rest with
    | '(' :: rest =>
      let (inner, rest) ← readArguments fuel rest
      let rest : List Char ← match rest with
        | ')' :: rest => pure rest
        | _ => throw s!"the arguments of {name} are not closed"
      match name, inner with
      | "pair", [first, second] => return (.pair first second, rest)
      | name, [inner] =>
        if wrapperNames.contains name then return (.wrap name inner, rest)
        else throw s!"unsupported parser {name}"
      | name, _ => throw s!"unsupported parser {name} of {inner.length} parsers"
    | rest =>
      if simpleNames.contains name then return (.simple name, rest)
      else throw s!"unsupported parser {name}"

/-- The parsers named at the start of the characters, separated by commas. -/
def readArguments : Nat → List Char → Except String (List Driven × List Char)
  | 0, _ => throw "the parser is nested too deeply"
  | fuel + 1, chars => do
    let (first, rest) ← readParser fuel chars
    match rest with
    | ',' :: rest =>
      let (others, rest) ← readArguments fuel rest
      return (first :: others, rest)
    | rest => return ([first], rest)

end

/-- The parser named in a `drive` request. -/
def readDriven (name : String) : Except String Driven := do
  let chars := name.toList
  match ← readParser (2 * chars.length + 2) chars with
  | (driven, []) => return driven
  | (_, rest) => throw s!"unexpected {String.ofList rest} after a parser"


/-! ## The requests -/

/-- The words that begin a parser request. -/
def requestNames : List String :=
  ["reader", "slice", "eof", "all", "file", "discarded", "version", "read-smt", "read-smt-file",
    "drive"]

/-- Reads a value of a request, failing the request if it is malformed. -/
def orFail {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => failRequest message

/-- The parser named in a `reader` request. -/
def readParserChoice (word : String) : Except String ParserChoice := do
  match word with
  | "command" => return .command
  | "term" => return .term
  | "sort" => return .sort
  | "s-expr" => return .sExpr
  | _ =>
    let some posture := word.dropPrefix? "script:"
      | throw s!"unknown parser {repr word}"
    let [versions, limit] := posture.toString.splitOn ";"
      | throw s!"bad posture {repr word}"
    let allowed ← if versions.isEmpty then pure #[]
      else (versions.splitOn ",").toArray.mapM readVersion
    let maxDeclarations ← if limit == "-" then pure none
      else match limit.toNat? with
        | some limit => pure (some limit)
        | none => throw s!"bad posture {repr word}"
    let builder := allowed.foldl (·.addAllowed ·) VersionPostureBuilder.new.clearAllowed
    return .script (builder.setMaxDeclarations maxDeclarations).build

/-- The feeds of a `drive` request, as those of `lex`. -/
def readFeeds (words : List String) : Except String (List (Option ByteArray)) :=
  words.mapM fun word =>
    if word == "e" then pure none
    else if word.startsWith "s" then some <$> unhex (word.drop 1).toString
    else throw s!"unknown feed {repr word}"

/-- The path given by its bytes. -/
def readPath (digits : String) : Except String System.FilePath := do
  match String.fromUTF8? (← unhex digits) with
  | some path => return path
  | none => throw s!"the path {digits} is not UTF-8"

/-- The reader of the session, failing the request if there is none. -/
def present : Option Session → IO Session
  | some session => pure session
  | none => failRequest "no reader: none was created"

/--
Answers a parser request, of the words of its line, writing its response. Returns the reader for
the next requests, which only `reader` replaces.

A request that cannot be answered fails with an I/O error, also one that fails while it runs;
the reader is then gone if the request had taken it.
-/
def answer (choice : LexerChoice) (remote : Remote) (session : Option Session)
    (words : List String) : IO (Option Session) := do
  match words with
  | ["reader", parser, version] =>
    let parser ← orFail (readParserChoice parser)
    let version ← orFail (readVersion version)
    let session ← newSession choice remote version parser
    remote.write "ready"
    return some session
  | ["slice", digits] =>
    let bytes ← orFail (unhex digits)
    match ← (← present session).readSlice bytes.toByteSlice with
    | .ok () => remote.write "ok"
    | .error err => remote.write (errorLine err)
  | ["eof"] =>
    match ← (← present session).readEof with
    | .ok (some result) =>
      remote.write s!"done {result.value} {location result.location}"
    | .ok none => remote.write "none"
    | .error err => remote.write (errorLine err)
  | ["all"] =>
    let reader ← present session
    let (result, buf) ← reader.readAll (← RemoteBuf.new remote)
    buf.report
    match result with
    | .ok (some result) =>
      remote.write s!"done {result.value} {location result.location}"
    | .ok none => remote.write "none"
    | .error err => remote.write (errorLine err)
  | ["file", digits] =>
    let path ← orFail (readPath digits)
    match ← (← present session).readFile path with
    | .ok (some result) =>
      remote.write s!"done {result.value} {location result.location}"
    | .ok none => remote.write "none"
    | .error err => remote.write (errorLine err)
  | ["discarded"] =>
    match ← (← present session).discardedFrom with
    | some place => remote.write s!"at {location place}"
    | none => remote.write "at -"
  | ["version"] =>
    remote.write s!"version {versionName (← (← present session).version)}"
  | ["read-smt"] =>
    let buf ← RemoteBuf.new remote
    let (result, buf) ← match choice with
      | .z => do
        let (result, buf) : Except (ReadFailure Remote (ScriptParser Remote)) Remote × RemoteBuf ←
          readSmt remote buf
        pure ((result.map fun _ => ()).mapError (·.error), buf)
      | _ => do
        let script ← newSession choice remote default (.script VersionPosture.default)
        let (result, buf) ← script.readAll buf
        pure (result.map fun _ => (), buf)
    buf.report
    match result with
    | .ok () => remote.write "ok"
    | .error err => remote.write (errorLine err)
  | ["read-smt-file", digits] =>
    let path ← orFail (readPath digits)
    let result ← match choice with
      | .z => do
        let result : Except (ReadFailure Remote (ScriptParser Remote)) Remote ←
          readSmtFile remote path
        pure ((result.map fun _ => ()).mapError (·.error))
      | _ => do
        let script ← newSession choice remote default (.script VersionPosture.default)
        pure ((← script.readFile path).map fun _ => ())
    match result with
    | .ok () => remote.write "ok"
    | .error err => remote.write (errorLine err)
  | "drive" :: name :: version :: count :: feeds =>
    let driven ← orFail (readDriven name)
    let version ← orFail (readVersion version)
    let some count := count.toNat?
      | failRequest s!"bad count {repr count}"
    let feeds ← orFail (readFeeds feeds)
    driven.with (fun parser render => runDrive choice remote version count feeds parser render)
  | _ => failRequest "malformed request"
  return session

end ParseRequests

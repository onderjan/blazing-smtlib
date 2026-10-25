/-
The writer requests of the driver protocol, see the section "The writer" of
`lean/driver-protocol.md`, answered by the writer of the Lean library and by `Token.writeSmt`
through their public interface.

The tokens are lexed by the library's lexer, whichever lexer answers the other requests: the
requests test the writer, not the lexer.
-/
module

public import BSmtLib
public import Protocol

public section

open BSmtLib
open BSmtLib.Token (AppendTokens BatchTag Consume ConsumeFrom Cursor TokensCursor)
open BSmtLib.Lexer.Cursor (LexerCursor)
open BSmtLib.Lexer.Error (LexerError)
open BSmtLib.Writer (WriteError WriteStyle WriterConfig)

namespace WriteRequests

/- The loop over a cursor's tokens ends as each step consumes a token: it descends by the
producer's consumption, which is well-founded. -/
local instance {batch : BatchTag} : WellFoundedRelation (LexerCursor batch) :=
  ⟨Cursor.Consumed, Cursor.consumed_wf⟩

/-- The message of the failure of the writer under a request with `fail`. -/
def WRITER_FAILURE : String := "the test writer fails every write"

/-- What a request hands to the writer, by its items. -/
inductive Item where
  /-- The bytes, lexed as one whole input into the writer. -/
  | lex (bytes : ByteArray)
  /-- One write of the tokens. -/
  | write (tokens : Array Token)
  /-- One consumption of a tokens cursor that holds the tokens. -/
  | consume (tokens : Array Token)
  /-- The version to write the following tokens in. -/
  | version (version : Version)

/-- A request, read from its line. -/
structure Request where
  version : Version
  /-- The style of the writer, or `none` for each token written by itself. -/
  style : Option WriteStyle
  fails : Bool
  items : Array Item

/-- The reserved word of the spelling, in whichever version reserves it. -/
def readReserved (spelling : String) : Except String Token.Reserved :=
  let found := [Version.v2_7, .v2_6, .v2_5, .v2_0].findSome? fun version =>
    Token.Reserved.fromBytes? spelling.toUTF8.toByteSlice version
  match found with
  | some reserved => pure reserved
  | none => throw s!"unknown reserved word {repr spelling}"

/-- The token of the word. -/
def readToken (word : String) : Except String Token := do
  let bad := s!"bad token {repr word}"
  let view {α : Type} (made : Except Lexicon.Value.DisallowedBytesError α) : Except String α :=
    made.mapError fun _ => bad
  match word with
  | "(" => return .parenOpen
  | ")" => return .parenClose
  | "e" => return .endOfFile
  | _ =>
    if word.isEmpty then
      throw bad
    let letter := (word.take 1).toString
    let rest := (word.drop 1).toString
    if letter == "r" then
      return .reserved (← readReserved rest)
    let bytes := (← unhex rest).toByteSlice
    match letter with
    | "N" => return .numeral (← view (Lexicon.Value.Numeral.new bytes))
    | "D" => return .decimal (← view (Lexicon.Value.Decimal.new bytes))
    | "X" => return .hexadecimal (← view (Lexicon.Value.HexDigits.new bytes))
    | "B" => return .binary (← view (Lexicon.Value.BinDigits.new bytes))
    | "S" => return .string (← view (Lexicon.Value.StringContent.new bytes))
    | "k" => return .keyword (← view (Lexicon.Value.Keyword.new bytes))
    | "u" => return .symbol (← view (Lexicon.Value.Symbol.newUnquoted bytes))
    | "q" => return .symbol (← view (Lexicon.Value.Symbol.newQuoted bytes))
    | "w" => return .whitespace (← view (Lexicon.Value.Whitespace.new bytes))
    | "c" => return .comment (← view (Lexicon.Value.Comment.new bytes))
    | _ => throw bad

/-- The tokens of the operand of an item, separated by commas. -/
def readTokens (operand : String) : Except String (Array Token) :=
  if operand.isEmpty then pure #[]
  else (operand.splitOn ",").toArray.mapM readToken

def readItem (word : String) : Except String Item := do
  let (name, operand) ← match word.splitOn ":" with
    | name :: operand@(_ :: _) => pure (name, ":".intercalate operand)
    | _ => throw s!"unknown item {repr word}"
  match name with
  | "lex" => return .lex (← unhex operand)
  | "write" => return .write (← readTokens operand)
  | "consume" => return .consume (← readTokens operand)
  | "version" => return .version (← readVersion operand)
  | _ => throw s!"unknown item {repr word}"

def readRequest (line : String) : Except String Request := do
  let words := line.splitOn " "
  if words.head? != some "write" then
    throw "unknown request"
  let some version := words[1]?
    | throw "no version"
  let version ← readVersion version
  let some style := words[2]?
    | throw "no style"
  let style : Option WriteStyle ← match style with
    | "-" => pure none
    | "line" => pure (some .line)
    | "compact" => pure (some .compact)
    | "layout" => pure (some .layout)
    | other => throw s!"unknown style {repr other}"
  let mut request : Request := { version, style, fails := false, items := #[] }
  for word in words.drop 3 do
    if word == "fail" && request.items.isEmpty && !request.fails then
      request := { request with fails := true }
      continue
    let item ← readItem word
    if let .consume tokens := item then
      if request.style.isNone then
        throw "consume needs a writer of a style"
      if tokens.isEmpty then
        throw "consume needs a token"
    request := { request with items := request.items.push item }
  return request

/-- The line of an error of writing. -/
def writeErrorLine (err : WriteError) : String :=
  match err.cause with
  | .io error => s!"werr io x{hex (toString error).toUTF8.toByteSlice}"
  | .notInVersion reserved => s!"werr not-in-version {reserved.asStr}"

/-- The line of the outcome of lexing a whole input into a consumer that fails with errors of
writing. -/
def lexLine {H : Type} (result : Except (LexerError WriteError × H) α) : String :=
  match result with
  | .ok _ => "ok"
  | .error (err, _) =>
    match err.cause with
    | .lexical kind =>
      s!"err {errorKindName kind} {location err.span.start} {location err.span.end}"
    | .consumer err => writeErrorLine err

/- LEAN: the Rust consumer borrows the sink; a stream is a handle to it here, so the consumer holds
the stream. -/
/-- A consumer that takes every token, whitespace and comments included, and writes each by itself
in the version of the cursor. -/
structure WriteBack where
  stream : IO.FS.Stream

instance : Consume WriteBack Unit WriteError where
  isConcrete := true

/-- Writes the tokens of the cursor, which has one, each by itself, until none is left, one ends
the input or writing one fails. -/
def writeBack {batch : BatchTag} (stream : IO.FS.Stream) (cursor : LexerCursor batch)
    (h : cursor.HasNext) :
    IO (Except WriteError (ControlFlow Unit) × { c : LexerCursor batch // c.Consumed cursor }) := do
  let (token, ⟨next, consumed⟩) := cursor.next h
  let token := Cursor.syntax cursor token
  match ← token.writeSmt (n := IO) stream cursor.version with
  | .error err => return (.error err, ⟨next, consumed⟩)
  | .ok () =>
    if token matches .endOfFile then
      return (.ok (.break ()), ⟨next, consumed⟩)
    if h : next.HasNext then
      let (result, ⟨last, taken⟩) ← writeBack stream next h
      return (result, ⟨last, taken.trans consumed⟩)
    else
      return (.ok .continue, ⟨next, consumed⟩)
termination_by cursor
decreasing_by exact consumed

instance {batch : BatchTag} : ConsumeFrom WriteBack (LexerCursor batch) IO where
  consume cursor h := do
    let state : WriteBack ← get
    writeBack state.stream cursor h

/-- Writes the tokens each by itself in the version, until writing one fails. -/
def writeAlone (stream : IO.FS.Stream) (version : Version) (tokens : Array Token) :
    IO (Except WriteError Unit) := do
  for token in tokens do
    if let .error err ← token.writeSmt (n := IO) stream version then
      return .error err
  return .ok ()

/-- Answers the items with each token written by itself, giving the lines. -/
def answerAlone (request : Request) (stream : IO.FS.Stream) : ExceptT String IO String := do
  let mut version := request.version
  let mut out := ""
  for item in request.items do
    let mut line := "ok"
    match item with
    | .lex bytes =>
      line := lexLine (← (Lexer.new ({ stream } : WriteBack) version).lexAll bytes.toByteSlice)
    | .write tokens =>
      if let .error err ← writeAlone stream version tokens then
        line := writeErrorLine err
    | .consume _ => throw "consume needs a writer of a style"
    | .version next => version := next
    out := out ++ line ++ "\n"
  return out

/-- Answers the items with a writer of the style, giving the lines. -/
def answerStyled (request : Request) (style : WriteStyle) (stream : IO.FS.Stream) :
    ExceptT String IO String := do
  let mut writer := Writer.new stream ((WriterConfig.new request.version).withStyle style)
  let mut out := ""
  for item in request.items do
    let mut line := "ok"
    match item with
    | .lex bytes =>
      let result ← (Lexer.new writer writer.version).lexAll bytes.toByteSlice
      -- the writer as the lexer left it, whether lexing succeeded or failed
      writer := match result with
        | .ok (_, lexer) => lexer.consumer
        | .error (_, consumer) => consumer
      line := lexLine result
    | .write tokens =>
      let (result, next) ← writer.write (n := IO) tokens
      writer := next
      if let .error err := result then
        line := writeErrorLine err
    | .consume tokens =>
      let cursor := tokens.foldl TokensCursor.push (TokensCursor.new writer.version)
      let .isTrue h := Cursor.decideHasNext cursor
        | throw "consume needs a token"
      let consumed : IO _ := (ConsumeFrom.consume (H := Writer) cursor h).run writer
      let ((result, ⟨left, _⟩), next) ← consumed
      writer := next
      -- the tokens the writer did not take
      let left := TokensCursor.Internal.remaining left
      line := match result with
        | .ok (.break ()) => s!"break {left}"
        | .ok .continue => s!"continue {left}"
        | .error err => writeErrorLine err
    | .version version => writer := writer.setVersion version
    out := out ++ line ++ "\n"
  return out

/-- Answers one request line, giving the response lines. -/
def answer (line : String) : ExceptT String IO String := do
  -- decode the whole request first, so that a malformed one produces no lines
  let request ← readRequest line
  let buffer ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let kept := IO.FS.Stream.ofBuffer buffer
  let stream : IO.FS.Stream := if request.fails then
      { kept with
        write := fun _ => throw (IO.userError WRITER_FAILURE)
        flush := throw (IO.userError WRITER_FAILURE) }
    else kept
  let out ← match request.style with
    | none => answerAlone request stream
    | some style => answerStyled request style stream
  let bytes := (← buffer.get).data
  return out ++ s!"out x{hex bytes.toByteSlice}\n"

end WriteRequests

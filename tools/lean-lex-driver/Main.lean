/-
The lexer driver protocol, answered by the Lean lexer, see `lean/driver-protocol.md`.
The Rust tests run their lexer inputs through it to check the Lean port.

Reads one request per line from the standard input and writes the response
to the standard output, until the input ends.
-/
import BSmtLib

open BSmtLib


/- LEAN: the Rust driver collects the lines in a `RefCell<String>` shared with the handler;
`IO.Ref` is Lean's counterpart, so the handler runs in `IO`. -/
/-- Writes every token handed over as a response line. -/
structure Report where
  version : Version
  out : IO.Ref String

def location (location : Location) : String :=
  s!"{location.offset}:{location.line}:{location.column}"

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hex (bytes : ByteSlice) : String := Id.run do
  let mut out := ""
  for i in [0:bytes.size] do
    let byte := (bytes.get! i).toNat
    out := (out.push (hexDigit (byte / 16))).push (hexDigit (byte % 16))
  out

/-- The token type, spelled as the Rust variant. -/
def tokenTypeName : TokenCategory → String
  | .parenOpen => "ParenOpen"
  | .parenClose => "ParenClose"
  | .numeral => "Numeral"
  | .decimal => "Decimal"
  | .hexadecimal => "Hexadecimal"
  | .binary => "Binary"
  | .string => "String"
  | .keyword => "Keyword"
  | .unquotedSymbol => "UnquotedSymbol"
  | .quotedSymbol => "QuotedSymbol"
  | .endOfFile => "EndOfFile"

/-- The lexer error kind, spelled as the Rust variant. -/
def errorKindName : LexicalErrorKind → String
  | .unexpectedCharacter => "UnexpectedCharacter"
  | .fractionDigitExpected => "FractionDigitExpected"
  | .hexadecimalDigitExpected => "HexadecimalDigitExpected"
  | .binaryDigitExpected => "BinaryDigitExpected"
  | .baseSelectionExpected => "BaseSelectionExpected"
  | .unclosedStringLiteral => "UnclosedStringLiteral"
  | .forbiddenCharInString => "ForbiddenCharInString"
  | .forbiddenKeywordName => "ForbiddenKeywordName"
  | .backslashInQuotedSymbol => "BackslashInQuotedSymbol"
  | .forbiddenCharInQuotedSymbol => "ForbiddenCharInQuotedSymbol"
  | .unclosedQuotedSymbol => "UnclosedQuotedSymbol"
  | .numeralLeadingZero => "NumeralLeadingZero"
  | .missingDelimiter => "MissingDelimiter"

/-- What the token is as a reserved word under the version. -/
def reservedName (ty : TokenCategory) (content : ByteSlice) (version : Version) : String :=
  -- only unquoted symbols can be reserved words
  if ty != .unquotedSymbol then
    "-"
  else
    match Reserved.fromBytes? content version with
    | some (.general _) => "general"
    | some (.commandName _) => "command"
    | none => "-"

/- LEAN: `partial`, as Lean is not shown that taking tokens from the cursor ends. -/
/-- Writes a line for every token remaining in the cursor. -/
partial def reportTokens (report : Report) : ConsumeM Report IO Empty Unit := do
  let some token ← modifyGetThe BatchCursor BatchCursor.next
    | return
  let cursor ← getThe BatchCursor
  let ty := cursor.category token
  let content := cursor.content token
  let span := cursor.span token
  let line := s!"t {tokenTypeName ty} {location span.start} {location span.end} \
    {reservedName ty content report.version} x{hex content}\n"
  report.out.modify (· ++ line)
  reportTokens report

/- LEAN: `Empty` is Lean's `Infallible`, a type without values. -/
instance : Consume Report IO Unit Empty where
  consume := do
    reportTokens (← getThe Report)
    return .continue

/-- Decodes the hexadecimal digits of a slice operand. -/
def unhex (digits : String) : Except String ByteArray := do
  let chars := digits.toList.toArray
  if chars.size % 2 != 0 then
    throw s!"odd number of hexadecimal digits in {repr digits}"
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else throw s!"bad hexadecimal digits in {repr digits}"
  let mut bytes := ByteArray.emptyWithCapacity (chars.size / 2)
  for i in [0:chars.size / 2] do
    let high ← digit chars[2 * i]!
    let low ← digit chars[2 * i + 1]!
    bytes := bytes.push (high * 16 + low).toUInt8
  return bytes

/-- What the consumer of a request does with one hand-over, by its plan. -/
inductive Reply where
  /-- Take every token and continue. -/
  | takeAll
  /-- Take this many tokens and continue: the rest is handed over again. -/
  | leave (count : Nat)
  /-- Take this many tokens and finish. -/
  | finish (count : Nat)
  /-- Take this many tokens and fail. -/
  | fail (count : Nat)
  /-- Take this many tokens, set the version and continue. -/
  | switch (count : Nat) (version : Version)
  /-- Take this many tokens, set the version and finish. -/
  | switchAndFinish (count : Nat) (version : Version)
  deriving BEq

/-- How the consumer of a request behaves. -/
inductive Behaviour where
  /-- It takes every token and always continues. -/
  | takeAll
  /-- It answers the hand-overs in order by the replies, and takes every
  token once they have run out. -/
  | plan (replies : Array Reply)
  /-- It takes every token and fails by what the tokens are: on the symbol
  `bad`, on a closing parenthesis that closes nothing, and on the
  end-of-file token inside a parenthesis, or on every end-of-file token
  if `refuseEnd` is set. The symbol `to-2.0` makes it set the version. -/
  | rules (refuseEnd : Bool)
  deriving BEq

/-- A request, read from its line. A feed is a slice, or `none` for the end of the input. -/
structure Request where
  version : Version
  whitespace : Bool
  recover : Bool
  behaviour : Behaviour
  feeds : Array (Option ByteArray)

def readVersion (word : String) : Except String Version :=
  match Version.fromDecimal? word.toUTF8.toByteSlice with
  | some version => pure version
  | none => throw s!"unknown version {repr word}"

def readReply (word : String) : Except String Reply := do
  let bad := s!"unknown reply {repr word}"
  if word == "t" then
    return .takeAll
  if word.isEmpty then
    throw bad
  let letter := (word.take 1).toString
  let rest := (word.drop 1).toString
  -- the version follows the first colon, if there is one
  let (count, version) ← match rest.splitOn ":" with
    | [count] => pure (count, none)
    | count :: version => pure (count, some (← readVersion (":".intercalate version)))
    | [] => throw bad
  let some count := count.toNat?
    | throw bad
  if count == 0 then
    throw s!"a reply must take a token: {repr word}"
  match letter, version with
  | "l", none => return .leave count
  | "f", none => return .finish count
  | "x", none => return .fail count
  | "v", some version => return .switch count version
  | "w", some version => return .switchAndFinish count version
  | _, _ => throw bad

def readRequest (line : String) : Except String Request := do
  let words := line.splitOn " "
  if words.head? != some "lex" then
    throw "unknown request"
  let some version := words[1]?
    | throw "no version"
  let mut request : Request := {
    version := ← readVersion version
    whitespace := false
    recover := false
    behaviour := .takeAll
    feeds := #[] }
  for word in words.drop 2 do
    let scripted := request.behaviour != .takeAll
    -- the options come before the feeds
    let option := request.feeds.isEmpty
    if word == "e" then
      request := { request with feeds := request.feeds.push none }
    else if word == "ws" && option then
      request := { request with whitespace := true }
    else if word == "recover" && option then
      request := { request with recover := true }
    else if word == "rules" && option && !scripted then
      request := { request with behaviour := .rules false }
    else if word == "rules=refuse-end" && option && !scripted then
      request := { request with behaviour := .rules true }
    else if word.startsWith "plan=" && option && !scripted then
      let replies := (word.drop 5).toString
      -- no replies at all are a plan too: every token is taken,
      -- and the hand-overs are reported
      let replies ← if replies.isEmpty then pure #[]
        else (replies.splitOn ",").toArray.mapM readReply
      request := { request with behaviour := .plan replies }
    else if word.startsWith "s" then
      request := { request with feeds := request.feeds.push (some (← unhex (word.drop 1).toString)) }
    else
      throw s!"unknown operation {repr word}"
  return request

/-- Answers one request line, giving the response lines. -/
def answer (line : String) : ExceptT String IO String := do
  -- decode the whole request first, so that a malformed one produces no lines
  let request ← readRequest line
  -- the options that the Lean lexer cannot answer yet
  if request.whitespace then
    throw "the option ws is not implemented yet"
  if request.recover then
    throw "the option recover is not implemented yet"
  match request.behaviour with
  | .takeAll => pure ()
  | .plan _ => throw "the option plan is not implemented yet"
  | .rules _ => throw "the option rules is not implemented yet"
  let version := request.version
  let operations := request.feeds

  let lines ← IO.mkRef ""
  let mut lexer := Lexer.new { version, out := lines : Report } version
  let mut error : Option LexicalError := none
  for operation in operations do
    let (result, next) ← match operation with
      | some slice => lexer.lexSlice slice.toByteSlice
      | none => lexer.lexEof
    lexer := next
    match result with
    -- the location the lexer is at after the operation
    | .ok _ => lines.modify (· ++ s!"at {location lexer.currentLocation}\n")
    | .error (.lexer err) =>
      error := some err
      break
    | .error (.handler never) => nomatch never
    -- the protocol has no line for an internal error, which must not occur
    | .error (.internal err) => throw s!"internal error: {err.message}"

  let mut out ← lines.get
  match error with
  | none => out := out ++ "ok\n"
  | some err =>
    out := out ++ s!"err {errorKindName err.kind} {location err.span.start} {location err.span.end}\n"
  return out

partial def serve (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  -- the input has ended
  if line.isEmpty then
    return
  let request := (line.dropEndWhile (· == '\n')).toString
  let request := (request.dropEndWhile (· == '\r')).toString
  let out ← match ← (answer request).run with
    | .ok out => pure out
    | .error message => pure s!"fail {message}\n"
  stdout.putStr out
  stdout.flush
  serve stdin stdout

def main : IO Unit := do
  serve (← IO.getStdin) (← IO.getStdout)

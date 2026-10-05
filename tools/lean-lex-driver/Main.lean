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
  version : SmtVersion
  out : IO.Ref String

def location (location : SmtLocation) : String :=
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
def tokenTypeName : TokenType → String
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
def errorKindName : LexerErrorKind → String
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
def reservedName (ty : TokenType) (content : ByteSlice) (version : SmtVersion) : String :=
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
partial def reportTokens (report : Report) : TokenHandlerM Report IO Empty Unit := do
  let some token ← modifyGetThe TokenCursor TokenCursor.next
    | return
  let cursor ← getThe TokenCursor
  let ty := cursor.ty token
  let content := cursor.content token
  let span := cursor.span token
  let line := s!"t {tokenTypeName ty} {location span.start} {location span.end} \
    {reservedName ty content report.version} x{hex content}\n"
  report.out.modify (· ++ line)
  reportTokens report

/- LEAN: `Empty` is Lean's `Infallible`, a type without values. -/
instance : TokenHandler Report IO Unit Empty where
  handleTokens := do
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

/-- Answers one request line, giving the response lines. -/
def answer (request : String) : ExceptT String IO String := do
  let words := request.splitOn " "
  let (kind, words) := (words.headD "", words.drop 1)
  if kind != "lex" then
    throw "unknown request"
  let some version := (words.head?).bind fun version =>
      SmtVersion.fromDecimal? version.toUTF8.toByteSlice
    | throw "unknown version"

  -- decode every operation first, so that a malformed request produces
  -- no token lines
  let mut operations : Array (Option ByteArray) := #[]
  for word in words.drop 1 do
    if word.startsWith "s" then
      match unhex (word.drop 1).toString with
      | .ok bytes => operations := operations.push (some bytes)
      | .error message => throw message
    else if word == "e" then
      operations := operations.push none
    else
      throw s!"unknown operation {repr word}"

  let lines ← IO.mkRef ""
  let mut lexer := Lexer.new { version, out := lines : Report } version
  let mut error : Option LexerError := none
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

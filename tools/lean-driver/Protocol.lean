/-
The fields of the driver protocol that the lexer and the parser requests share, see
`lean/driver-protocol.md`: bytes in hexadecimal, locations, versions and the names of token types
and lexer errors; and the lexer that answers the requests.
-/
module

public import BSmtLib

public section

open BSmtLib
open BSmtLib.Token (Version TokenCategory)
open BSmtLib.Lexer (LexicalErrorKind)

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

def versionName : Version → String
  | .v2_0 => "2.0"
  | .v2_5 => "2.5"
  | .v2_6 => "2.6"
  | .v2_7 => "2.7"

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
  | .whitespace => "Whitespace"
  | .comment => "Comment"
  | .endOfFile => "EndOfFile"

/-- The lexer error kind, spelled as the Rust `Debug` form of the kind. -/
def errorKindName : LexicalErrorKind → String
  | .unexpectedCharacter => "UnexpectedByte"
  | .expected .fractionDigit => "Expected(FractionDigit)"
  | .expected .hexadecimalDigit => "Expected(HexadecimalDigit)"
  | .expected .binaryDigit => "Expected(BinaryDigit)"
  | .expected .base => "Expected(Base)"
  | .unclosedStringLiteral => "UnclosedString"
  | .forbiddenCharInString => "ForbiddenByteInString"
  | .emptyKeyword => "EmptyKeyword"
  | .backslashInQuotedSymbol => "BackslashInQuotedSymbol"
  | .forbiddenCharInQuotedSymbol => "ForbiddenByteInQuotedSymbol"
  | .unclosedQuotedSymbol => "UnclosedQuotedSymbol"
  | .numeralLeadingZero => "NumeralLeadingZero"
  | .missingDelimiter => "MissingDelimiter"
  | .unexpectedTrailingToken => "UnexpectedTrailingToken"

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

def readVersion (word : String) : Except String Version :=
  match Version.fromDecimal? word.toUTF8.toByteSlice with
  | some version => pure version
  | none => throw s!"unknown version {repr word}"

/-- The lexer that answers the requests. -/
inductive LexerChoice where
  /-- The naive lexer, `BSmtLib.Lexer.Internal.VNaive`. -/
  | v
  /-- The Rust lexer ported to Lean, `BSmtLib.Lexer.Internal.WRustPort`. -/
  | w
  /-- The lexer with the batch kept in its state, `BSmtLib.Lexer.Internal.X1BatchInCore`. -/
  | x1
  /-- The library's lexer, `BSmtLib.Lexer`. -/
  | z

/-- The lexer named by the value of `BLAZING_SMTLIB_LEAN_LEXER`, the library's if it is unset. -/
def readLexerChoice : Option String → Except String LexerChoice
  | none | some "z" => pure .z
  | some "v" => pure .v
  | some "w" => pure .w
  | some "x1" => pure .x1
  | some other => throw s!"unknown lexer {repr other} in BLAZING_SMTLIB_LEAN_LEXER, \
      expected v, w, x1 or z"

/-- A line read from a stream, without its line end. -/
def lineContent (line : String) : String :=
  let line := (line.dropEndWhile (· == '\n')).toString
  (line.dropEndWhile (· == '\r')).toString

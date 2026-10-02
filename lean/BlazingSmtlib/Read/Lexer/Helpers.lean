import BlazingSmtlib.Read.Lexer.CharClass
import BlazingSmtlib.Read.Lexer.Error
import BlazingSmtlib.Token

namespace BlazingSmtlib.Read.Lexer

open BlazingSmtlib.Token

/-- What a byte does in the normal state. -/
inductive Start where
  | whitespace
  | lineFeed
  | parenOpen
  | parenClose
  | comment
  | hash
  | quote
  | colon
  | pipe
  | digit
  | symbol
  | other
  deriving BEq, Inhabited

namespace Start

def classify (c : UInt8) : Start :=
  let flags := CharClass.runFlags c
  if c == byte ' ' || c == byte '\t' || c == byte '\r' then .whitespace
  else if c == byte '\n' then .lineFeed
  else if c == byte '(' then .parenOpen
  else if c == byte ')' then .parenClose
  else if c == byte ';' then .comment
  else if c == byte '#' then .hash
  else if c == byte '"' then .quote
  else if c == byte ':' then .colon
  else if c == byte '|' then .pipe
  else if flags &&& RUN_DIGIT != 0 then .digit
  else if flags &&& RUN_SIMPLE_SYMBOL != 0 then .symbol
  else .other

end Start

/-- Normal-state dispatch table. -/
def START : Array Start :=
  (Array.range 256).map fun i => Start.classify i.toUInt8

/- LEAN: Rust tests the `FAST_DELIM` bit of the fast-path table; the fast path is not ported
yet, so the delimiters are tested directly. -/
/--
Whether the byte delimits a token: whitespace, a parenthesis, or the start
of a comment. Every token must be followed by such a byte or by the end
of the input.
-/
@[inline]
def isDelimiter (c : UInt8) : Bool :=
  c == byte ' ' || c == byte '\t' || c == byte '\n' || c == byte '\r'
    || c == byte '(' || c == byte ')' || c == byte ';'

/- LEAN: declared in `lexer.rs` in Rust, where `helpers.rs` uses it in turn. Lean modules
cannot import each other, so it is declared here, before `DigitRun` needs it. -/
/-- The states of the lexer, see the lexer for their meaning. -/
inductive LexerState where
  | normal
  | numeralOrDecimal
  | fraction
  | baseSelection
  | hexadecimal
  | binary
  | stringLiteral
  | stringLiteralDoubleQuote
  | stringLiteralBackslashEscape
  | simpleSymbol
  | quotedSymbol
  | keyword
  | comment
  | quotedSymbolClosed
  | failed
  deriving BEq, Inhabited

structure DigitRun where
  flag : UInt8
  state : LexerState
  tokenType : TokenType
  emptyError : LexerErrorKind

def HEXADECIMAL_RUN : DigitRun :=
  { flag := RUN_HEX_DIGIT, state := .hexadecimal, tokenType := .hexadecimal,
    emptyError := .hexadecimalDigitExpected }

def BINARY_RUN : DigitRun :=
  { flag := RUN_BINARY_DIGIT, state := .binary, tokenType := .binary,
    emptyError := .binaryDigitExpected }

/-- Where a token ended. -/
structure TokenEnd where
  /-- The position after `Lexer.offset` where the token ended. -/
  position : Nat
  /-- Whether the token end was detected at a byte that is not a part of the token. -/
  atByte : Bool

namespace TokenEnd

def EOF : TokenEnd := { position := 0, atByte := false }

/- LEAN: `at_byte` in Rust; the name clashes with the field `atByte` in Lean. -/
@[inline]
def mkAtByte (position : Nat) : TokenEnd := { position, atByte := true }

end TokenEnd

/--
The content of the token being lexed, accumulated across slices.

A byte array cannot be shortened in place, so the buffer keeps its bytes
and the length of the content in use: clearing it only resets the length,
and the bytes after it are overwritten as the content grows again.
-/
/- LEAN: Rust keeps the content in a `String8` and clears it, keeping its allocation. Lean
cannot shorten a `ByteArray` in place, so the lexer keeps its own buffer with a length. -/
structure ContentBuffer where
  bytes : ByteArray
  len : Nat

namespace ContentBuffer

def empty : ContentBuffer := { bytes := ByteArray.empty, len := 0 }

@[inline]
def clear (self : ContentBuffer) : ContentBuffer :=
  { self with len := 0 }

@[inline]
def isEmpty (self : ContentBuffer) : Bool :=
  self.len == 0

/-- The content as a view of the buffer. -/
@[inline]
def view (self : ContentBuffer) : ByteSlice :=
  self.bytes.toByteSlice 0 self.len

@[inline]
def extendFromSlice (self : ContentBuffer) (slice : ByteSlice) : ContentBuffer :=
  { bytes := slice.byteArray.copySlice slice.start self.bytes self.len slice.size false,
    len := self.len + slice.size }

@[inline]
def push (self : ContentBuffer) (byte : UInt8) : ContentBuffer :=
  if self.len < self.bytes.size then
    { bytes := self.bytes.set! self.len byte, len := self.len + 1 }
  else
    { bytes := self.bytes.push byte, len := self.len + 1 }

end ContentBuffer

/-- Where the bytes of a finished token are. -/
inductive Content where
  /-- Accumulated in the lexer's token content. -/
  | stored
  /-- Still in the input slice. -/
  | borrowed (bytes : ByteSlice)

namespace Content

@[inline]
def bytes (self : Content) (stored : ContentBuffer) : ByteSlice :=
  match self with
  | .stored => stored.view
  | .borrowed bytes => bytes

end Content

end BlazingSmtlib.Read.Lexer

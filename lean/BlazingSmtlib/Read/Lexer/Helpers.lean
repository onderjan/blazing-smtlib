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

/-- Bits not used by fast masks, kept so that `FAST_MASKS` partition the byte. -/
def FAST_RESERVED : UInt8 := 0b0000_0010

/--
Set if the byte delimits a token: whitespace, a parenthesis, or the start
of a comment. Every token must be followed by such a byte or by the end
of the input.
-/
def FAST_DELIM : UInt8 := 0b0000_0001

/-- Determines whether the fast path should be taken. -/
def FAST_ON : UInt8 := 0b0000_0100

/--
Determines whether a token should be emitted in the fast path.

Is unset for whitespace.
-/
def FAST_EMIT : UInt8 := 0b0000_1000

/-- Determines the run mask that should be used. -/
def FAST_RUN_MASK : UInt8 := 0b0111_0000

/--
Set if this is a quoted symbol ending with a pipe.

The pipe requires special behaviour: the token extends
from the opening pipe to the closing pipe including them,
but its content excludes the pipes.
-/
def FAST_PIPE : UInt8 := 0b1000_0000

/-- Masks for the fast flags. -/
def FAST_MASKS : Array UInt8 :=
  #[FAST_RESERVED, FAST_DELIM, FAST_ON, FAST_EMIT, FAST_RUN_MASK, FAST_PIPE]

/- LEAN: the `#guard` checks below run when the module is built, as the Rust `assert!`s in
`const` blocks do. -/
-- fast masks partition u8 and are pairwise distinct
#guard (FAST_MASKS.foldl (init := some (0 : UInt8)) fun union mask =>
    union.bind fun union => if union &&& mask == 0 then some (union ||| mask) else none)
  == some 0xFF

-- fast run flags contain exactly the three run flags we need
#guard (RUN_SIMPLE_SYMBOL ||| RUN_NON_LF_WHITESPACE ||| RUN_QUOTED_PLAIN) &&& FAST_RUN_MASK
    == FAST_RUN_MASK
  && (RUN_STRING_PLAIN ||| RUN_DIGIT ||| RUN_HEX_DIGIT ||| RUN_BINARY_DIGIT ||| RUN_COMMENT_PLAIN)
    &&& FAST_RUN_MASK == 0

/--
Fast dispatch bitmasks for every input byte.

The bitmasks carry the masks present in `FAST_MASKS`.
-/
def FAST : ByteArray :=
  ⟨(Array.range 256).map fun i =>
    let c := i.toUInt8
    let flags := CharClass.runFlags c
    if c == byte ' ' || c == byte '\t' || c == byte '\r' then
      FAST_ON ||| FAST_DELIM ||| RUN_NON_LF_WHITESPACE
    else if c == byte '\n' || c == byte '(' || c == byte ')' || c == byte ';' then
      FAST_DELIM
    else if c == byte '|' then
      FAST_ON ||| FAST_EMIT ||| FAST_PIPE ||| RUN_QUOTED_PLAIN
    -- a simple symbol may contain digits but must not start with one
    else if flags &&& RUN_SIMPLE_SYMBOL != 0 && flags &&& RUN_DIGIT == 0 then
      FAST_ON ||| FAST_EMIT ||| RUN_SIMPLE_SYMBOL
    else
      0⟩

/-- The fast flags of the byte. -/
@[inline]
def fastFlags (c : UInt8) : UInt8 :=
  FAST.get! c.toNat

-- a byte carries the delimiter flag exactly when it is whitespace, a parenthesis, or a semicolon
#guard (List.range 256).all fun i =>
  let c := i.toUInt8
  (fastFlags c &&& FAST_DELIM != 0)
    == (c == byte ' ' || c == byte '\t' || c == byte '\n' || c == byte '\r'
      || c == byte '(' || c == byte ')' || c == byte ';')

-- a byte is fast exactly when its START class is one the fast path replaces; parentheses
-- are dispatched by byte tests ahead of the table, so they are neither fast nor covered here
#guard (List.range 256).all fun i =>
  let start := START[i]!
  (fastFlags i.toUInt8 &&& FAST_ON != 0)
    == (start == .whitespace || start == .pipe || start == .symbol)

/--
Whether the byte delimits a token: whitespace, a parenthesis, or the start
of a comment. Every token must be followed by such a byte or by the end
of the input.
-/
@[inline]
def isDelimiter (c : UInt8) : Bool :=
  fastFlags c &&& FAST_DELIM != 0

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

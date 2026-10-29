module

public import BSmtLib.Lexer.Internal.CharClass
public import BSmtLib.Lexer.Error
public import BSmtLib.Token
import all Init.Data.Array.Basic
import all Init.Data.Nat.Bitwise.Basic

public section

open BSmtLib.Lexer.Error

namespace BSmtLib.Lexer.Internal.Helpers

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
  if c == byte! ' ' || c == byte! '\t' || c == byte! '\r' then .whitespace
  else if c == byte! '\n' then .lineFeed
  else if c == byte! '(' then .parenOpen
  else if c == byte! ')' then .parenClose
  else if c == byte! ';' then .comment
  else if c == byte! '#' then .hash
  else if c == byte! '"' then .quote
  else if c == byte! ':' then .colon
  else if c == byte! '|' then .pipe
  else if flags &&& CharClass.RUN_DIGIT != 0 then .digit
  else if flags &&& CharClass.RUN_SIMPLE_SYMBOL != 0 then .symbol
  else .other

end Start

/-- Normal-state dispatch table. -/
def START : Array Start :=
  (Array.range 256).map fun i => Start.classify i.toUInt8

/-- The dispatch table has an entry for every byte. -/
theorem size_START : START.size = 256 := by
  simp [START]

/-- What the byte does in the normal state. -/
@[inline]
def startOf (c : UInt8) : Start :=
  START[c.toNat]'(size_START ▸ c.toNat_lt)

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

/- LEAN: the Rust `assert!`s in `const` blocks that the fast masks partition the byte and
carry the three run flags are `#guard`s in `BSmtLib.Facts.Asserts`, checked when the facts are
built; so are the checks of the fast flags of every byte below. -/

/--
Fast dispatch bitmasks for every input byte.

The bitmasks carry the masks present in `FAST_MASKS`.
-/
def FAST : ByteArray :=
  ⟨(Array.range 256).map fun i =>
    let c := i.toUInt8
    let flags := CharClass.runFlags c
    if c == byte! ' ' || c == byte! '\t' || c == byte! '\r' then
      FAST_ON ||| FAST_DELIM ||| CharClass.RUN_NON_LF_WHITESPACE
    else if c == byte! '\n' || c == byte! '(' || c == byte! ')' || c == byte! ';' then
      FAST_DELIM
    else if c == byte! '|' then
      FAST_ON ||| FAST_EMIT ||| FAST_PIPE ||| CharClass.RUN_QUOTED_PLAIN
    -- a simple symbol may contain digits but must not start with one
    else if flags &&& CharClass.RUN_SIMPLE_SYMBOL != 0 && flags &&& CharClass.RUN_DIGIT == 0 then
      FAST_ON ||| FAST_EMIT ||| CharClass.RUN_SIMPLE_SYMBOL
    else
      0⟩

/-- The table of fast flags has an entry for every byte. -/
theorem size_FAST : FAST.size = 256 := by
  simp [FAST, ByteArray.size]

/-- The fast flags of the byte. -/
@[inline]
def fastFlags (c : UInt8) : UInt8 :=
  FAST[c.toNat]'(size_FAST ▸ c.toNat_lt)

/--
Whether the byte delimits a token: whitespace, a parenthesis, or the start
of a comment. Every token must be followed by such a byte or by the end
of the input.
-/
@[inline]
def isDelimiter (c : UInt8) : Bool :=
  fastFlags c &&& FAST_DELIM != 0

/- LEAN: the two facts below are checked by the kernel for every byte; the loops of the
lexer are shown to end by them. -/

/-- A byte that the fast path takes for whitespace continues a run of whitespace. -/
theorem not_endsRun_of_fastFlags {c : UInt8}
    (h : (fastFlags c &&& CharClass.RUN_NON_LF_WHITESPACE != 0) = true) :
    CharClass.endsRun c CharClass.RUN_NON_LF_WHITESPACE = false := by
  have table : ∀ n, n < 256 → (fastFlags n.toUInt8 &&& CharClass.RUN_NON_LF_WHITESPACE != 0) = true
      →
      CharClass.endsRun n.toUInt8 CharClass.RUN_NON_LF_WHITESPACE = false := by
    decide +kernel
  have := table c.toNat c.toNat_lt
  rw [show c.toNat.toUInt8 = c by simp] at this
  exact this h

/-- The only byte that the normal state takes for a line feed is the line feed. -/
theorem eq_of_startOf_eq_lineFeed {c : UInt8} (h : startOf c = .lineFeed) : c = byte! '\n' := by
  have table : ∀ n, n < 256 → (startOf n.toUInt8 == .lineFeed) = true →
      n.toUInt8 = byte! '\n' := by
    decide +kernel
  have := table c.toNat c.toNat_lt
  rw [show c.toNat.toUInt8 = c by simp] at this
  exact this (by rw [h]; rfl)

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
  | whitespace
  | quotedSymbolClosed
  deriving BEq, Inhabited

/-- The state of recovery in a lexer. -/
inductive RecoveryState where
  /--
  Nothing more: the end of the input raised the error, so only
  the end of the input can be lexed again.
  -/
  | «end»
  /--
  Nothing yet: recovery starts at a token boundary.

  If no parenthesis is open there, nothing is skipped at all.
  -/
  | boundary
  /-- Plain text outside of the strings, quoted symbols, and comments. -/
  | plain
  /-- Inside string literal. -/
  | string
  /-- At the byte after a backslash in a string literal (SMT-LIB 2.0 only). -/
  | stringEscape
  /-- Inside a quoted symbol. -/
  | quotedSymbol
  /-- Inside a comment. -/
  | comment
  deriving BEq, Inhabited

structure DigitRun where
  flag : UInt8
  state : LexerState
  tokenType : Token.TokenCategory
  emptyError : LexicalErrorKind

@[expose]
def HEXADECIMAL_RUN : DigitRun :=
  { flag := CharClass.RUN_HEX_DIGIT, state := .hexadecimal, tokenType := .hexadecimal,
    emptyError := (.expected .hexadecimalDigit) }

@[expose]
def BINARY_RUN : DigitRun :=
  { flag := CharClass.RUN_BINARY_DIGIT, state := .binary, tokenType := .binary,
    emptyError := (.expected .binaryDigit) }

/-- Where a token ended. -/
structure TokenEnd where
  /-- The position in the input where the token ended. -/
  position : USize
  /-- Whether the token end was detected at a byte that is not a part of the token. -/
  atByte : Bool

namespace TokenEnd

def EOF : TokenEnd := { position := 0, atByte := false }

/- LEAN: `at_byte` in Rust; the name clashes with the field `atByte` in Lean. -/
@[inline]
def mkAtByte (position : USize) : TokenEnd := { position, atByte := true }

end TokenEnd

/- LEAN: Rust keeps the content in a `BytesBuf` and clears it, keeping its allocation. Lean
cannot shorten a `ByteArray` in place, so the lexer keeps its own buffer with a length, and the
proof that the length is within the array, so that the content's bytes are read without a
bounds check. -/
/--
The content of the token being lexed, accumulated across slices.

A byte array cannot be shortened in place, so the buffer keeps its bytes
and the length of the content in use: clearing it only resets the length,
and the bytes after it are overwritten as the content grows again.
-/
structure ContentBuffer where
  bytes : ByteArray
  len : Nat
  fits : len ≤ bytes.size

namespace ContentBuffer

def empty : ContentBuffer := { bytes := ByteArray.empty, len := 0, fits := Nat.le_refl _ }

@[inline]
def clear (self : ContentBuffer) : ContentBuffer :=
  { self with len := 0, fits := Nat.zero_le _ }

@[inline]
def isEmpty (self : ContentBuffer) : Bool :=
  self.len == 0

/-- The content as a view of the buffer. -/
@[inline]
def view (self : ContentBuffer) : ByteSlice :=
  self.bytes.toByteSlice 0 self.len

/-- The number of bytes that `extendFrom` copies from `source`: those from `start` to `stop`
that are in it. -/
@[inline]
def copiedCount (source : ByteArray) (start stop : Nat) : Nat :=
  min (stop - start) (source.size - start)

/-- A copy of bytes into the array after the length keeps the length within the array. -/
theorem fits_copySlice {bytes : ByteArray} {len : Nat} (fits : len ≤ bytes.size)
    (source : ByteArray) (start stop : Nat) :
    len + copiedCount source start stop ≤
      (source.copySlice start bytes len (stop - start) false).size := by
  simp only [ByteArray.copySlice_eq_append, ByteArray.size_append, ByteArray.size_extract,
    copiedCount, ByteArray.size_data]
  omega

/- LEAN: the fields are taken out of `self` before the array is changed. Changing
`self.bytes` while `self` still refers to it would find the array shared and copy it. The
length grows by the bytes copied, which are all from `start` to `stop` when `stop` is within
`source`, as it is wherever the lexer extends the content. -/
/-- Appends the bytes of `source` from `start` to `stop`. -/
@[inline]
def extendFrom (self : ContentBuffer) (source : ByteArray) (start stop : Nat) : ContentBuffer :=
  let { bytes, len, fits } := self
  { bytes := source.copySlice start bytes len (stop - start) false,
    len := len + copiedCount source start stop,
    fits := fits_copySlice fits source start stop }

/-- A write of a byte within the array keeps its size. -/
theorem size_set_byte (bytes : ByteArray) (index : Nat) (value : UInt8) (h : index < bytes.size) :
    (bytes.set index value h).size = bytes.size := by
  cases bytes; simp [ByteArray.set, ByteArray.size]

@[inline]
def push (self : ContentBuffer) (byte : UInt8) : ContentBuffer :=
  let { bytes, len, fits } := self
  if h : len < bytes.size then
    { bytes := bytes.set len byte h, len := len + 1,
      fits := by rw [size_set_byte]; exact h }
  else
    { bytes := bytes.push byte, len := len + 1,
      fits := by rw [ByteArray.size_push]; exact Nat.succ_le_succ fits }

end ContentBuffer

/- LEAN: Rust borrows a sub-slice; here the content is the slice's array with the positions
in it, from which the token is built without allocating a view. The positions come with the
proof that they are in order and within the array, so that the content's bytes are read without
a bounds check. -/
/-- Where the bytes of a finished token are. -/
inductive Content where
  /-- Accumulated in the lexer's token content. -/
  | stored
  /-- Still in the input slice: its array from `start` to `stop`. -/
  | borrowed (bytes : ByteArray) (start stop : Nat) (ordered : start ≤ stop)
    (within : stop ≤ bytes.size)

namespace Content

/-- The bytes of the input from `start` to `stop`, which are in order and within the slice. -/
@[inline]
def borrow (input : CharClass.Input) (start stop : USize) (ordered : start.toNat ≤ stop.toNat)
    (within : stop.toNat ≤ input.stop.toNat) : Content :=
  .borrowed input.bytes start.toNat stop.toNat ordered (Nat.le_trans within input.stop_le)

/-- The number of bytes of the content. -/
@[inline]
def size (self : Content) (stored : ContentBuffer) : Nat :=
  match self with
  | .stored => stored.len
  | .borrowed _ start stop _ _ => stop - start

/-- The last byte of the content, if any. -/
@[inline]
def last? (self : Content) (stored : ContentBuffer) : Option UInt8 :=
  match self with
  | .stored =>
    if h : stored.len = 0 then none
    else some (stored.bytes[stored.len - 1]'(by have := stored.fits; omega))
  | .borrowed bytes start stop ordered within =>
    if h : stop = start then none else some (bytes[stop - 1]'(by omega))

end Content

end BSmtLib.Lexer.Internal.Helpers

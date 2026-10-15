module

public import BSmtLib.Bytes
public import BSmtLib.Lexer.Internal.CharClass

public section

namespace BSmtLib.Plain

open BSmtLib.Lexer.Internal (CharClass)

/- LEAN: `value.iter().all(f)` in Rust. `ByteSlice` has no `all`; its `foldr` reads the bytes
with their bounds proved, so no read can fail. -/
private def allBytes (value : ByteSlice) (f : UInt8 → Bool) : Bool :=
  value.foldr (fun c rest => f c && rest) true

/- LEAN: `u8::is_ascii_digit` in Rust. -/
private def isAsciiDigit (c : UInt8) : Bool :=
  byte! '0' ≤ c && c ≤ byte! '9'

/- LEAN: `u8::is_ascii_hexdigit` in Rust. -/
private def isAsciiHexDigit (c : UInt8) : Bool :=
  isAsciiDigit c || (byte! 'a' ≤ c && c ≤ byte! 'f') || (byte! 'A' ≤ c && c ≤ byte! 'F')

/- LEAN: the position of the first occurrence of the byte, which Rust finds by splitting the
slice. -/
private def findByte (value : ByteSlice) (byte : UInt8) : Option Nat :=
  let rec loop (i : Nat) : Option Nat :=
    if h : i < value.size then
      if value[i] == byte then some i else loop (i + 1)
    else
      none
  loop 0

/--
SMT-LIB string content.

May be empty.
Must contain only SMT-LIB printable or whitespace bytes.
-/
structure StringContentBuf where
  private ofBytes ::
  private bytes : Bytes.BytesBuf

namespace StringContentBuf

def isAllowed (value : ByteSlice) : Bool :=
  allBytes value fun c => (CharClass.classify c).isPrintableOrWhitespace

end StringContentBuf

/--
An owned SMT-LIB symbol, quoted or unquoted.

The symbol carries its bytes and whether it is quoted.

May be empty if quoted.
Must contain only SMT-LIB printable or whitespace bytes
except for pipe (|) and backslash (\), with an additional
restriction for unquoted symbols: they must contain
a nonempty sequence of simple-symbol bytes not starting
with a digit.

Equality and hash are intentionally not implemented:
quoted and unquoted symbols refer to the same value semantically,
so the value without the quoted flag should be compared in that case,
obtained through `SymbolBuf.bytes` or `SymbolBuf.intoBytesBuf`.
-/
structure SymbolBuf where
  private ofParts ::
  private quoted : Bool
  private value : Bytes.BytesBuf

/--
A view of an SMT-LIB symbol, quoted or unquoted.

The symbol carries its bytes and whether it is quoted.

May be empty if quoted.
Must contain only SMT-LIB printable or whitespace bytes
except for pipe (|) and backslash (\), with additional
restrictions for unquoted symbols.

Equality and hash are intentionally not implemented:
quoted and unquoted symbols refer to the same value semantically,
so the value without the quoted flag should be compared in that case,
obtained through `Symbol.bytes`.
-/
structure Symbol where
  private ofParts ::
  private quoted : Bool
  private slice : ByteSlice

namespace SymbolBuf

def isUnquotedAllowed (value : ByteSlice) : Bool :=
  if h : 0 < value.size then
    !isAsciiDigit value[0] && allBytes value fun c =>
      (CharClass.classify c).isAllowedInSimpleSymbol
  else
    false

def isQuotedAllowed (value : ByteSlice) : Bool :=
  allBytes value fun c =>
    (CharClass.classify c).isPrintableOrWhitespace && c != byte! '|' && c != byte! '\\'

end SymbolBuf

/--
SMT-LIB keyword.

Cannot be empty.
Must contain only SMT-LIB simple-symbol-class bytes.

A keyword may start with a digit and may spell a reserved word.
It is defined in version 2.0 as a colon followed by a non-empty sequence
of simple-symbol-class bytes with no further restriction. From version 2.5 on,
the standard defines it as a colon followed by a simple symbol, which
read literally excludes a leading digit and the reserved words. We consider
this unintended and keep the 2.0 rule in every version: the standard's
own keyword examples include `:56`, and there is no need to exclude
reserved words as the colon already uniquely determines the category.
-/
structure KeywordBuf where
  private ofBytes ::
  private bytes : Bytes.BytesBuf

namespace KeywordBuf

def isAllowed (value : ByteSlice) : Bool :=
  value.size != 0 && allBytes value fun c => (CharClass.classify c).isAllowedInSimpleSymbol

end KeywordBuf

/--
SMT-LIB numeral (base 10).

Cannot be empty.
Must contain only digits.
Cannot contain any leading zeros except for the constant "0" itself.
-/
structure NumeralBuf where
  private ofBytes ::
  private bytes : Bytes.BytesBuf

namespace NumeralBuf

/- LEAN: Rust walks the bytes with a flag that allows a zero everywhere but in the first
position of a numeral longer than one byte; this states the same directly. -/
def isAllowed (value : ByteSlice) : Bool :=
  if h : 0 < value.size then
    -- if the length is not 1, a leading zero must be rejected
    (value.size == 1 || value[0] != byte! '0') && allBytes value isAsciiDigit
  else
    false

/- LEAN: Rust's `from_usize`; Lean's natural numbers stand for every unsigned type. -/
/-- Construct from a natural number. -/
def fromNat (value : Nat) : NumeralBuf :=
  -- convert the value into a string and get its bytes
  -- this is allowed since it produces digits without leading zeros
  -- or the allowed special case of constant "0"
  ⟨Bytes.BytesBuf.fromByteArray (toString value).toUTF8⟩

end NumeralBuf

/--
SMT-LIB hexadecimal digits (base 16).

Cannot be empty.
Must contain only digits, lower-case letters a-f or upper-case letters A-F.
-/
structure HexDigitsBuf where
  private ofBytes ::
  private bytes : Bytes.BytesBuf

namespace HexDigitsBuf

def isAllowed (value : ByteSlice) : Bool :=
  value.size != 0 && allBytes value isAsciiHexDigit

end HexDigitsBuf

/--
SMT-LIB binary digits (base 2).

Cannot be empty.
Must contain only the digits 0, 1.
-/
structure BinDigitsBuf where
  private ofBytes ::
  private bytes : Bytes.BytesBuf

namespace BinDigitsBuf

def isAllowed (value : ByteSlice) : Bool :=
  value.size != 0 && allBytes value fun c => c == byte! '0' || c == byte! '1'

end BinDigitsBuf

/--
SMT-LIB decimal (a decimal number with whole part, a dot, then a fractional part)

A dot (the character '.') must be present. It divides the decimal into
a whole part (before it) and a fractional part (after it).

The whole part follows the same rules as `Numeral`:
cannot be empty, must contain only digits, the leading digit must not be zero.

The fractional part cannot be empty and must contain only digits.
-/
structure DecimalBuf where
  private ofBytes ::
  private bytes : Bytes.BytesBuf

namespace DecimalBuf

def isAllowed (value : ByteSlice) : Bool :=
  -- split by the dot
  match findByte value (byte! '.') with
  | none =>
    -- no dot present
    false
  | some dot =>
    let wholePart := value.slice 0 dot
    let fractionalPart := value.slice (dot + 1)
    -- the whole part must form a numeral, which also excludes a dot in it
    -- the fractional part must be a non-empty string of digits,
    -- which also excludes multiple dots
    NumeralBuf.isAllowed wholePart && fractionalPart.size != 0
      && allBytes fractionalPart isAsciiDigit

end DecimalBuf

/--
SMT-LIB whitespace (one or more whitespace bytes)

Cannot be empty.
Must contain only tabs, line feeds, carriage returns and spaces.
-/
structure WhitespaceBuf where
  private ofBytes ::
  private bytes : Bytes.BytesBuf

namespace WhitespaceBuf

def isAllowed (value : ByteSlice) : Bool :=
  value.size != 0 && allBytes value fun c =>
    c == byte! '\t' || c == byte! '\n' || c == byte! '\r' || c == byte! ' '

end WhitespaceBuf

/--
SMT-LIB comment (not including starting semicolon, including ending CR/LF)

The semicolon that starts the comment is not a part of it.
The content may be empty.
Only the last byte may be a carriage return (CR) or a line feed (LF).
If the comment runs to the end of the input, there is no ending CR/LF.
-/
structure CommentBuf where
  private ofBytes ::
  private bytes : Bytes.BytesBuf

namespace CommentBuf

def isAllowed (value : ByteSlice) : Bool :=
  -- empty content is allowed (starting semicolon at the end of input);
  -- otherwise it may not contain CR/LF except in the last position,
  -- no other restrictions
  allBytes (value.slice 0 (value.size - 1)) fun c => c != byte! '\r' && c != byte! '\n'

end CommentBuf

structure DisallowedByteVecError where
  private ofBytes ::
  private bytes : Bytes.BytesBuf

namespace DisallowedByteVecError

def intoByteArray (self : DisallowedByteVecError) : ByteArray :=
  self.bytes.intoByteArray

@[no_expose] instance : Repr DisallowedByteVecError := ⟨fun s p => reprPrec s.bytes p⟩

end DisallowedByteVecError

/- LEAN: the counterpart of the Rust macro `string8_newtype!`, which gives each type above its
methods and its view. The methods follow `BytesBuf`: `into_vec` is `intoByteArray`, and `Borrow`
and `iter` are left out, as they are for `BytesBuf`; the comparisons are made by
`plain_newtype_eq`.
Hygiene is off so that the generated code can name the private fields and constructors of
the structures above. -/
set_option hygiene false in
local macro "plain_newtype " name:ident view:ident : command => do
  let viewStructure ← `(
    structure $view where
      private ofSlice ::
      private slice : ByteSlice)
  let ownedMethods ← `(
    namespace $name

    def new (value : ByteArray) : Except DisallowedByteVecError $name :=
      let value := Bytes.BytesBuf.fromByteArray value
      if isAllowed value.asSlice then .ok ⟨value⟩ else .error ⟨value⟩

    def asSlice (self : $name) : ByteSlice := self.bytes.asSlice

    def asView (self : $name) : $view := ⟨self.bytes.asSlice⟩

    def intoBytesBuf (self : $name) : Bytes.BytesBuf := self.bytes

    def intoByteArray (self : $name) : ByteArray := self.bytes.intoByteArray

    def len (self : $name) : Nat := self.bytes.len

    def isEmpty (self : $name) : Bool := self.bytes.isEmpty

    @[no_expose] instance : Repr $name := ⟨fun s p => reprPrec s.bytes p⟩

    end $name)
  let viewMethods ← `(
    namespace $view

    /- LEAN: crate-private in Rust, where it also checks the value in debug builds. -/
    @[inline]
    def Internal.newUnchecked (value : ByteSlice) : $view := ⟨value⟩

    @[inline]
    def asSlice (self : $view) : ByteSlice := self.slice

    def intoOwned (self : $view) : $name := ⟨(Bytes.Internal.new self.slice).intoOwned⟩

    def len (self : $view) : Nat := self.slice.size

    def isEmpty (self : $view) : Bool := self.len == 0

    @[no_expose] instance : Repr $view :=
        ⟨fun s p => reprPrec (Bytes.Internal.new s.slice) p⟩

    end $view)
  return ⟨Lean.mkNullNode #[viewStructure, ownedMethods, viewMethods]⟩

/- LEAN: the comparisons that Rust derives on the types of `string8_newtype!`: `BEq` is
`PartialEq`, `Hashable` is `Hash`, with an owned value and a view of the same bytes hashing
alike. Rust's comparisons with byte slices, strings and the other of the pair are functions, as
`BEq` compares values of one type; Rust's `[u8]` and `&[u8]` are both `ByteSlice`, `str` and
`&str` both `String`. The symbol is not among those types in Rust and has none of them, so it is
given none here. -/
set_option hygiene false in
local macro "plain_newtype_eq " name:ident view:ident : command => `(
    namespace $name

    @[no_expose] instance : BEq $name := ⟨fun a b => a.bytes == b.bytes⟩

    @[no_expose] instance : Hashable $name := ⟨fun s => hash s.bytes⟩

    /-- Whether the bytes are those of the slice. -/
    def eqSlice (self : $name) (other : ByteSlice) : Bool := self.bytes.asSlice == other

    /-- Whether the bytes are those of the string's UTF-8 encoding. -/
    def eqString (self : $name) (other : String) : Bool :=
      self.bytes.asSlice == other.toUTF8.toByteSlice

    /-- Whether the bytes are those of the view. -/
    def eqView (self : $name) (other : $view) : Bool := self.bytes.asSlice == other.slice

    end $name

    namespace $view

    @[no_expose] instance : BEq $view := ⟨fun a b => a.slice == b.slice⟩

    @[no_expose] instance : Hashable $view := ⟨fun s => Bytes.Internal.hashSlice s.slice⟩

    /-- Whether the bytes are those of the slice. -/
    def eqSlice (self : $view) (other : ByteSlice) : Bool := self.slice == other

    /-- Whether the bytes are those of the string's UTF-8 encoding. -/
    def eqString (self : $view) (other : String) : Bool :=
      self.slice == other.toUTF8.toByteSlice

    /-- Whether the bytes are those of the owned value. -/
    def eqOwned (self : $view) (other : $name) : Bool := self.slice == other.bytes.asSlice

    end $view)

plain_newtype StringContentBuf StringContent

/- LEAN: the symbol is not made by `string8_newtype!` in Rust, as it carries whether it is
quoted; its methods are written out here, named as the macro's are. -/
namespace SymbolBuf

/-- Whether this is a quoted symbol enclosed in pipes, e.g. `|x|`, or a simple symbol, e.g. `x`. -/
def isQuoted (self : SymbolBuf) : Bool := self.quoted

def newUnquoted (value : ByteArray) : Except DisallowedByteVecError SymbolBuf :=
  let value := Bytes.BytesBuf.fromByteArray value
  if isUnquotedAllowed value.asSlice then .ok ⟨false, value⟩ else .error ⟨value⟩

def newQuoted (value : ByteArray) : Except DisallowedByteVecError SymbolBuf :=
  let value := Bytes.BytesBuf.fromByteArray value
  if isQuotedAllowed value.asSlice then .ok ⟨true, value⟩ else .error ⟨value⟩

def bytes (self : SymbolBuf) : Bytes := self.value.asView

def asSlice (self : SymbolBuf) : ByteSlice := self.value.asSlice

def asView (self : SymbolBuf) : Symbol := ⟨self.quoted, self.value.asSlice⟩

def intoBytesBuf (self : SymbolBuf) : Bytes.BytesBuf := self.value

def intoByteArray (self : SymbolBuf) : ByteArray := self.value.intoByteArray

def len (self : SymbolBuf) : Nat := self.value.len

def isEmpty (self : SymbolBuf) : Bool := self.value.isEmpty

end SymbolBuf

namespace Symbol

/- LEAN: crate-private in Rust, where it also checks the value in debug builds. -/
@[inline]
def Internal.newUnchecked (isQuoted : Bool) (value : ByteSlice) : Symbol := ⟨isQuoted, value⟩

@[inline]
def isQuoted (self : Symbol) : Bool := self.quoted

def bytes (self : Symbol) : Bytes := Bytes.Internal.new self.slice

@[inline]
def asSlice (self : Symbol) : ByteSlice := self.slice

def intoOwned (self : Symbol) : SymbolBuf :=
  ⟨self.quoted, (Bytes.Internal.new self.slice).intoOwned⟩

def len (self : Symbol) : Nat := self.slice.size

def isEmpty (self : Symbol) : Bool := self.len == 0

/- LEAN: Rust's `Debug`, which writes a quoted symbol in bars around the bytes' `Debug`. -/
@[no_expose] instance : Repr Symbol where
  reprPrec symbol prec :=
    if symbol.quoted then .text "|" ++ reprPrec symbol.bytes prec ++ .text "|"
    else reprPrec symbol.bytes prec

end Symbol

namespace SymbolBuf

@[no_expose] instance : Repr SymbolBuf := ⟨fun s p => reprPrec s.asView p⟩

end SymbolBuf

plain_newtype KeywordBuf Keyword
plain_newtype NumeralBuf Numeral
plain_newtype HexDigitsBuf HexDigits
plain_newtype BinDigitsBuf BinDigits
plain_newtype DecimalBuf Decimal
plain_newtype WhitespaceBuf Whitespace
plain_newtype CommentBuf Comment

/- LEAN: `eqSlice`, `eqString`, `eqView` and `eqOwned` stand for Rust's implementations of
`PartialEq` with other types, which have no names (see `plain_newtype_eq`). -/
plain_newtype_eq StringContentBuf StringContent
plain_newtype_eq KeywordBuf Keyword
plain_newtype_eq NumeralBuf Numeral
plain_newtype_eq HexDigitsBuf HexDigits
plain_newtype_eq BinDigitsBuf BinDigits
plain_newtype_eq DecimalBuf Decimal
plain_newtype_eq WhitespaceBuf Whitespace
plain_newtype_eq CommentBuf Comment

end BSmtLib.Plain

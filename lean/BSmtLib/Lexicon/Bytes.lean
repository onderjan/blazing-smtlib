module

public import Std.Data.ByteSlice

public section

namespace BSmtLib.Lexicon.Bytes

/- LEAN: `ByteArray` is Lean's `Vec<u8>`. Lean values are immutable and reference-counted;
an update changes an array in place when nothing else refers to it, and copies it
otherwise. So a view never dangles and needs no lifetime. -/
/--
Owned byte content.

Content of a lexicon value without its kind, e.g. of a symbol without whether it is quoted.
It may hold any bytes.
-/
structure BytesBuf where
  private ofByteArray ::
  private bytes : ByteArray
  deriving Inhabited

/- LEAN: `ByteSlice` from Lean's `Std` is the counterpart of `&[u8]`: a reference to a
byte array with a start and a stop. -/
/--
View of byte content.

Content of a lexicon value without its kind, e.g. of a symbol without whether it is quoted.
It may hold any bytes.
-/
structure _root_.BSmtLib.Lexicon.Bytes where
  private ofSlice ::
  private slice : ByteSlice
  deriving Inhabited

/- LEAN: the Rust `Debug` implementation; Lean's counterpart of `Debug` is the `Repr`
class, whose instances below call this. -/
/--
Writes the bytes in the manner of a Rust string literal, using byte escapes
instead of Unicode escapes as the bytes need not be UTF-8.
-/
private def reprBytes (bytes : ByteSlice) : String := Id.run do
  let mut out := "\""
  for h : i in [0:bytes.size] do
    let c := bytes[i]'h.upper
    -- specially escape the same characters Rust does
    let escape : Option String := match c.toNat with
      | 0x0A => some "\\n"
      | 0x0D => some "\\r"
      | 0x09 => some "\\t"
      | 0x5C => some "\\\\"
      | 0x00 => some "\\0"
      | 0x22 => some "\\\""
      | _ => none
    match escape with
    | some escape => out := out ++ escape
    | none =>
      if 32 ≤ c.toNat && c.toNat < 127 then
        -- not a control byte, DEL, nor non-ASCII: print as itself
        out := out.push (Char.ofNat c.toNat)
      else
        -- control byte, DEL, or non-ASCII: escape the byte
        out := out ++ "\\x" ++ (String.ofList (Nat.toDigits 16 (c.toNat / 16))).toUpper
          ++ (String.ofList (Nat.toDigits 16 (c.toNat % 16))).toUpper
  out.push '"'


/- LEAN: Rust's derived `Hash` hashes the bytes, so that an owned string and a view of the same
bytes hash alike. `ByteArray`'s hash cannot be computed on a part of an array, so the owned
strings and the views all hash their bytes with this function. -/
/-- The hash of the bytes. -/
@[inline]
def Internal.hashSlice (slice : ByteSlice) : UInt64 := Id.run do
  let mut h : UInt64 := 7
  for hi : i in [0:slice.size] do
    h := mixHash h (slice[i]'hi.upper).toUInt64
  return h

namespace BytesBuf

/-- Creates empty content. -/
@[inline]
def new : BytesBuf := ⟨ByteArray.empty⟩

/-- Converts from a byte array. -/
def fromByteArray (bytes : ByteArray) : BytesBuf := ⟨bytes⟩

/-- Converts from a single byte. -/
def fromByte (byte : UInt8) : BytesBuf := ⟨ByteArray.empty.push byte⟩

/-- Returns the content as a byte slice. -/
@[inline]
def asSlice (self : BytesBuf) : ByteSlice := self.bytes.toByteSlice

/-- Views as `Bytes`. -/
@[inline]
def view (self : BytesBuf) : Bytes := ⟨self.asSlice⟩

/-- Converts into a byte array. -/
def intoByteArray (self : BytesBuf) : ByteArray := self.bytes

/-- Returns the length of the content in bytes. -/
@[inline]
def len (self : BytesBuf) : Nat := self.bytes.size

/-- Returns `true` if the content is empty. -/
@[inline]
def isEmpty (self : BytesBuf) : Bool := self.len == 0

/- LEAN: a `ByteArray` cannot be shortened in place, so clearing gives a new empty string
instead of keeping the allocation as `Vec::clear` does. Methods that mutate in Rust
return the updated value in Lean. -/
@[inline]
def Internal.clear (_ : BytesBuf) : BytesBuf := new

/- LEAN: `copySlice` with `exact := false` appends the slice's bytes, growing the capacity
by doubling as `Vec` does. -/
@[inline]
def Internal.extendFromSlice (self : BytesBuf) (slice : ByteSlice) : BytesBuf :=
  ⟨slice.byteArray.copySlice slice.start self.bytes self.bytes.size slice.size false⟩

@[inline]
def Internal.push (self : BytesBuf) (byte : UInt8) : BytesBuf := ⟨self.bytes.push byte⟩

@[no_expose] instance : BEq BytesBuf := ⟨fun a b => a.bytes == b.bytes⟩

@[no_expose] instance : Hashable BytesBuf := ⟨fun s => Internal.hashSlice s.asSlice⟩

@[no_expose] instance : Repr BytesBuf := ⟨fun s _ => reprBytes s.asSlice⟩

/- LEAN: Rust's `impl PartialEq<[u8]> for SmtBytesBuf`. `BEq` compares values of one type, so
the comparisons with other types are functions. -/
/-- Returns `true` if the bytes are those of the slice. -/
def eqSlice (self : BytesBuf) (other : ByteSlice) : Bool := self.asSlice == other

/- LEAN: Rust's `impl PartialEq<SmtBytes<'_>> for SmtBytesBuf`, as `eqSlice`. -/
/-- Returns `true` if the bytes are those of the view. -/
def eqView (self : BytesBuf) (other : Bytes) : Bool := self.asSlice == other.slice

end BytesBuf

@[inline]
def Internal.new (slice : ByteSlice) : Bytes := ⟨slice⟩

/-- Returns the length of the content in bytes. -/
@[inline]
def len (self : Bytes) : Nat := self.slice.size

/-- Returns `true` if the content is empty. -/
@[inline]
def isEmpty (self : Bytes) : Bool := self.len == 0

/-- Returns the content as a byte slice. -/
@[inline]
def asSlice (self : Bytes) : ByteSlice := self.slice

/-- Converts into `BytesBuf`. -/
def intoOwned (self : Bytes) : BytesBuf := ⟨self.slice.toByteArray⟩

@[no_expose] instance : BEq Bytes := ⟨fun a b => a.slice == b.slice⟩

@[no_expose] instance : Repr Bytes := ⟨fun s _ => reprBytes s.slice⟩

@[no_expose] instance : Hashable Bytes := ⟨fun s => Internal.hashSlice s.slice⟩

/- LEAN: Rust's `impl PartialEq<[u8]> for SmtBytes<'_>`. `BEq` compares values of one type, so
the comparisons with other types are functions. -/
/-- Returns `true` if the bytes are those of the slice. -/
def eqSlice (self : Bytes) (other : ByteSlice) : Bool := self.slice == other

/- LEAN: Rust's `impl PartialEq<SmtBytesBuf> for SmtBytes<'_>`, as `eqSlice`. -/
/-- Returns `true` if the bytes are those of the owned string. -/
def eqOwned (self : Bytes) (other : BytesBuf) : Bool := self.slice == other.asSlice

end BSmtLib.Lexicon.Bytes

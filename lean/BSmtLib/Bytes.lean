module

public import Std.Data.ByteSlice

public section

namespace BSmtLib.Bytes

/-- An owned string of bytes. -/
/- LEAN: `ByteArray` is Lean's `Vec<u8>`. Lean values are immutable and reference-counted;
an update changes an array in place when nothing else refers to it, and copies it
otherwise. So a view never dangles and needs no lifetime. -/
structure _root_.BSmtLib.Bytes where
  private ofByteArray ::
  private bytes : ByteArray
  deriving Inhabited

/-- A view of a string of bytes. -/
/- LEAN: `ByteSlice` from Lean's `Std` is the counterpart of `&[u8]`: a reference to a
byte array with a start and a stop. -/
structure BytesView where
  private ofSlice ::
  private slice : ByteSlice
  deriving Inhabited

/--
Writes the bytes in the manner of a Rust string literal, using byte escapes
instead of Unicode escapes as the bytes need not be UTF-8.
-/
/- LEAN: the Rust `Debug` implementation; Lean's counterpart of `Debug` is the `Repr`
class, whose instances below call this. -/
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


@[inline]
def new : Bytes := ⟨ByteArray.empty⟩

def fromByteArray (bytes : ByteArray) : Bytes := ⟨bytes⟩

def fromByte (byte : UInt8) : Bytes := ⟨ByteArray.empty.push byte⟩

@[inline]
def asSlice (self : Bytes) : ByteSlice := self.bytes.toByteSlice

@[inline]
def asView (self : Bytes) : BytesView := ⟨self.asSlice⟩

def intoByteArray (self : Bytes) : ByteArray := self.bytes

@[inline]
def len (self : Bytes) : Nat := self.bytes.size

@[inline]
def isEmpty (self : Bytes) : Bool := self.len == 0

/- LEAN: a `ByteArray` cannot be shortened in place, so clearing gives a new empty string
instead of keeping the allocation as `Vec::clear` does. Methods that mutate in Rust
return the updated value in Lean. -/
@[inline]
def clear (_ : Bytes) : Bytes := new

/- LEAN: `copySlice` with `exact := false` appends the slice's bytes, growing the capacity
by doubling as `Vec` does. -/
@[inline]
def extendFromSlice (self : Bytes) (slice : ByteSlice) : Bytes :=
  ⟨slice.byteArray.copySlice slice.start self.bytes self.bytes.size slice.size false⟩

@[inline]
def push (self : Bytes) (byte : UInt8) : Bytes := ⟨self.bytes.push byte⟩

@[no_expose] instance : BEq Bytes := ⟨fun a b => a.bytes == b.bytes⟩

@[no_expose] instance : Hashable Bytes := ⟨fun s => hash s.bytes⟩

@[no_expose] instance : Repr Bytes := ⟨fun s _ => reprBytes s.asSlice⟩

namespace BytesView

@[inline]
def new (slice : ByteSlice) : BytesView := ⟨slice⟩

@[inline]
def len (self : BytesView) : Nat := self.slice.size

@[inline]
def isEmpty (self : BytesView) : Bool := self.len == 0

@[inline]
def asSlice (self : BytesView) : ByteSlice := self.slice

def intoOwned (self : BytesView) : Bytes := ⟨self.slice.toByteArray⟩

@[no_expose] instance : BEq BytesView := ⟨fun a b => a.slice == b.slice⟩

@[no_expose] instance : Repr BytesView := ⟨fun s _ => reprBytes s.slice⟩

end BytesView

end BSmtLib.Bytes

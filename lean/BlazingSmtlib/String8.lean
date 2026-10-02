import Std.Data.ByteSlice

namespace BlazingSmtlib

/-- An owned string of bytes. -/
/- LEAN: `ByteArray` is Lean's `Vec<u8>`. Lean values are immutable and reference-counted;
an update changes an array in place when nothing else refers to it, and copies it
otherwise. So a view never dangles and needs no lifetime. -/
structure String8 where
  private ofByteArray ::
  private bytes : ByteArray
  deriving Inhabited

/-- A view of a string of bytes. -/
/- LEAN: `ByteSlice` from Lean's `Std` is the counterpart of `&[u8]`: a reference to a
byte array with a start and a stop. -/
structure String8View where
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
  for i in [0:bytes.size] do
    let c := bytes.get! i
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


namespace String8

@[inline]
def new : String8 := ⟨ByteArray.empty⟩

def fromByteArray (bytes : ByteArray) : String8 := ⟨bytes⟩

def fromByte (byte : UInt8) : String8 := ⟨ByteArray.empty.push byte⟩

@[inline]
def asSlice (self : String8) : ByteSlice := self.bytes.toByteSlice

@[inline]
def asView (self : String8) : String8View := ⟨self.asSlice⟩

def intoByteArray (self : String8) : ByteArray := self.bytes

@[inline]
def len (self : String8) : Nat := self.bytes.size

@[inline]
def isEmpty (self : String8) : Bool := self.len == 0

/- LEAN: a `ByteArray` cannot be shortened in place, so clearing gives a new empty string
instead of keeping the allocation as `Vec::clear` does. Methods that mutate in Rust
return the updated value in Lean. -/
@[inline]
def clear (_ : String8) : String8 := new

/- LEAN: `copySlice` with `exact := false` appends the slice's bytes, growing the capacity
by doubling as `Vec` does. -/
@[inline]
def extendFromSlice (self : String8) (slice : ByteSlice) : String8 :=
  ⟨slice.byteArray.copySlice slice.start self.bytes self.bytes.size slice.size false⟩

@[inline]
def push (self : String8) (byte : UInt8) : String8 := ⟨self.bytes.push byte⟩

instance : BEq String8 := ⟨fun a b => a.bytes == b.bytes⟩

instance : Hashable String8 := ⟨fun s => hash s.bytes⟩

instance : Repr String8 := ⟨fun s _ => reprBytes s.asSlice⟩

end String8

namespace String8View

@[inline]
def new (slice : ByteSlice) : String8View := ⟨slice⟩

@[inline]
def len (self : String8View) : Nat := self.slice.size

@[inline]
def isEmpty (self : String8View) : Bool := self.len == 0

@[inline]
def asSlice (self : String8View) : ByteSlice := self.slice

def intoOwned (self : String8View) : String8 := ⟨self.slice.toByteArray⟩

instance : BEq String8View := ⟨fun a b => a.slice == b.slice⟩

instance : Repr String8View := ⟨fun s _ => reprBytes s.slice⟩

end String8View

end BlazingSmtlib

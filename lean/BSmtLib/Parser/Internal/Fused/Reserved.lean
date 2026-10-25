module

public import BSmtLib.Token.Reserved

public section

/-!
# Reserved words, read from the content's bytes

`Token.Reserved.fromBytes?` with the same table and hash, on the bytes, start and stop of a
token's content instead of its slice, written so that the compiler inlines it: the bytes are read
from the array directly, and the word is compared byte by byte after its length, without the
comparison of slices. The bounds are clamped as `ByteArray.toByteSlice` clamps them, so that the
lookup is the library's on the slice that the bounds make.
-/

namespace BSmtLib.Parser.Internal.Fused.Reserved

open BSmtLib (Version)

/-- The table has a slot for every hash. -/
theorem size_table : Token.Reserved.Internal.reservedTable.size = 128 :=
  Token.Reserved.Internal.size_reservedTable

/-- Whether the `length` bytes of `word` from 0 equal those of `bytes` from `start`, from the
index `index` on. -/
@[specialize]
def bytesEqFrom (word bytes : ByteArray) (start length : Nat) (inWord : length ≤ word.size)
    (inBytes : start + length ≤ bytes.size) (index : Nat) : Bool :=
  if h : index < length then
    if word[index]'(by omega) == bytes[start + index]'(by omega) then
      bytesEqFrom word bytes start length inWord inBytes (index + 1)
    else false
  else true
termination_by length - index

/-- The reserved word that the bytes from `start` to `stop` spell in the version, if any. -/
@[inline]
def ofParts? (bytes : ByteArray) (start stop : Nat) (ordered : start ≤ stop)
    (within : stop ≤ bytes.size) (version : Version) : Option Token.Reserved :=
  if empty : stop - start = 0 then
    none
  else
    let length := stop - start
    let first := (bytes[start]'(by omega)).toNat
    let last := (bytes[start + (length - 1)]'(by omega)).toNat
    let mid := (bytes[start + length / 2]'(by
      have : length / 2 < length := Nat.div_lt_self (by omega) (by decide)
      omega)).toNat
    let slot := (first + last * 4 + length * 34 + mid * 54) % 128
    let (word, reserved, since) :=
      Token.Reserved.Internal.reservedTable[slot]'(by
        rw [size_table]; exact Nat.mod_lt _ (by decide))
    if sized : word.size = length then
      if bytesEqFrom word bytes start length (by omega) (by omega) 0 &&
          Version.Internal.rank since ≤ Version.Internal.rank version then
        some reserved
      else none
    else none

/-- The reserved word that the slice `bytes.toByteSlice start stop` spells in the version, if
any: the bounds clamped as `ByteArray.toByteSlice` clamps them. -/
@[inline]
def ofBounds? (bytes : ByteArray) (start stop : Nat) (version : Version) :
    Option Token.Reserved :=
  if within : stop ≤ bytes.size then
    if ordered : start ≤ stop then ofParts? bytes start stop ordered within version
    else none
  else if ordered : start ≤ bytes.size then
    ofParts? bytes start bytes.size ordered (Nat.le_refl _) version
  else none

end BSmtLib.Parser.Internal.Fused.Reserved

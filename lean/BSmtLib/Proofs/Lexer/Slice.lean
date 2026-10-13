import BSmtLib.Lexer.Helpers

/-!
Reading a slice by indices, for the lexers of the chain that read their input as the Rust lexer
does: by `Nat` indices into the slice, where the library's lexer reads the slice's array by
`USize` positions (`BSmtLib.Lexer.Input`). Index 0 is the first byte of the slice.

The run scans are those of the library (`BSmtLib.Lexer.runEnd`, `runEndAll`), with the same
tables, over indices.
-/

namespace BSmtLib.Proofs.Lexer.Slice

open BSmtLib.Lexer (runFlagsOf endsRun Content)

/-- The byte at the index of the slice, if the index is below its size. -/
@[inline]
def get? (slice : ByteSlice) (index : Nat) : Option UInt8 :=
  if h : index < slice.size then some slice[index] else none

/-- The byte at the index of the slice, which is below its size. -/
@[inline]
def get (slice : ByteSlice) (index : Nat) (h : index < slice.size) : UInt8 :=
  slice[index]

/-- The byte at an index below the size of the slice is the one `get?` gives. -/
theorem get?_eq_some_get {slice : ByteSlice} {index : Nat} (h : index < slice.size) :
    get? slice index = some (get slice index h) := by
  unfold get? get
  simp only [h, dite_true]

/-- The first index from `index` to the size of the slice of a byte for which `stops` holds, the
size if none, or `index` if it is at the size or after it. -/
def runEndBy (stops : UInt8 → Bool) (slice : ByteSlice) (index : Nat) : Nat :=
  if h : index < slice.size then
    if stops slice[index] then index else runEndBy stops slice (index + 1)
  else
    index
termination_by slice.size - index

/--
Index of the first byte at `start` or after it carrying no flags from the
mask, the size of the slice if none, or `start` if it is at the size or after it.

In other words, the end of the longest run from `start` where all bytes carry
at least one flag from the mask.
-/
@[inline]
def runEnd (slice : ByteSlice) (start : Nat) (mask : UInt8) : Nat :=
  runEndBy (fun c => endsRun c mask) slice start

/--
Like `runEnd`, but a byte continues the run only if it has all the flags of
the mask.
-/
@[inline]
def runEndAll (slice : ByteSlice) (start : Nat) (mask : UInt8) : Nat :=
  runEndBy (fun c => runFlagsOf c &&& mask != mask) slice start

/-- The bytes of the slice from index `start` to index `stop`, which are in order and within the
slice, as a content borrowed from its array. -/
@[inline]
def borrow (slice : ByteSlice) (start stop : Nat) (ordered : start ≤ stop)
    (within : stop ≤ slice.size) : Content :=
  .borrowed slice.byteArray (slice.start + start) (slice.start + stop) (by omega) (by
    have := slice.stop_le_size_byteArray
    have := slice.start_le_stop
    have : slice.size = slice.stop - slice.start := rfl
    omega)

/-- Where a token ended. -/
structure TokenEnd where
  /-- The index in the slice where the token ended. -/
  position : Nat
  /-- Whether the token end was detected at a byte that is not a part of the token. -/
  atByte : Bool

namespace TokenEnd

def EOF : TokenEnd := { position := 0, atByte := false }

@[inline]
def mkAtByte (position : Nat) : TokenEnd := { position, atByte := true }

end TokenEnd

/-! The facts the loops of the lexers are shown to end by. -/

theorem le_runEndBy (stops : UInt8 → Bool) (slice : ByteSlice) (index : Nat) :
    index ≤ runEndBy stops slice index := by
  fun_induction runEndBy stops slice index <;> omega

/-- A run ends at its start or after it. -/
theorem le_runEnd (slice : ByteSlice) (start : Nat) (mask : UInt8) :
    start ≤ runEnd slice start mask :=
  le_runEndBy _ _ _

/-- A run ends at its start or after it. -/
theorem le_runEndAll (slice : ByteSlice) (start : Nat) (mask : UInt8) :
    start ≤ runEndAll slice start mask :=
  le_runEndBy _ _ _

theorem runEndBy_le (stops : UInt8 → Bool) (slice : ByteSlice) {index : Nat}
    (h : index ≤ slice.size) : runEndBy stops slice index ≤ slice.size := by
  fun_induction runEndBy stops slice index <;> omega

/-- A run from an index within the slice ends within it. -/
theorem runEnd_le (slice : ByteSlice) {start : Nat} (mask : UInt8) (h : start ≤ slice.size) :
    runEnd slice start mask ≤ slice.size :=
  runEndBy_le _ _ h

/-- A run from an index within the slice ends within it. -/
theorem runEndAll_le (slice : ByteSlice) {start : Nat} (mask : UInt8) (h : start ≤ slice.size) :
    runEndAll slice start mask ≤ slice.size :=
  runEndBy_le _ _ h

/-- A byte is at an index below the size of the slice. -/
theorem lt_size_of_get? {slice : ByteSlice} {index : Nat} {c : UInt8}
    (h : get? slice index = some c) : index < slice.size := by
  unfold get? at h
  split at h
  · assumption
  · cases h

/-- An index within the slice that is not its size is below the size. -/
theorem lt_size_of_ne {slice : ByteSlice} {index : Nat} (hle : index ≤ slice.size)
    (hne : ¬ (index == slice.size) = true) : index < slice.size :=
  Nat.lt_of_le_of_ne hle fun e => hne (beq_iff_eq.mpr e)

/-- A position without a byte is at or after the size of the slice. -/
theorem size_le_of_get?_none {slice : ByteSlice} {index : Nat} (h : get? slice index = none) :
    slice.size ≤ index := by
  unfold get? at h
  split at h
  · cases h
  · omega

/-- A run ends after its start if the byte at the start does not end it. -/
theorem lt_runEnd {slice : ByteSlice} {start : Nat} {c : UInt8} (mask : UInt8)
    (h : get? slice start = some c) (hc : endsRun c mask = false) :
    start < runEnd slice start mask := by
  unfold get? at h
  split at h
  · rename_i hlt
    simp only [Option.some.injEq] at h
    unfold runEnd
    rw [runEndBy]
    simp only [hlt, dite_true, h, hc, Bool.false_eq_true, ite_false]
    have := le_runEndBy (fun c => endsRun c mask) slice (start + 1)
    omega
  · cases h

end BSmtLib.Proofs.Lexer.Slice

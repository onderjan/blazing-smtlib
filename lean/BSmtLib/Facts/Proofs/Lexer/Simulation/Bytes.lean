module

public import BSmtLib.Lexer
import all BSmtLib.Lexer.Helpers
import all Std.Data.ByteSlice

@[expose] public section

/-!
# Byte arrays, views of them, and the content buffer

Facts of the library's byte arrays and views (`ByteArray`, `ByteSlice`) that the links between
the lexers use: reads of an array by `get!`, the views a slice gives of its array and the
positions of its bytes in it, and the content buffer (`ContentBuffer`), which stands for the
bytes of its array below its length (`contentBytes`) as long as the length is within the array
(`Fits`), which every change of the buffer keeps.
-/

namespace BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes

open BSmtLib.Lexer.Helpers (ContentBuffer)

/-! ## Byte arrays as lists -/

theorem toList_loop (a : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop a i r = r.reverse ++ a.data.toList.drop i := by
  induction i, r using ByteArray.toList.loop.induct a with
  | case1 i r h ih =>
    rw [ByteArray.toList.loop]
    simp only [h, ↓reduceIte]
    rw [ih]
    have h' : i < a.data.toList.length := by simpa using h
    rw [List.drop_eq_getElem_cons h']
    have h'' : i < a.data.size := h
    simp [ByteArray.get!, getElem!_pos a.data i h'']
  | case2 i r h =>
    rw [ByteArray.toList.loop]
    simp only [h, ↓reduceIte]
    have h' : a.data.toList.length ≤ i := by simp; omega
    simp [List.drop_eq_nil_of_le h']

theorem byteArray_toList (a : ByteArray) : a.toList = a.data.toList := by
  simp [ByteArray.toList, toList_loop]

/-! ## Byte arrays read by `get!` -/

theorem get!_eq_getElem! (a : ByteArray) (i : Nat) : a.get! i = a[i]! := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h]
    show a.data[i]! = _
    rw [getElem!_pos a.data i h]
    rfl
  · rw [getElem!_neg a i h]
    show a.data[i]! = _
    rw [getElem!_neg a.data i h]

theorem ext_get! {a b : ByteArray} (hs : a.size = b.size) (h : ∀ i, i < a.size → a[i]! = b[i]!) :
    a = b := by
  apply ByteArray.ext_getElem hs
  intro i hi hi'
  rw [← getElem!_pos a i hi, ← getElem!_pos b i hi', h i hi]

theorem get!_extract (a : ByteArray) (s e i : Nat) (hi : i < (a.extract s e).size) :
    (a.extract s e)[i]! = a[s + i]! := by
  rw [getElem!_pos _ i hi, getElem!_pos a (s + i) (ByteArray.getElem_extract_aux hi),
    ByteArray.getElem_extract]

theorem get!_append_left (a b : ByteArray) (i : Nat) (hi : i < a.size) :
    (a ++ b)[i]! = a[i]! := by
  rw [getElem!_pos _ i (by rw [ByteArray.size_append]; omega), getElem!_pos a i hi,
    ByteArray.getElem_append_left hi]

theorem get!_append_right (a b : ByteArray) (i : Nat) (hi : a.size ≤ i) :
    (a ++ b)[i]! = b[i - a.size]! := by
  by_cases h : i < (a ++ b).size
  · rw [getElem!_pos _ i h, getElem!_pos b (i - a.size)
      (by rw [ByteArray.size_append] at h; omega), ByteArray.getElem_append_right hi]
  · rw [getElem!_neg _ i h, getElem!_neg b (i - a.size)
      (by rw [ByteArray.size_append] at h; omega)]

/-! ## The content buffer as a byte array -/

/-- The bytes of the content buffer: those of its array below its length. -/
def contentBytes (buf : ContentBuffer) : ByteArray :=
  buf.bytes.extract 0 buf.len

/-- The length of the content buffer is within its array, as every change of it keeps. -/
def Fits (buf : ContentBuffer) : Prop :=
  buf.len ≤ buf.bytes.size

theorem contentBytes_empty : contentBytes ContentBuffer.empty = ByteArray.empty := (rfl)

theorem contentBytes_clear (buf : ContentBuffer) : contentBytes buf.clear = ByteArray.empty := by
  simp [contentBytes, ContentBuffer.clear, ByteArray.extract_same]

theorem fits_empty : Fits ContentBuffer.empty := Nat.le_refl _

theorem fits_clear (buf : ContentBuffer) : Fits buf.clear := Nat.zero_le _

theorem size_contentBytes {buf : ContentBuffer} (h : Fits buf) :
    (contentBytes buf).size = buf.len := by
  simp only [contentBytes, ByteArray.size_extract]
  unfold Fits at h
  omega

theorem get!_contentBytes {buf : ContentBuffer} (h : Fits buf) {i : Nat} (hi : i < buf.len) :
    (contentBytes buf)[i]! = buf.bytes[i]! := by
  rw [contentBytes, get!_extract _ _ _ _ (by rw [ByteArray.size_extract]; unfold Fits at h; omega),
    Nat.zero_add]

theorem len_push (buf : ContentBuffer) (x : UInt8) : (buf.push x).len = buf.len + 1 := by
  obtain ⟨bytes, len, fits⟩ := buf
  simp only [ContentBuffer.push]
  split <;> rfl

theorem fits_push {buf : ContentBuffer} (_ : Fits buf) (x : UInt8) : Fits (buf.push x) :=
  (buf.push x).fits

/-- A write of a byte within the array is the write that checks the bounds. -/
theorem set_eq_set! (bytes : ByteArray) (i : Nat) (v : UInt8) (h : i < bytes.size) :
    bytes.set i v h = bytes.set! i v := by
  obtain ⟨data⟩ := bytes
  simp only [ByteArray.set, ByteArray.set!, Array.set!_eq_setIfInBounds, Array.setIfInBounds]
  simp only [ByteArray.size] at h
  simp [h]

theorem contentBytes_push {buf : ContentBuffer} (h : Fits buf) (x : UInt8) :
    contentBytes (buf.push x) = (contentBytes buf).push x := by
  have hf := fits_push h x
  apply ext_get!
  · rw [size_contentBytes hf, ByteArray.size_push, size_contentBytes h, len_push]
  · intro i hi
    rw [size_contentBytes hf, len_push] at hi
    rw [get!_contentBytes hf (by rw [len_push]; exact hi), ByteArray.getElem!_push,
      size_contentBytes h]
    have h' := h
    unfold Fits at h'
    obtain ⟨bytes, len, fits⟩ := buf
    simp only at h' hi ⊢
    by_cases hil : i = len
    · subst hil
      simp only [ContentBuffer.push, ite_true]
      split
      · dsimp only; rw [set_eq_set!]; exact ByteArray.getElem!_set!_self _ _ _ ‹_›
      · dsimp only; rw [show i = bytes.size by omega]; exact ByteArray.getElem!_push_eq _ _
    · simp only [hil, ite_false]
      rw [get!_contentBytes h (by simp only; omega)]
      simp only [ContentBuffer.push]
      split
      · dsimp only; rw [set_eq_set!]; exact ByteArray.getElem!_set!_ne _ _ _ _ (Ne.symm hil)
      · dsimp only; exact ByteArray.getElem!_push_lt _ _ _ (by omega)

/-- What a range of an array that the content is extended from must satisfy: it ends within the
array, or it is empty. -/
def RangeOk (source : ByteArray) (start stop : Nat) : Prop :=
  stop ≤ source.size ∨ stop ≤ start

theorem extract_sub (source : ByteArray) (start stop : Nat) :
    source.extract start (start + (stop - start)) = source.extract start stop := by
  by_cases hs : start ≤ stop
  · rw [show start + (stop - start) = stop by omega]
  · rw [show start + (stop - start) = start by omega, ByteArray.extract_same]
    exact ((ByteArray.extract_eq_empty_iff).mpr (by omega)).symm

theorem size_extract_of_rangeOk {source : ByteArray} {start stop : Nat}
    (h : RangeOk source start stop) :
    (source.extract start stop).size = stop - start := by
  rw [ByteArray.size_extract]
  unfold RangeOk at h
  omega

/-- Over a range that is within the array or empty, every byte of it is copied. -/
theorem copiedCount_of_rangeOk {source : ByteArray} {start stop : Nat}
    (h : RangeOk source start stop) :
    ContentBuffer.copiedCount source start stop = stop - start := by
  unfold ContentBuffer.copiedCount
  unfold RangeOk at h
  omega

theorem len_extendFrom (buf : ContentBuffer) {source : ByteArray} {start stop : Nat}
    (hr : RangeOk source start stop) :
    (buf.extendFrom source start stop).len = buf.len + (stop - start) :=
  congrArg (buf.len + ·) (copiedCount_of_rangeOk hr)

theorem bytes_extendFrom {buf : ContentBuffer} {source : ByteArray}
    {start stop : Nat} (hr : RangeOk source start stop) :
    (buf.extendFrom source start stop).bytes =
      contentBytes buf ++ source.extract start stop ++
        buf.bytes.extract (buf.len + (stop - start)) buf.bytes.size := by
  obtain ⟨bytes, len, fits⟩ := buf
  simp only [ContentBuffer.extendFrom, ByteArray.copySlice_eq_append, contentBytes,
    extract_sub]
  congr 2
  unfold RangeOk at hr
  have : min (stop - start) (source.data.size - start) = stop - start := by
    simp only [ByteArray.size_data] at *
    omega
  rw [this]

theorem fits_extendFrom {buf : ContentBuffer} (_ : Fits buf) {source : ByteArray}
    {start stop : Nat} (_ : RangeOk source start stop) :
    Fits (buf.extendFrom source start stop) :=
  (buf.extendFrom source start stop).fits

theorem contentBytes_extendFrom {buf : ContentBuffer} (h : Fits buf) {source : ByteArray}
    {start stop : Nat} (hr : RangeOk source start stop) :
    contentBytes (buf.extendFrom source start stop) =
      contentBytes buf ++ source.extract start stop := by
  conv => lhs; unfold contentBytes
  rw [bytes_extendFrom hr, len_extendFrom _ hr]
  apply ByteArray.extract_append_eq_left
  rw [ByteArray.size_append, size_contentBytes h, size_extract_of_rangeOk hr]

/-! ## Views of the slice and positions in its array -/

section

variable (input : ByteSlice) (a b : Nat)

/-- The view of the slice from `a` to `b`, with both clamped to its size and `a` to `b`. -/
theorem slice_spec :
    (input.slice a b).byteArray = input.byteArray ∧
      (input.slice a b).start = input.start + min (min a input.size) (min b input.size) ∧
      (input.slice a b).stop = input.start + min b input.size := by
  have := input.stop_le_size_byteArray
  have := input.start_le_stop
  have hs : input.size = input.stop - input.start := rfl
  unfold ByteSlice.slice
  dsimp only
  split
  · split
    · refine ⟨rfl, ?_, rfl⟩
      show input.start + min a input.size = _
      omega
    · refine ⟨rfl, ?_, rfl⟩
      show input.start + min b input.size = _
      omega
  · omega

theorem slice_byteArray : (input.slice a b).byteArray = input.byteArray :=
  (slice_spec input a b).1

variable {a b}

theorem slice_start (hab : a ≤ b) (hb : b ≤ input.size) :
    (input.slice a b).start = input.start + a := by
  rw [(slice_spec input a b).2.1]
  omega

theorem slice_stop (hb : b ≤ input.size) : (input.slice a b).stop = input.start + b := by
  rw [(slice_spec input a b).2.2]
  omega

theorem slice_size (hab : a ≤ b) (hb : b ≤ input.size) : (input.slice a b).size = b - a := by
  simp only [ByteSlice.size, slice_start input hab hb, slice_stop input hb]
  omega

theorem slice_toByteArray (h : b ≤ input.size ∨ b ≤ a) :
    (input.slice a b).toByteArray =
      input.byteArray.extract (input.start + a) (input.start + b) := by
  have := input.stop_le_size_byteArray
  have := input.start_le_stop
  have hs : input.size = input.stop - input.start := rfl
  obtain ⟨h1, h2, h3⟩ := slice_spec input a b
  rw [ByteSlice.toByteArray, ByteSlice.size, h1, h2, h3]
  by_cases hab : a ≤ b ∧ b ≤ input.size
  · congr 1 <;> omega
  · have e1 : min (min a input.size) (min b input.size) = min b input.size := by omega
    rw [e1, Nat.sub_self, Nat.add_zero, ByteArray.extract_same]
    exact ((ByteArray.extract_eq_empty_iff).mpr (by omega)).symm

/-- Extending the buffer from positions in the slice's array is extending the bytes by the view
of the slice, for a range that ends within the slice or is empty. -/
theorem contentBytes_extendSlice {buf : ContentBuffer} (h : Fits buf)
    (hr : b ≤ input.size ∨ b ≤ a) :
    contentBytes (buf.extendFrom input.byteArray (input.start + a) (input.start + b)) =
      contentBytes buf ++ (input.slice a b).toByteArray := by
  have := input.stop_le_size_byteArray
  have hs : input.size = input.stop - input.start := rfl
  rw [contentBytes_extendFrom h (by unfold RangeOk; omega), slice_toByteArray input hr]

theorem fits_extendSlice {buf : ContentBuffer} (h : Fits buf) (hr : b ≤ input.size ∨ b ≤ a) :
    Fits (buf.extendFrom input.byteArray (input.start + a) (input.start + b)) := by
  have := input.stop_le_size_byteArray
  have hs : input.size = input.stop - input.start := rfl
  exact fits_extendFrom h (by unfold RangeOk; omega)

end

/-! ## Views of an array -/

theorem toByteArray_toByteSlice (a : ByteArray) : a.toByteSlice.toByteArray = a := by
  simp [ByteArray.toByteSlice, ByteSlice.toByteArray, ByteSlice.size, ByteSlice.start,
    ByteSlice.stop, ByteSlice.byteArray, ByteArray.extract_zero_size]

theorem toByteSlice_beq (a b : ByteArray) :
    (a.toByteSlice == b.toByteSlice) = true ↔ a = b := by
  change ByteSlice.beq _ _ = true ↔ _
  unfold ByteSlice.beq
  rw [toByteArray_toByteSlice, toByteArray_toByteSlice]
  change (a.data == b.data) = true ↔ _
  rw [beq_iff_eq]
  exact ⟨fun h => ByteArray.ext h, fun h => h ▸ rfl⟩

theorem size_toByteSlice' (a : ByteArray) : a.toByteSlice.size = a.data.toList.length := by
  rw [Array.length_toList]
  simp only [ByteArray.toByteSlice, Nat.le_refl, Nat.zero_le, dite_true, ByteSlice.size,
    ByteSlice.start, ByteSlice.stop, Nat.sub_zero]
  rfl

theorem start_add_lt (s : ByteSlice) {i : Nat} (h : i < s.size) :
    s.start + i < s.byteArray.data.size := by
  have := s.stop_le_size_byteArray
  simp only [ByteSlice.size] at h
  simp only [ByteArray.size] at this
  omega

theorem getElem_slice (s : ByteSlice) (i : Nat) (h : i < s.size) :
    s[i] = s.byteArray.data[s.start + i]'(start_add_lt s h) := (rfl)

theorem toByteArray_toByteSlice_range (a : ByteArray) {i j : Nat} (hij : i ≤ j) (hj : j ≤ a.size) :
    (a.toByteSlice i j).toByteArray = a.extract i j := by
  simp only [ByteArray.toByteSlice, hj, hij, dite_true, ByteSlice.toByteArray, ByteSlice.byteArray,
    ByteSlice.start, ByteSlice.size, ByteSlice.stop]
  congr 1
  omega

theorem size_toByteArray (s : ByteSlice) : s.toByteArray.size = s.size := by
  have h1 := s.stop_le_size_byteArray
  have h2 := s.start_le_stop
  simp only [ByteSlice.toByteArray, ByteArray.size_extract, ByteSlice.size]
  omega

theorem size_toByteSlice_full (a : ByteArray) : a.toByteSlice.size = a.size := by
  simp [ByteArray.toByteSlice, ByteSlice.size, ByteSlice.start, ByteSlice.stop]

theorem getElem_slice_byteArray (s : ByteSlice) (i : Nat) (h : i < s.size) :
    s[i] = s.byteArray[s.start + i]'(by
      have := s.stop_le_size_byteArray; simp only [ByteSlice.size] at h; omega) := (rfl)

theorem size_toByteArray_toByteSlice (s : ByteSlice) :
    s.toByteArray.toByteSlice.size = s.size := by
  rw [size_toByteSlice_full, size_toByteArray]

theorem get!_toByteArray (s : ByteSlice) (i : Nat) :
    s.toByteArray.toByteSlice.get! i = s.get! i := by
  have hs := size_toByteArray_toByteSlice s
  simp only [ByteSlice.get!, ByteSlice.getD]
  by_cases h : i < s.size
  · have h' : i < s.toByteArray.toByteSlice.size := by omega
    simp only [h, h', dite_true]
    rw [getElem_slice_byteArray, getElem_slice_byteArray]
    have h1 := s.stop_le_size_byteArray
    simp only [ByteSlice.size] at h
    simp [ByteArray.toByteSlice, ByteSlice.byteArray, ByteSlice.start, ByteSlice.toByteArray,
      ByteSlice.size, ByteSlice.stop, ByteArray.getElem_extract]
  · have h' : ¬ i < s.toByteArray.toByteSlice.size := by omega
    simp only [h, h', dite_false]

theorem getElem_toByteArray (s : ByteSlice) (i : Nat) (h : i < s.toByteArray.toByteSlice.size) :
    s.toByteArray.toByteSlice[i] = s[i]'(by rwa [size_toByteArray_toByteSlice] at h) := by
  have e := get!_toByteArray s i
  have h' : i < s.size := by rwa [size_toByteArray_toByteSlice] at h
  simp only [ByteSlice.get!, ByteSlice.getD, h, h', dite_true] at e
  exact e

theorem beq_toByteArray (w s : ByteSlice) : (w == s.toByteArray.toByteSlice) = (w == s) := by
  show ByteSlice.beq _ _ = ByteSlice.beq _ _
  unfold ByteSlice.beq
  rw [toByteArray_toByteSlice]

theorem empty_append (b : ByteArray) : ByteArray.empty ++ b = b := by
  apply ByteArray.ext
  rw [ByteArray.data_append, show ByteArray.empty.data = #[] from rfl, Array.empty_append]

end BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes

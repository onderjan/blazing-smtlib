import BSmtLib.Proofs.Lexer.X1BatchInCore
import BSmtLib.Proofs.Lexer.X2Contents

/-!
# The content buffer and the byte array of the token content

The lexer with the content buffer `X2Contents` keeps the content of the token in progress in a
buffer, a byte array with a length (`ContentBuffer`), where the lexer with the batch kept in the
lexer's state `X1BatchInCore` keeps a byte array of its own. The buffer stands for its bytes
below its length (`contentBytes`), as long as the length is within its array (`Fits`), which
every change of the buffer keeps. This module proves the changes and reads of the buffer that
the lexers make against those of the byte array, the contents of tokens lexed from the slice,
which the second lexer takes as a view of the slice and the first as positions in its array,
and gives the map from the states of the first lexer to those of the second (`coreMap`).
-/

namespace BSmtLib.Proofs.X1BatchInCoreX2Contents

open BSmtLib.Lexer (ContentBuffer)

theorem get!_eq_getElem! (a : ByteArray) (i : Nat) : a.get! i = a[i]! := by
  by_cases h : i < a.size
  · rw [getElem!_pos a i h]
    show a.data[i]! = _
    rw [getElem!_pos a.data i h]
    rfl
  · rw [getElem!_neg a i h]
    show a.data[i]! = _
    rw [getElem!_neg a.data i h]

/-! ## Byte arrays read by `get!` -/

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

theorem contentBytes_empty : contentBytes ContentBuffer.empty = ByteArray.empty := rfl

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
  obtain ⟨bytes, len⟩ := buf
  simp only [ContentBuffer.push]
  split <;> rfl

theorem fits_push {buf : ContentBuffer} (h : Fits buf) (x : UInt8) : Fits (buf.push x) := by
  obtain ⟨bytes, len⟩ := buf
  unfold Fits at h ⊢
  simp only [ContentBuffer.push] at h ⊢
  split
  · simp only [ByteArray.size_set!]; omega
  · simp only [ByteArray.size_push]; omega

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
    obtain ⟨bytes, len⟩ := buf
    simp only at h' hi ⊢
    by_cases hil : i = len
    · subst hil
      simp only [ContentBuffer.push, ite_true]
      split
      · exact ByteArray.getElem!_set!_self _ _ _ ‹_›
      · rw [show i = bytes.size by omega]; exact ByteArray.getElem!_push_eq _ _
    · simp only [hil, ite_false]
      rw [get!_contentBytes h (by simp only; omega)]
      simp only [ContentBuffer.push]
      split
      · exact ByteArray.getElem!_set!_ne _ _ _ _ (Ne.symm hil)
      · exact ByteArray.getElem!_push_lt _ _ _ (by omega)

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

theorem len_extendFrom (buf : ContentBuffer) (source : ByteArray) (start stop : Nat) :
    (buf.extendFrom source start stop).len = buf.len + (stop - start) := rfl

theorem bytes_extendFrom {buf : ContentBuffer} {source : ByteArray}
    {start stop : Nat} (hr : RangeOk source start stop) :
    (buf.extendFrom source start stop).bytes =
      contentBytes buf ++ source.extract start stop ++
        buf.bytes.extract (buf.len + (stop - start)) buf.bytes.size := by
  obtain ⟨bytes, len⟩ := buf
  simp only [ContentBuffer.extendFrom, ByteArray.copySlice_eq_append, contentBytes,
    extract_sub]
  congr 2
  unfold RangeOk at hr
  have : min (stop - start) (source.data.size - start) = stop - start := by
    simp only [ByteArray.size_data] at *
    omega
  rw [this]

theorem fits_extendFrom {buf : ContentBuffer} (h : Fits buf) {source : ByteArray}
    {start stop : Nat} (hr : RangeOk source start stop) :
    Fits (buf.extendFrom source start stop) := by
  unfold Fits
  rw [bytes_extendFrom hr, len_extendFrom, ByteArray.size_append, ByteArray.size_append,
    size_contentBytes h, size_extract_of_rangeOk hr]
  omega

theorem contentBytes_extendFrom {buf : ContentBuffer} (h : Fits buf) {source : ByteArray}
    {start stop : Nat} (hr : RangeOk source start stop) :
    contentBytes (buf.extendFrom source start stop) =
      contentBytes buf ++ source.extract start stop := by
  conv => lhs; unfold contentBytes
  rw [bytes_extendFrom hr, len_extendFrom]
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

/-! ## Reads of a content -/

theorem size_stored {buf : ContentBuffer} (h : Fits buf) :
    Lexer.X1BatchInCore.Content.stored.size (contentBytes buf) =
      BSmtLib.Lexer.Content.stored.size buf :=
  size_contentBytes h

theorem last?_stored {buf : ContentBuffer} (h : Fits buf) :
    Lexer.X1BatchInCore.Content.stored.last? (contentBytes buf) =
      BSmtLib.Lexer.Content.stored.last? buf := by
  simp only [Lexer.X1BatchInCore.Content.last?, BSmtLib.Lexer.Content.last?, size_contentBytes h]
  split
  · rfl
  · rename_i hne
    rw [get!_eq_getElem!, get!_eq_getElem!, get!_contentBytes h (by simp at hne; omega)]

theorem isZero_stored {buf : ContentBuffer} (h : Fits buf) (x : UInt8) :
    ((contentBytes buf).size == 1 && (contentBytes buf).get! 0 == x) =
      (buf.len == 1 && buf.bytes.get! 0 == x) := by
  rw [size_contentBytes h]
  by_cases hl : buf.len = 1
  · rw [get!_eq_getElem!, get!_eq_getElem!, get!_contentBytes h (by omega)]
  · have e : (buf.len == 1) = false := by simpa using hl
    rw [e]
    rfl

theorem size_borrow (hab : a ≤ b) (hb : b ≤ input.size) (stored : ByteArray)
    (stored' : ContentBuffer) :
    (Lexer.X1BatchInCore.borrow input a b).size stored =
      (Lexer.Slice.borrow input a b).size stored' := by
  simp only [Lexer.X1BatchInCore.borrow, Lexer.Slice.borrow, Lexer.X1BatchInCore.Content.size,
    BSmtLib.Lexer.Content.size, slice_size input hab hb]
  omega

theorem last?_borrow (hab : a ≤ b) (hb : b ≤ input.size) (stored : ByteArray)
    (stored' : ContentBuffer) :
    (Lexer.X1BatchInCore.borrow input a b).last? stored =
      (Lexer.Slice.borrow input a b).last? stored' := by
  have := input.stop_le_size_byteArray
  have hs : input.size = input.stop - input.start := rfl
  simp only [Lexer.X1BatchInCore.borrow, Lexer.Slice.borrow, Lexer.X1BatchInCore.Content.last?,
    BSmtLib.Lexer.Content.last?, slice_size input hab hb]
  by_cases hab' : b - a = 0
  · have e1 : (b - a == 0) = true := by simpa using hab'
    have e2 : (input.start + b == input.start + a) = true := by simp; omega
    rw [e1, e2]
    rfl
  · have e1 : (b - a == 0) = false := by simpa using hab'
    have e2 : (input.start + b == input.start + a) = false := by simp; omega
    rw [e1, e2]
    simp only [Bool.false_eq_true, ite_false, Option.some.injEq]
    rw [ByteSlice.getD, dite_eq_left_of_eq_true (eq_true (by rw [slice_size input hab hb]; omega))]
    rw [get!_eq_getElem!, getElem!_pos _ _ (by omega)]
    show (input.slice a b).byteArray[(input.slice a b).start + (b - a - 1)]'_ = _
    simp only [slice_byteArray, slice_start input hab hb]
    congr 1
    omega

end

/-! ## The states -/

/-- The state of the lexer with the content buffer. -/
abbrev Core2 := Lexer.X2Contents.LexerCore

/-- The state of the lexer with the batch kept in the lexer's state. -/
abbrev Core1 := Lexer.X1BatchInCore.LexerCore

/-- The state of the lexer with the batch kept in the lexer's state for that of the lexer with
the content buffer: every field the same, and the token content the buffer's bytes. -/
def coreMap (c : Core2) : Core1 :=
  { version := c.version, initialVersion := c.initialVersion, state := c.state
    discard := c.discard, recovers := c.recovers, consumedDepth := c.consumedDepth
    lexedDepth := c.lexedDepth, recoveryState := c.recoveryState, tokenStart := c.tokenStart
    tokenContent := contentBytes c.tokenContent, offset := c.offset, base := c.base
    line := c.line, lineStart := c.lineStart, batch := c.batch
    tokenStarted := c.tokenStarted, batchEnded := c.batchEnded }

/-- The bounded state of the lexer with the content buffer. -/
abbrev S2 (floor : Option Nat) (low : Nat) := {c : Core2 // c.Bound floor low}

/-- The bounded state of the lexer with the batch kept in the lexer's state. -/
abbrev S1 (floor : Option Nat) (low : Nat) := {c : Core1 // c.Bound floor low}

/-- The bounded states, mapped. -/
def boundMap {floor : Option Nat} {low : Nat} (c : S2 floor low) : S1 floor low :=
  ⟨coreMap c.val, c.property⟩

/-- The content buffer of the bounded state fits its array. -/
abbrev BFits {floor : Option Nat} {low : Nat} (c : S2 floor low) : Prop := Fits c.val.tokenContent

end BSmtLib.Proofs.X1BatchInCoreX2Contents

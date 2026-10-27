module

public import BSmtLib.Parser.Internal.Fused.Basic
import all BSmtLib.Parser.Internal.Fused.Basic
import all BSmtLib.Parser.Internal.Fused.Reserved
import all BSmtLib.Lexicon.Reserved

@[expose] public section

/-!
# The reserved-word lookup on bytes against the library's

The fused reader looks reserved words up on the bytes and bounds of a token's content
(`Parser.Internal.Fused.Reserved.ofBounds?`); the port, on the content's slice
(`Lexicon.Reserved.fromBytes?`). The two agree on every array and bounds (`ofBounds?_eq`), so on
every token (`reservedAt_eq`): the bounds are clamped as `ByteArray.toByteSlice` clamps them, the
hash reads the same bytes, the word is compared byte by byte where the library compares slices,
and the versions by rank where the library compares them by their order.
-/

namespace BSmtLib.Facts.Proofs.Parser.Fused.Reserved

open BSmtLib.Parser.Internal.Fused.Reserved
open BSmtLib.Parser.Internal.Fused.Basic (contentOf reservedAt?)
open BSmtLib.Token (BatchTag)
open BSmtLib.Lexer.Cursor (LexerCursor LexerToken)
open BSmtLib (Version)

/-- The bounds of a slice made within its array. -/
theorem toByteSlice_parts (bytes : ByteArray) {start stop : Nat} (ordered : start ≤ stop)
    (within : stop ≤ bytes.size) :
    (bytes.toByteSlice start stop).byteArray = bytes ∧
      (bytes.toByteSlice start stop).start = start ∧
      (bytes.toByteSlice start stop).stop = stop := by
  unfold ByteArray.toByteSlice
  rw [dite_eq_left within, dite_eq_left ordered]
  exact ⟨rfl, rfl, rfl⟩

/-- The comparison from an index on: every byte from it on is equal. -/
theorem bytesEqFrom_iff (word bytes : ByteArray) (start length : Nat) (inWord : length ≤ word.size)
    (inBytes : start + length ≤ bytes.size) (index : Nat) :
    bytesEqFrom word bytes start length inWord inBytes index = true ↔
      ∀ i (_ : index ≤ i) (hl : i < length),
        word[i]'(by omega) = bytes[start + i]'(by omega) := by
  induction index using bytesEqFrom.induct word bytes start length inWord inBytes with
  | case1 index h heq ih =>
    rw [bytesEqFrom, dite_eq_left h, ite_eq_left heq, ih]
    constructor
    · intro hall i hi hl
      by_cases e : i = index
      · subst e
        exact beq_iff_eq.mp heq
      · exact hall i (by omega) hl
    · intro hall i hi hl
      exact hall i (by omega) hl
  | case2 index h hne =>
    rw [bytesEqFrom, dite_eq_left h, ite_eq_right hne]
    simp only [Bool.false_eq_true, false_iff, Classical.not_forall]
    exact ⟨index, Nat.le_refl _, h, fun e => hne (beq_iff_eq.mpr e)⟩
  | case3 index h =>
    rw [bytesEqFrom, dite_eq_right h]
    simp only [true_iff]
    intro i hi hl
    omega

/-- A word equals the bytes of a slice when it has their length and each of their bytes. -/
theorem word_beq_iff (word bytes : ByteArray) {start stop : Nat} (ordered : start ≤ stop)
    (within : stop ≤ bytes.size) :
    (word.toByteSlice == bytes.toByteSlice start stop) = true ↔
      ∃ (sized : word.size = stop - start), ∀ i (hl : i < stop - start),
        word[i]'(by omega) = bytes[start + i]'(by omega) := by
  obtain ⟨hb, hs, he⟩ := toByteSlice_parts bytes ordered within
  obtain ⟨wb, ws, we⟩ := toByteSlice_parts word (Nat.zero_le word.size) (Nat.le_refl _)
  show (ByteSlice.beq _ _) = true ↔ _
  unfold ByteSlice.beq ByteSlice.toByteArray ByteSlice.size
  rw [hb, hs, he, wb, ws, we]
  show (ByteArray.beq _ _) = true ↔ _
  unfold ByteArray.beq
  rw [beq_iff_eq, Array.ext_iff]
  simp only [ByteArray.data_extract, Array.size_extract, ByteArray.size_data,
    Array.getElem_extract, ByteArray.getElem_eq_getElem_data, Nat.zero_add, Nat.sub_zero]
  have e2 : min (start + (stop - start)) bytes.size - start = stop - start := by omega
  simp only [Nat.min_self, e2]
  constructor
  · rintro ⟨hsize, hall⟩
    exact ⟨hsize, fun i hl => hall i (by omega) hl⟩
  · rintro ⟨sized, hall⟩
    exact ⟨sized, fun i _ h₂ => hall i h₂⟩

/-- A byte of a slice made within its array is the array's byte from the start on. -/
theorem slice_getElem (bytes : ByteArray) {start stop : Nat} (ordered : start ≤ stop)
    (within : stop ≤ bytes.size) (i : Nat) (h : i < (bytes.toByteSlice start stop).size) :
    (bytes.toByteSlice start stop)[i] = bytes[start + i]'(by
      unfold ByteSlice.size at h
      obtain ⟨_, hs, he⟩ := toByteSlice_parts bytes ordered within
      rw [hs, he] at h
      omega) := by
  obtain ⟨hb, hs, he⟩ := toByteSlice_parts bytes ordered within
  show (bytes.toByteSlice start stop).get ⟨i, h⟩ = _
  unfold ByteSlice.get
  simp only [hb, hs]

/-- The slot of a slice made within its array, hashed from the array's bytes. -/
theorem slot_eq (bytes : ByteArray) {start stop : Nat} (ordered : start ≤ stop)
    (within : stop ≤ bytes.size) (h : 0 < (bytes.toByteSlice start stop).size)
    (hsize : (bytes.toByteSlice start stop).size = stop - start) :
    (Lexicon.Reserved.Internal.reservedSlot (bytes.toByteSlice start stop) h).val =
      ((bytes[start]'(by omega)).toNat +
        (bytes[start + (stop - start - 1)]'(by omega)).toNat * 4 + (stop - start) * 34 +
        (bytes[start + (stop - start) / 2]'(by
          have : (stop - start) / 2 < stop - start := Nat.div_lt_self (by omega) (by decide)
          omega)).toNat * 54) % 128 := by
  unfold Lexicon.Reserved.Internal.reservedSlot
  simp only [slice_getElem bytes ordered within, hsize, Nat.add_zero]
  rfl

/-- A read of an entry at equal indices of an array. -/
theorem array_getElem_congr {α : Type} (a : Array α) {i j : Nat} (hij : i = j) (hi : i < a.size)
    (hj : j < a.size) : a[i] = a[j] := by
  subst hij
  rfl

/-- The lookup within the array is the library's on the slice the bounds make. -/
theorem ofParts?_eq (bytes : ByteArray) (start stop : Nat) (ordered : start ≤ stop)
    (within : stop ≤ bytes.size) (version : Version) :
    ofParts? bytes start stop ordered within version =
      BSmtLib.Lexicon.Reserved.fromBytes? (bytes.toByteSlice start stop) version := by
  obtain ⟨hb, hs, he⟩ := toByteSlice_parts bytes ordered within
  have hsize : (bytes.toByteSlice start stop).size = stop - start := by
    unfold ByteSlice.size
    rw [hs, he]
  unfold ofParts? BSmtLib.Lexicon.Reserved.fromBytes?
  by_cases empty : stop - start = 0
  · rw [dite_eq_left empty, dite_eq_left (hsize.trans empty)]
  rw [dite_eq_right empty, dite_eq_right (fun h => empty (hsize.symm.trans h))]
  have hpos : 0 < (bytes.toByteSlice start stop).size := by omega
  have e := array_getElem_congr Lexicon.Reserved.Internal.reservedTable
    (slot_eq bytes ordered within hpos hsize)
    (by rw [Lexicon.Reserved.Internal.size_reservedTable]; exact Fin.isLt _)
    (by rw [size_table]; exact Nat.mod_lt _ (by decide))
  simp only [e]
  rw [e]
  generalize Lexicon.Reserved.Internal.reservedTable[((_ : Nat))]'_ = entry
  obtain ⟨word, reserved, since⟩ := entry
  have hcmp := word_beq_iff word bytes ordered within
  by_cases sized : word.size = stop - start
  · rw [dite_eq_left sized]
    by_cases same : ∀ i (hl : i < stop - start),
        word[i]'(by omega) = bytes[start + i]'(by omega)
    · have heq : bytesEqFrom word bytes start (stop - start) (by omega) (by omega) 0 = true :=
        (bytesEqFrom_iff _ _ _ _ _ _ 0).mpr fun i _ hl => same i hl
      have hslice : (word.toByteSlice == bytes.toByteSlice start stop) = true :=
        hcmp.mpr ⟨sized, same⟩
      rw [heq, hslice, Bool.true_and, Bool.true_and]
      -- `version ≥ since` is by definition the comparison of the ranks
      by_cases hv : version ≥ since
      · rw [ite_eq_left (decide_eq_true (show Version.Internal.rank since ≤
            Version.Internal.rank version from hv)), ite_eq_left (decide_eq_true hv)]
      · rw [ite_eq_right (fun (h : decide (Version.Internal.rank since ≤
            Version.Internal.rank version) = true) => hv (of_decide_eq_true h)),
          ite_eq_right (fun h => hv (of_decide_eq_true h))]
    · have heq : bytesEqFrom word bytes start (stop - start) (by omega) (by omega) 0 = false := by
        cases h : bytesEqFrom word bytes start (stop - start) (by omega) (by omega) 0
        · rfl
        · exact absurd (fun i hl => (bytesEqFrom_iff _ _ _ _ _ _ 0).mp h i (Nat.zero_le _) hl)
            same
      have hslice : (word.toByteSlice == bytes.toByteSlice start stop) = false := by
        cases h : (word.toByteSlice == bytes.toByteSlice start stop)
        · rfl
        · obtain ⟨_, all⟩ := hcmp.mp h
          exact absurd all same
      rw [heq, hslice, Bool.false_and, Bool.false_and]
  · rw [dite_eq_right sized]
    have hslice : (word.toByteSlice == bytes.toByteSlice start stop) = false := by
      cases h : (word.toByteSlice == bytes.toByteSlice start stop)
      · rfl
      · obtain ⟨s, _⟩ := hcmp.mp h
        exact absurd s sized
    rw [hslice, Bool.false_and]
    rfl

/-- The lookup on bounds, clamped, is the library's on the slice the bounds make. -/
theorem ofBounds?_eq (bytes : ByteArray) (start stop : Nat) (version : Version) :
    ofBounds? bytes start stop version =
      Lexicon.Reserved.fromBytes? (bytes.toByteSlice start stop) version := by
  unfold ofBounds?
  by_cases within : stop ≤ bytes.size
  · rw [dite_eq_left within]
    by_cases ordered : start ≤ stop
    · rw [dite_eq_left ordered, ofParts?_eq]
    · rw [dite_eq_right ordered]
      -- the slice is empty, which is no word
      have : (bytes.toByteSlice start stop) = bytes.toByteSlice stop stop := by
        unfold ByteArray.toByteSlice
        rw [dite_eq_left within, dite_eq_right ordered, dite_eq_left within,
          dite_eq_left (Nat.le_refl _)]
      rw [this, ← ofParts?_eq bytes stop stop (Nat.le_refl _) within]
      unfold ofParts?
      rw [dite_eq_left (Nat.sub_self _)]
  · rw [dite_eq_right within]
    have clamp : bytes.toByteSlice start stop = bytes.toByteSlice start bytes.size := by
      unfold ByteArray.toByteSlice
      rw [dite_eq_right within, dite_eq_left (Nat.le_refl _)]
    rw [clamp]
    by_cases ordered : start ≤ bytes.size
    · rw [dite_eq_left ordered, ofParts?_eq]
    · rw [dite_eq_right ordered]
      have : bytes.toByteSlice start bytes.size = bytes.toByteSlice bytes.size bytes.size := by
        unfold ByteArray.toByteSlice
        rw [dite_eq_left (Nat.le_refl _), dite_eq_right ordered, dite_eq_left (Nat.le_refl _),
          dite_eq_left (Nat.le_refl _)]
      rw [this, ← ofParts?_eq bytes bytes.size bytes.size (Nat.le_refl _) (Nat.le_refl _)]
      unfold ofParts?
      rw [dite_eq_left (Nat.sub_self _)]

/-- The fused reader's content is the cursor's. -/
theorem contentOf_eq {batch : BatchTag} (next : LexerCursor batch) (token : LexerToken batch) :
    contentOf next token = next.content token :=
  (Lexer.Cursor.Internal.content_eq_parts next token).symm

/-- The reserved-word lookup on the content's bytes is the library's on the content. -/
theorem reservedAt_eq {batch : BatchTag} (version : Version) (next : LexerCursor batch)
    (token : LexerToken batch) :
    reservedAt? version next token = Lexicon.Reserved.fromBytes? (next.content token) version := by
  unfold reservedAt?
  rw [ofBounds?_eq, Lexer.Cursor.Internal.content_eq_parts]

end BSmtLib.Facts.Proofs.Parser.Fused.Reserved

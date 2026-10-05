import BSmtLib.Proofs.V1Naive.Facts

/-!
# Reserved words

`fromBytes_kind`: the library's lookup of reserved words, `Reserved.fromBytes?`, finds exactly
the reserved words of the spec in each version, with the kind the spec gives them. The lookup
reads the table `Reserved.Internal.reservedTable`, whose entries the kernel checks one by one.
-/

open BSmtLib.Proofs BSmtLib.SpecChecks.Lexicon
open BSmtLib.Spec.Lexicon (chars basicReservedWords commandNames)
open BSmtLib.Spec.Lexer (ReservedKind)

namespace BSmtLib.Proofs.Lexer.V1Naive

/-- The kind of reserved word of the spec for a reserved word of the library. -/
def reservedKindOf (word : Reserved) : ReservedKind :=
  if word.isCommandName then .command else .general

/-- The kind of reserved word the spec gives the characters in the version, if they are one. -/
def specReservedKind (version : Spec.Lexicon.Version) (x : List UInt8) : Option ReservedKind :=
  if x ∈ (basicReservedWords version).map chars then some .general
  else if x ∈ (commandNames version).map chars then some .command
  else none

theorem getElem!_mem {α : Type} [Inhabited α] (T : Array α) (i : Nat) :
    T[i]! ∈ T.toList ∨ T[i]! = default := by
  by_cases h : i < T.size
  · left
    rw [getElem!_pos T i h]
    exact Array.getElem_mem_toList h
  · right
    rw [getElem!_neg T i h]

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

theorem fromBytes_kind (version : Spec.Lexicon.Version) (a : ByteArray) :
    (Reserved.fromBytes? a.toByteSlice (Adapter.toVersion version)).map reservedKindOf =
      specReservedKind version a.data.toList := by
  unfold Reserved.fromBytes?
  generalize hT : BSmtLib.Reserved.Internal.reservedTable = T
  generalize hslot : BSmtLib.Reserved.Internal.reservedSlot = slot
  have hgood : ∀ e ∈ T.toList, e.1.size = 0 ∨
      (if Adapter.toVersion version ≥ e.2.2 then some (reservedKindOf e.2.1) else none) =
        specReservedKind version e.1.data.toList := by
    subst hT
    cases version <;> decide +kernel
  have hfound : ∀ x ∈ reservedWords version,
      (T[slot x.toByteArray.toByteSlice]!).1.data.toList = x := by
    subst hT hslot
    cases version <;> decide +kernel
  have hempty : specReservedKind version [] = none := by
    cases version <;> decide
  by_cases h0 : a.toByteSlice.size = 0
  · have : a.data.toList = [] := by
      rw [size_toByteSlice'] at h0
      exact List.eq_nil_of_length_eq_zero h0
    simp [h0, this, hempty]
  · simp only [h0, beq_iff_eq, ite_false]
    generalize he : T[slot a.toByteSlice]! = e
    obtain ⟨word, r, since⟩ := e
    simp only
    by_cases hw : word = a
    · subst hw
      have hne : word.size ≠ 0 := by
        rw [size_toByteSlice'] at h0
        rw [show word.size = word.data.toList.length from Array.length_toList.symm]
        exact h0
      have hmem : (word, r, since) ∈ T.toList := by
        rcases getElem!_mem T (slot word.toByteSlice) with h | h
        · rwa [he] at h
        · rw [he] at h
          simp only [default, Prod.mk.injEq] at h
          exact absurd (by rw [h.1]; rfl) hne
      rcases hgood _ hmem with h | h
      · exact absurd h hne
      · rw [← h]
        have hb : (word.toByteSlice == word.toByteSlice) = true := (toByteSlice_beq _ _).mpr rfl
        by_cases hv : Adapter.toVersion version ≥ since <;> simp [hb, hv]
    · have hb : (word.toByteSlice == a.toByteSlice) = false := by
        cases h : (word.toByteSlice == a.toByteSlice)
        · rfl
        · exact absurd ((toByteSlice_beq _ _).mp h) hw
      simp only [hb, Bool.false_and, Bool.false_eq_true, ite_false, Option.map_none]
      symm
      unfold specReservedKind
      have hnot : a.data.toList ∉ reservedWords version := by
        intro hx
        have := hfound _ hx
        have ha : a.data.toList.toByteArray = a := by
          apply ByteArray.ext
          simp
        rw [ha, he] at this
        exact hw (ByteArray.ext (Array.ext' this))
      simp only [reservedWords, List.map_append, List.mem_append, not_or] at hnot
      simp [hnot.1, hnot.2]

end BSmtLib.Proofs.Lexer.V1Naive

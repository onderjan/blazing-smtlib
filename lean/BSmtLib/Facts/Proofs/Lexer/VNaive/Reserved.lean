module

public import BSmtLib.Facts.Proofs.Lexer.VNaive.Facts
public import BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
import all BSmtLib.Token.Reserved

@[expose] public section

/-!
# Reserved words

`fromBytes_kind`: the library's lookup of reserved words, `Reserved.fromBytes?`, finds exactly
the reserved words of the spec in each version, with the kind the spec gives them. The lookup
reads the table `Reserved.Internal.reservedTable`, whose entries the kernel checks one by one.
-/

open BSmtLibSpec.Facts.Proofs.Lexicon.Unique
open BSmtLibSpec.Lexicon (basicReservedWords commandNames)
open BSmtLibSpec.Regex (chars)
open BSmtLibSpec.Lexer (ReservedKind)
open BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes (toByteArray_toByteSlice toByteSlice_beq
    size_toByteSlice')

namespace BSmtLib.Facts.Proofs.Lexer.VNaive.Reserved

/-- The kind of reserved word of the spec for a reserved word of the library. -/
def reservedKindOf (word : Token.Reserved) : ReservedKind :=
  if word.isCommandName then .command else .general

/-- The kind of reserved word the spec gives the characters in the version, if they are one. -/
def specReservedKind (version : BSmtLibSpec.Lexicon.Version)
    (x : List UInt8) : Option ReservedKind :=
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

/-- The slot of the slice in the table of reserved words, if it has a byte. -/
def slotOf (s : ByteSlice) : Nat :=
  if h : 0 < s.size then (Token.Reserved.Internal.reservedSlot s h).val else 0

/-- The lookup reads the table at the slot of a slice with a byte. -/
theorem fromBytes_eq (s : ByteSlice) (v : Version) (h : s.size ≠ 0) :
    Token.Reserved.fromBytes? s v =
      (let e := Token.Reserved.Internal.reservedTable[slotOf s]!
       if e.1.toByteSlice == s && v ≥ e.2.2 then some e.2.1 else none) := by
  have hpos : 0 < s.size := Nat.pos_of_ne_zero h
  have hlt : (Token.Reserved.Internal.reservedSlot s hpos).val <
      Token.Reserved.Internal.reservedTable.size := by
    rw [Token.Reserved.Internal.size_reservedTable]
    exact Fin.isLt _
  rw [show slotOf s = (Token.Reserved.Internal.reservedSlot s hpos).val from
      dite_eq_left_of_eq_true (eq_true hpos),
    getElem!_pos Token.Reserved.Internal.reservedTable _ hlt]
  simp only [Token.Reserved.fromBytes?, h, ↓reduceDIte]

theorem fromBytes_kind (version : BSmtLibSpec.Lexicon.Version) (a : ByteArray) :
    (Token.Reserved.fromBytes? a.toByteSlice (Lexer.Adapters.toVersion version)).map reservedKindOf
    =
      specReservedKind version a.data.toList := by
  have hgood : ∀ e ∈ Token.Reserved.Internal.reservedTable.toList, e.1.size = 0 ∨
      (if Lexer.Adapters.toVersion version ≥ e.2.2 then some (reservedKindOf e.2.1) else none) =
        specReservedKind version e.1.data.toList := by
    cases version <;> decide +kernel
  have hfound : ∀ x ∈ reservedWords version,
      (Token.Reserved.Internal.reservedTable[slotOf x.toByteArray.toByteSlice]!).1.data.toList =
        x := by
    cases version <;> decide +kernel
  have hempty : specReservedKind version [] = none := by
    cases version <;> decide
  by_cases h0 : a.toByteSlice.size = 0
  · have : a.data.toList = [] := by
      rw [size_toByteSlice'] at h0
      exact List.eq_nil_of_length_eq_zero h0
    simp [Token.Reserved.fromBytes?, h0, this, hempty]
  · rw [fromBytes_eq _ _ h0]
    generalize hT : Token.Reserved.Internal.reservedTable = T at hgood hfound ⊢
    generalize hslot : slotOf = slot at hfound ⊢
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
        by_cases hv : Lexer.Adapters.toVersion version ≥ since <;> simp [hb, hv]
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

end BSmtLib.Facts.Proofs.Lexer.VNaive.Reserved

import BSmtLib.Proofs.Lexer.V3Runs

/-!
# Bytes of a slice

The bytes the lexer over runs takes from a slice in one go (`V3Runs.bytesOf`) are the bytes the
batched lexer takes one at a time, and a run of bytes other than line feeds moves the location
by as many columns.
-/

namespace BSmtLib.Proofs.Lexer.V2BatchedV3Runs

open V1Naive V3Runs

theorem start_add_lt (s : ByteSlice) {i : Nat} (h : i < s.size) :
    s.start + i < s.byteArray.data.size := by
  have := s.stop_le_size_byteArray
  simp only [ByteSlice.size] at h
  simp only [ByteArray.size] at this
  omega

theorem getElem_slice (s : ByteSlice) (i : Nat) (h : i < s.size) :
    s[i] = s.byteArray.data[s.start + i]'(start_add_lt s h) := rfl

theorem data_bytesOf (s : ByteSlice) {i j : Nat} (hij : i ≤ j) (hj : j ≤ s.size) :
    (bytesOf s i j).data = s.byteArray.data.extract (s.start + i) (s.start + j) := by
  have h1 := s.stop_le_size_byteArray
  have h2 := s.start_le_stop
  simp only [ByteSlice.size] at hj
  have ei : min i (s.stop - s.start) = i := by omega
  have ej : min j (s.stop - s.start) = j := by omega
  simp only [bytesOf, ByteSlice.slice, ByteSlice.size, ei, ej]
  split
  · split
    · simp only [ByteSlice.toByteArray, ByteSlice.byteArray, ByteSlice.start, ByteSlice.size,
        ByteSlice.stop, ByteArray.data_extract]
      congr 1; omega
    · omega
  · omega

theorem bytesOf_self (s : ByteSlice) (i : Nat) (h : i ≤ s.size) : bytesOf s i i = .empty := by
  apply ByteArray.ext
  rw [data_bytesOf s (Nat.le_refl _) h]
  rw [show ByteArray.empty.data = #[] from rfl, Array.extract_eq_empty_iff]
  omega

theorem bytesOf_push (s : ByteSlice) {i j : Nat} (hij : i ≤ j) (hj : j < s.size) :
    bytesOf s i (j + 1) = (bytesOf s i j).push s[j] := by
  apply ByteArray.ext
  rw [ByteArray.data_push, data_bytesOf s hij (Nat.le_of_lt hj), data_bytesOf s (by omega) hj,
    getElem_slice]
  have h1 := start_add_lt s hj
  have h3 : s.byteArray.size = s.byteArray.data.size := rfl
  apply Array.ext
  · simp; omega
  · intro k hk1 hk2
    simp only [Array.size_extract, Array.size_push] at hk1 hk2
    rw [Array.getElem_extract, Array.getElem_push]
    split
    · rw [Array.getElem_extract]
    · rename_i hk
      have e : min (s.start + j) s.byteArray.data.size = s.start + j := Nat.min_eq_left (by omega)
      simp only [Array.size_extract, e] at hk
      congr 1
      omega

theorem push_append_bytesOf (x : ByteArray) (s : ByteSlice) {i j : Nat} (hi : i < s.size)
    (hij : i < j) (hj : j ≤ s.size) :
    x.push s[i] ++ bytesOf s (i + 1) j = x ++ bytesOf s i j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + 1 + k := ⟨j - (i + 1), by omega⟩
  induction k with
  | zero =>
    rw [Nat.add_zero, bytesOf_self s _ hj, bytesOf_push s (Nat.le_refl _) (by omega),
      bytesOf_self s _ (by omega)]
    apply ByteArray.ext
    simp
  | succ k ih =>
    have e := congrArg ByteArray.data (ih (by omega) (by omega))
    rw [← Nat.add_assoc, bytesOf_push s (by omega) (by omega),
      bytesOf_push s (by omega) (by omega)]
    apply ByteArray.ext
    simp only [ByteArray.data_append, ByteArray.data_push] at e ⊢
    rw [Array.append_push, Array.append_push, e]

theorem runEnd_le (s : ByteSlice) (p : UInt8 → Bool) (i : Nat) (h : i ≤ s.size) :
    runEnd s p i ≤ s.size := by
  fun_induction runEnd s p i <;> omega

/-! ## Locations -/

theorem afterColumns_zero (location : Location) : afterColumns location 0 = location := rfl

theorem afterColumns_afterByte (location : Location) (c : UInt8) (h : c ≠ 10) (n : Nat) :
    afterColumns (location.afterByte c) n = afterColumns location (n + 1) := by
  unfold Location.afterByte
  split
  · rename_i hc
    exact absurd (beq_iff_eq.mp hc) h
  · simp only [afterColumns, Location.afterColumn]
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm 1 n]

end BSmtLib.Proofs.Lexer.V2BatchedV3Runs

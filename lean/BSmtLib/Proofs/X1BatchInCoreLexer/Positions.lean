import BSmtLib.Proofs.Lexer.X1BatchInCore

/-!
# Positions of the library's lexer and indices of `X1BatchInCore`

The library's lexer reads a slice by `USize` positions in the slice's array (`Input`);
`X1BatchInCore`, which runs the code of the Rust port, reads it by `Nat` indices into the slice
(`Slice`). A position `p` of the input over a slice is the index `p.toNat - slice.start`. This
module relates the reads, the run scans and the contents of the two once, so that the bounds
arithmetic of `USize` stays here.
-/

namespace BSmtLib.Proofs.X1BatchInCoreLexer

open BSmtLib.Lexer (Input runEnd runEndAll endsRun RUN_FLAGS Content)

/-- The input of the library's lexer over the slice, which ends below `USize.size`. -/
def inputOf (slice : ByteSlice) (h : slice.stop < USize.size) : Input :=
  { bytes := slice.byteArray
    start := USize.ofNat slice.start
    stop := USize.ofNatLT slice.stop h
    stop_le := by
      simp only [USize.toNat_ofNatLT]
      exact slice.stop_le_size_byteArray }

theorem ofSlice?_eq (slice : ByteSlice) (h : slice.stop < USize.size) :
    Input.ofSlice? slice = some (inputOf slice h) := by
  simp [Input.ofSlice?, h, inputOf]

theorem ofSlice?_none (slice : ByteSlice) (h : ¬slice.stop < USize.size) :
    Input.ofSlice? slice = none := by
  simp [Input.ofSlice?, h]

section

variable {slice : ByteSlice} {h : slice.stop < USize.size}

@[simp] theorem inputOf_start : (inputOf slice h).start.toNat = slice.start := by
  have := slice.start_le_stop
  simp only [inputOf, USize.toNat_ofNat']
  have := USize.size_eq_two_pow
  exact Nat.mod_eq_of_lt (by omega)

@[simp] theorem inputOf_stop : (inputOf slice h).stop.toNat = slice.stop := by
  simp [inputOf]

@[simp] theorem inputOf_bytes : (inputOf slice h).bytes = slice.byteArray := rfl

/-- The index of the position in the slice. -/
abbrev idx (slice : ByteSlice) (p : USize) : Nat := p.toNat - slice.start

theorem get?_eq (p : USize) (hp : slice.start ≤ p.toNat) :
    (inputOf slice h).get? p = BSmtLib.Proofs.Lexer.Slice.get? slice (idx slice p) := by
  unfold Input.get? BSmtLib.Proofs.Lexer.Slice.get?
  have hsz : slice.size = slice.stop - slice.start := rfl
  by_cases hlt : p < (inputOf slice h).stop
  · have hlt' := USize.lt_iff_toNat_lt.mp hlt
    rw [inputOf_stop] at hlt'
    have hi : idx slice p < slice.size := by simp only [idx]; omega
    have := slice.stop_le_size_byteArray
    simp only [hlt, dite_true, hi, Option.some.injEq]
    show slice.byteArray[p.toNat] = slice.byteArray[slice.start + (p.toNat - slice.start)]
    congr 1
    omega
  · have hge : slice.stop ≤ p.toNat := by
      have := mt USize.lt_iff_toNat_lt.mpr hlt
      rw [inputOf_stop] at this
      omega
    have hi : ¬idx slice p < slice.size := by simp only [idx]; omega
    simp only [hlt, dite_false, hi]

/-- The scan over positions ends at the position of the index where the scan over indices ends,
for tests that agree on the bytes. -/
theorem runEndIn_eq (test : BSmtLib.Lexer.Internal.RunTest) (stops : UInt8 → Bool)
    (htest : ∀ q (hq : q.toNat < slice.byteArray.size),
      test slice.byteArray q hq = stops (slice.byteArray[q.toNat]'hq))
    (p : USize) (hp : slice.start ≤ p.toNat) :
    let r := BSmtLib.Lexer.Internal.runEndIn test slice.byteArray p (inputOf slice h).stop
      (inputOf slice h).stop_le
    slice.start ≤ r.toNat ∧
      idx slice r = BSmtLib.Proofs.Lexer.Slice.runEndBy stops slice (idx slice p) := by
  intro r
  have hsz : slice.size = slice.stop - slice.start := rfl
  have hstop := slice.stop_le_size_byteArray
  simp only [r]
  fun_induction BSmtLib.Lexer.Internal.runEndIn test slice.byteArray p (inputOf slice h).stop
    (inputOf slice h).stop_le with
  | case1 q hlt htrue =>
    have hlt' := USize.lt_iff_toNat_lt.mp hlt
    rw [inputOf_stop] at hlt'
    refine ⟨hp, ?_⟩
    rw [BSmtLib.Proofs.Lexer.Slice.runEndBy]
    have hi : idx slice q < slice.size := by simp only [idx]; omega
    simp only [hi, dite_true]
    rw [htest q (by omega)] at htrue
    have : slice[idx slice q] = slice.byteArray[q.toNat]'(by omega) := by
      show slice.byteArray[slice.start + (q.toNat - slice.start)] = _
      congr 1; omega
    rw [this, htrue]; simp
  | case2 q hlt hfalse ih =>
    have hlt' := USize.lt_iff_toNat_lt.mp hlt
    rw [inputOf_stop] at hlt'
    have e1 := BSmtLib.Lexer.toNat_add_one_of_lt (bound := (inputOf slice h).stop) hlt
    obtain ⟨ih1, ih2⟩ := ih (by rw [e1]; omega)
    refine ⟨ih1, ?_⟩
    rw [ih2]
    conv => rhs; rw [BSmtLib.Proofs.Lexer.Slice.runEndBy]
    have hi : idx slice q < slice.size := by simp only [idx]; omega
    simp only [hi, dite_true]
    rw [htest q (by omega)] at hfalse
    have : slice[idx slice q] = slice.byteArray[q.toNat]'(by omega) := by
      show slice.byteArray[slice.start + (q.toNat - slice.start)] = _
      congr 1; omega
    rw [this]
    simp only [hfalse, Bool.false_eq_true, ite_false]
    congr 1
    simp only [idx, e1]; omega
  | case3 q hge =>
    refine ⟨hp, ?_⟩
    rw [BSmtLib.Proofs.Lexer.Slice.runEndBy]
    have hge' : slice.stop ≤ q.toNat := by
      have := mt USize.lt_iff_toNat_lt.mpr hge
      rw [inputOf_stop] at this
      omega
    have hi : ¬idx slice q < slice.size := by simp only [idx]; omega
    simp only [hi, dite_false]

theorem runEnd_eq (p : USize) (hp : slice.start ≤ p.toNat) (mask : UInt8) :
    slice.start ≤ (BSmtLib.Lexer.runEnd (inputOf slice h) p mask).toNat ∧
      idx slice (BSmtLib.Lexer.runEnd (inputOf slice h) p mask) =
        BSmtLib.Proofs.Lexer.Slice.runEnd slice (idx slice p) mask :=
  runEndIn_eq _ _ (fun _ _ => rfl) p hp

theorem runEndAll_eq (p : USize) (hp : slice.start ≤ p.toNat) (mask : UInt8) :
    slice.start ≤ (BSmtLib.Lexer.runEndAll (inputOf slice h) p mask).toNat ∧
      idx slice (BSmtLib.Lexer.runEndAll (inputOf slice h) p mask) =
        BSmtLib.Proofs.Lexer.Slice.runEndAll slice (idx slice p) mask :=
  runEndIn_eq _ _ (fun _ _ => rfl) p hp

end

end BSmtLib.Proofs.X1BatchInCoreLexer

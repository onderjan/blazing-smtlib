module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Legacy
import all BSmtLib.Lexer.Internal.WRustPort.Slice

@[expose] public section

/-!
# The Rust port's run scans against the naive lexer's bytes

A run scan of the Rust port ends where the run of bytes that pass a test ends (`runEnd`), by
the byte tables (`runEndBy_eq`, `runEnd_eq`, `runEndAll_legacy`), and within the slice
(`runEndBy_le`); `bound_tac` and `fits_tac` show the bounds of indices and content buffers in
the steps.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Runs

open BSmtLib.Lexer.Internal.CharClass (endsRun RUN_FLAGS RUN_DIGIT RUN_SIMPLE_SYMBOL RUN_HEX_DIGIT
    RUN_BINARY_DIGIT RUN_NON_LF_WHITESPACE RUN_QUOTED_PLAIN RUN_STRING_PLAIN RUN_COMMENT_PLAIN)
open BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Bytes
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Tables.Legacy

/-! ## Run scans -/

theorem runEndBy_eq (stops : UInt8 → Bool) (P : UInt8 → Bool) (hP : ∀ c, stops c = !P c)
    (s : ByteSlice) (i : Nat) : Lexer.Internal.WRustPort.Slice.runEndBy stops s i = runEnd s P i :=
    by
  fun_induction Lexer.Internal.WRustPort.Slice.runEndBy stops s i with
  | case1 i h hs =>
    rw [runEnd]
    simp only [h, dite_true]
    rw [hP] at hs
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at hs
    simp [hs]
  | case2 i h hs ih =>
    rw [runEnd]
    simp only [h, dite_true]
    rw [hP] at hs
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hs
    simp [hs, ih]
  | case3 i h =>
    rw [runEnd]
    simp [h]

/-- A run scan of the Rust port with a mask, as a run of bytes that pass a test. -/
theorem runEnd_eq {mask : UInt8} {P : UInt8 → Bool} (hP : ∀ c, endsRun c mask = !P c)
    (s : ByteSlice) (i : Nat) : Lexer.Internal.WRustPort.Slice.runEnd s i mask = runEnd s P i :=
  runEndBy_eq _ P hP s i

/-- A run scan of the Rust port from within the slice ends within it. -/
theorem runEndBy_le (stops : UInt8 → Bool) (s : ByteSlice) {i : Nat} (h : i ≤ s.size) :
    Lexer.Internal.WRustPort.Slice.runEndBy stops s i ≤ s.size := by
  rw [runEndBy_eq stops (fun c => !stops c) (fun c => by simp) s i]
  exact runEnd_le s _ i h

/-- Shows that an index into the slice, possibly the end of a run scan, is within the slice. -/
macro "bound_tac" : tactic =>
  `(tactic| first
    | omega
    | exact runEndBy_le _ _ (by omega))

/-- Shows that the content buffer of a token begun in the step fits its array. -/
macro "fits_tac" : tactic =>
  `(tactic| first
    | exact fits_clear_extendSlice _ _ (by bound_tac)
    | exact fits_clear _
    | exact fits_push (fits_clear _) _
    | exact fits_empty)

/-- The run of the Rust port over a string under version 2.0. -/
theorem runEndAll_legacy (s : ByteSlice) (i : Nat) :
    Lexer.Internal.WRustPort.Slice.runEndAll s i (RUN_STRING_PLAIN ||| RUN_QUOTED_PLAIN) =
      runEnd s isLegacyRun i :=
  runEndBy_eq _ isLegacyRun endsRunAll_legacy s i

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Runs

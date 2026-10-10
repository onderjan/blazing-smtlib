import BSmtLib.Proofs.WRustPortX1BatchInCore.Handed

/-!
# What the adapter's `fedInput` records

Fed the same slices and then, if the input has ended, the end of the input by the adapter,
lexers that correspond record the same tokens and fail alike (`feedInput_eq`), as every call of
their steps, on a slice and at the end of the input, gives the same result with lexers that
correspond again, also where it fails (`run_lexSliceStep_sim`, `run_lexEofStep_sim`).
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Adapter
open BSmtLib.Proofs.Simulation

/-- Coupled computations in `Id` are related values. -/
theorem mcouple_id {α β : Type} {Rel : α → β → Prop} {a : Id α} {b : Id β}
    (h : MCouple Rel a b) : Rel a b := by
  obtain ⟨y, h1, h2⟩ := h
  rw [h1, h2]
  exact y.property

/-- Lexers that correspond, fed the end of the input with the adapter's consumer, record the same
tokens and fail alike. -/
theorem feedEnd_eq (a : WRustPort.ops.Lexer) (b : X1BatchInCore.ops.Lexer) (h : LexRel a b) :
    feedEnd WRustPort.ops a = feedEnd X1BatchInCore.ops b := by
  have hr := mcouple_id (run_lexEofStep_sim (m := Id) (R := Empty) (E := Unit)
    (opsSim_rust_x1BatchInCore collector_consumesAlike)
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast) a b h)
  have e1 : WRustPort.ops.lexEofStep a =
      a.run (Lexer.WRustPort.lexEofStep (ops := Lexer.WRustPort.Rust.ops)
        (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)) := rfl
  have e2 : X1BatchInCore.ops.lexEofStep b =
      b.run (Lexer.WRustPort.lexEofStep (ops := Lexer.X1BatchInCore.ops)
        (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)) := rfl
  simp only [feedEnd, e1, e2]
  revert hr
  generalize a.run (Lexer.WRustPort.lexEofStep (ops := Lexer.WRustPort.Rust.ops)
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)) = ra
  generalize b.run (Lexer.WRustPort.lexEofStep (ops := Lexer.X1BatchInCore.ops)
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)) = rb
  intro hr
  obtain ⟨res, a'⟩ := ra
  obtain ⟨res', b'⟩ := rb
  obtain ⟨e, hl⟩ := hr
  simp only at e hl
  subst e
  rcases res with err | flow
  · show (a'.handler, true) = (b'.handler, true)
    rw [hl.1]
  · cases flow with
    | «continue» =>
      show (a'.handler, false) = (b'.handler, false)
      rw [hl.1]
    | «break» fin => exact fin.value.elim

/-- Lexers that correspond, fed the same slices and then, if the input has ended, the end of the
input with the adapter's consumer, record the same tokens and fail alike. -/
theorem feedInput_eq (ended : Bool) (slices : List Spec.Lexicon.Chars) :
    ∀ (a : WRustPort.ops.Lexer) (b : X1BatchInCore.ops.Lexer), LexRel a b →
      feedInput WRustPort.ops a ended slices = feedInput X1BatchInCore.ops b ended slices := by
  induction slices with
  | nil =>
    intro a b h
    cases ended with
    | false =>
      show (a.handler, false) = (b.handler, false)
      rw [h.1]
    | true => exact feedEnd_eq a b h
  | cons slice slices ih =>
    intro a b h
    have hr := mcouple_id (run_lexSliceStep_sim (m := Id) (R := Empty) (E := Unit)
      (opsSim_rust_x1BatchInCore collector_consumesAlike)
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
      slice.toByteArray.toByteSlice a b h)
    have e1 : WRustPort.ops.lexSliceStep a slice.toByteArray.toByteSlice =
        a.run (Lexer.WRustPort.lexSliceStep (ops := Lexer.WRustPort.Rust.ops)
          (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
          slice.toByteArray.toByteSlice) := rfl
    have e2 : X1BatchInCore.ops.lexSliceStep b slice.toByteArray.toByteSlice =
        b.run (Lexer.WRustPort.lexSliceStep (ops := Lexer.X1BatchInCore.ops)
          (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
          slice.toByteArray.toByteSlice) := rfl
    simp only [feedInput, e1, e2]
    revert hr
    generalize a.run (Lexer.WRustPort.lexSliceStep (ops := Lexer.WRustPort.Rust.ops)
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
      slice.toByteArray.toByteSlice) = ra
    generalize b.run (Lexer.WRustPort.lexSliceStep (ops := Lexer.X1BatchInCore.ops)
      (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
      slice.toByteArray.toByteSlice) = rb
    intro hr
    obtain ⟨res, a'⟩ := ra
    obtain ⟨res', b'⟩ := rb
    obtain ⟨e, hl⟩ := hr
    simp only at e hl
    subst e
    rcases res with err | flow
    · show (a'.handler, true) = (b'.handler, true)
      rw [hl.1]
    · cases flow with
      | «continue» => exact ih a' b' hl
      | «break» fin => exact fin.value.elim

/-- The two lexers, fed by the adapter slices and then, if the input has ended, the end of the
input, record the same tokens and fail alike. -/
theorem fedInput_eq (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars)
    (ended : Bool) :
    fedInput WRustPort.ops version slices ended =
      fedInput X1BatchInCore.ops version slices ended := by
  simp only [fedInput]
  have e := feedInput_eq ended slices (WRustPort.ops.new { handed := [] } (toVersion version))
    (X1BatchInCore.ops.new { handed := [] } (toVersion version)) (new_rel _ _)
  exact congrArg (fun p : Collector × Bool => ({ handed := p.1.handed, failed := p.2 } :
    Spec.Lexer.Fed)) e

end BSmtLib.Proofs.WRustPortX1BatchInCore

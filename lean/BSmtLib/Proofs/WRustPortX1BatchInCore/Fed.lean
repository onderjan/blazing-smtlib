import BSmtLib.Proofs.WRustPortX1BatchInCore.Handed

/-!
# What the adapter's `fed` records

Fed the same slices before the end of the input by the adapter, lexers that correspond record
the same tokens and fail alike (`feedSlices_eq`), as every call of their steps gives the same
result with lexers that correspond again, also where it fails (`run_lexSliceStep_sim`).
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

/-- Lexers that correspond, fed the same slices before the end of the input with the adapter's
consumer, record the same tokens and fail alike. -/
theorem feedSlices_eq (slices : List Spec.Lexicon.Chars) :
    ∀ (a : WRustPort.ops.Lexer) (b : X1BatchInCore.ops.Lexer), LexRel a b →
      feedSlices WRustPort.ops a slices = feedSlices X1BatchInCore.ops b slices := by
  induction slices with
  | nil =>
    intro a b h
    show (a.handler, false) = (b.handler, false)
    rw [h.1]
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
    simp only [feedSlices, e1, e2]
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

/-- The two lexers, fed slices by the adapter before the end of the input, record the same tokens
and fail alike. -/
theorem fed_eq (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars) :
    fed WRustPort.ops version slices = fed X1BatchInCore.ops version slices := by
  simp only [fed]
  have e := feedSlices_eq slices (WRustPort.ops.new { handed := [] } (toVersion version))
    (X1BatchInCore.ops.new { handed := [] } (toVersion version)) (new_rel _ _)
  exact congrArg (fun p : Collector × Bool => ({ handed := p.1.handed, failed := p.2 } :
    Spec.Lexer.Fed)) e

end BSmtLib.Proofs.WRustPortX1BatchInCore

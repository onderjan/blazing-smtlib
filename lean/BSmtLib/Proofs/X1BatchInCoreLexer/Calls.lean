import BSmtLib.Proofs.X1BatchInCoreLexer.Eof
import BSmtLib.Proofs.X1BatchInCoreLexer.Slice

/-!
# The steps of the calls of the library's lexer and of `X1BatchInCore`

`lexEofStep` and `lexSliceStep` are coupled from related states, step by step with the rules of
`Outer`. The end of the input is simulated exactly from a state with a known base (`coreMap`),
and it sets the base before it reads it, so it is coupled from every related state; the loop
over a slice is coupled in `Slice`.
-/

namespace BSmtLib.Proofs.X1BatchInCoreLexer

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type} [Consume H R E]
  [∀ batch, ConsumeFrom H (BatchCursor batch) m]

theorem lexEofInner_couple :
    Coupled Eq (BSmtLib.Lexer.Internal.lexEofInner (H := H) (m := m) (R := R) (E := E))
      Lexer.WRustPort.lexEofInner :=
  Coupled.of_exact (coreMap 0) (coreMap 0) id lexEofInner_exact
    (fun c x h hx => by rw [eq_wb hx]; rfl) (rel_coreMap 0) fun _ => rfl

/-- The end of `lexEofStep`: the inner step, then the reset or the failure. -/
local macro "eof_tail" : tactic => `(tactic| (
  refine Coupled.bind (executeStep_couple lexEofInner_couple) fun a b e => ?_
  subst e
  rcases a with failure | flow
  · exact Coupled.ite Iff.rfl
      (fun _ => Coupled.bind reset_couple fun _ _ _ => Coupled.pure rfl)
      fun _ => Coupled.bind (failCall_couple _ _ _) fun _ _ e => Coupled.pure (by rw [e])
  · exact Coupled.bind reset_couple fun _ _ _ => Coupled.pure rfl))

theorem lexEofStep_couple (abandon recover : Location → StateT H m Unit) :
    Coupled Eq (BSmtLib.Lexer.Internal.lexEofStep (R := R) (E := E) abandon recover)
      (Lexer.WRustPort.lexEofStep abandon recover) := by
  unfold BSmtLib.Lexer.Internal.lexEofStep Lexer.WRustPort.lexEofStep
  refine Coupled.bind Coupled.get fun c x hx => ?_
  rw [eq_wb hx]
  dsimp only
  refine Coupled.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  refine Coupled.bind (Coupled.modify fun c x hx => ?_) fun _ _ _ => ?_
  · rw [eq_wb hx]
    rfl
  · refine Coupled.bind Coupled.get fun c x hx => ?_
    rw [currentLocation_eq hx]
    refine Coupled.bind (Coupled.lift _) fun _ _ e => ?_
    subst e
    eof_tail
  · eof_tail

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type} [Consume H R E]
  [∀ batch, ConsumeFrom H (BatchCursor batch) m]

theorem stop_slice_lt {slice : ByteSlice} (h : slice.stop < USize.size) (k : Nat) :
    (slice.slice k).stop < USize.size := by
  have := slice.start_le_stop
  have hs : slice.size = slice.stop - slice.start := rfl
  unfold ByteSlice.slice
  dsimp only
  split
  · split
    · show slice.start + min slice.size slice.size < USize.size
      omega
    · show slice.start + min slice.size slice.size < USize.size
      omega
  · show slice.start < USize.size
    omega

set_option hygiene false in
/-- The end of `lexSliceStep`: the inner step on the slice, which ends below `USize.size` by
`hb`, then the failure, if it fails. -/
local macro "slice_tail " hb:term:max : tactic => `(tactic| (
  unfold BSmtLib.Lexer.Internal.lexFitting
  rw [ofSlice_eq _ $hb]
  refine Coupled.bind (lexSliceInner_couple _ $hb) fun a b e => ?_
  subst e
  rcases a with failure | held
  · exact Coupled.bind (failCall_couple _ _ _) fun _ _ e => Coupled.pure (by rw [e])
  · exact Coupled.pure rfl))

theorem lexSliceStep_couple (abandon recover : Location → StateT H m Unit) (slice : ByteSlice)
    (h : slice.stop < USize.size) :
    Coupled Eq (BSmtLib.Lexer.Internal.lexSliceStep (R := R) (E := E) abandon recover slice)
      (Lexer.WRustPort.lexSliceStep abandon recover slice) := by
  unfold BSmtLib.Lexer.Internal.lexSliceStep
  rw [dite_eq_left_of_eq_true (eq_true h)]
  unfold BSmtLib.Lexer.Internal.lexSliceFitting Lexer.WRustPort.lexSliceStep
  refine Coupled.bind Coupled.get fun c x hx => ?_
  rw [eq_wb hx]
  refine Coupled.ite Iff.rfl (fun _ => Coupled.pure rfl) fun _ => ?_
  refine Coupled.bind Coupled.get fun c x hx => ?_
  rw [eq_wb hx]
  dsimp only
  rw [show (wb x.base c).recoveryState = c.recoveryState from rfl]
  rcases c.recoveryState with _ | skip
  · slice_tail h
  · refine Coupled.ite Iff.rfl (fun _ => Coupled.pure rfl) fun _ => ?_
    refine Coupled.bind (skipSlice_couple _ _) fun a b e => ?_
    subst e
    rcases a with _ | skipped
    · exact Coupled.pure rfl
    · refine Coupled.bind (Coupled.modify fun c x hx => by rw [eq_wb hx]; rfl) fun _ _ _ => ?_
      refine Coupled.bind Coupled.get fun c x hx => ?_
      rw [currentLocation_eq hx]
      refine Coupled.bind (Coupled.lift _) fun _ _ e => ?_
      subst e
      slice_tail (stop_slice_lt h skipped)

end

end BSmtLib.Proofs.X1BatchInCoreLexer

import BSmtLib.Proofs.X2ContentsLexer.Eof
import BSmtLib.Proofs.X2ContentsLexer.Slice

/-!
# The steps of the calls of the library's lexer and of the lexer with the content buffer

`lexEofStep` and `lexSliceStep` are coupled from related states, step by step with the rules of
`Outer`. The end of the input is simulated exactly from a state with a known base (`coreMap`),
and it sets the base before it reads it, so it is coupled from every related state; the loop
over a slice is coupled in `Slice`.
-/

namespace BSmtLib.Proofs.X2ContentsLexer

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type} [Consume H m R E]

theorem lexEofInner_couple :
    Couple Eq (BSmtLib.Lexer.Internal.lexEofInner (H := H) (m := m) (R := R) (E := E))
      Lexer.X2Contents.lexEofInner :=
  Couple.of_exact (coreMap 0) (coreMap 0) id lexEofInner_exact
    (fun c x h hx => by rw [eq_wb hx]; rfl) (rel_coreMap 0) fun _ => rfl

/-- The end of `lexEofStep`: the inner step, then the reset or the failure. -/
local macro "eof_tail" : tactic => `(tactic| (
  refine Couple.bind (executeStep_couple lexEofInner_couple) fun a b e => ?_
  subst e
  rcases a with failure | flow
  · exact Couple.ite Iff.rfl
      (fun _ => Couple.bind reset_couple fun _ _ _ => Couple.pure rfl)
      fun _ => Couple.bind (failCall_couple _ _ _) fun _ _ e => Couple.pure (by rw [e])
  · exact Couple.bind reset_couple fun _ _ _ => Couple.pure rfl))

theorem lexEofStep_couple (abandon recover : Location → StateT H m Unit) :
    Couple Eq (BSmtLib.Lexer.Internal.lexEofStep (R := R) (E := E) abandon recover)
      (Lexer.X2Contents.lexEofStep abandon recover) := by
  unfold BSmtLib.Lexer.Internal.lexEofStep Lexer.X2Contents.lexEofStep
  refine Couple.bind Couple.get fun c x hx => ?_
  rw [eq_wb hx]
  refine Couple.ite Iff.rfl (fun _ => Couple.bind reset_couple fun _ _ _ => Couple.pure rfl)
    fun _ => ?_
  refine Couple.bind Couple.get fun c x hx => ?_
  rw [eq_wb hx]
  dsimp only
  refine Couple.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  refine Couple.bind (Couple.modify fun c x hx => ?_) fun _ _ _ => ?_
  · rw [eq_wb hx]
    rfl
  · refine Couple.bind Couple.get fun c x hx => ?_
    rw [currentLocation_eq hx]
    refine Couple.bind (Couple.lift _) fun _ _ e => ?_
    subst e
    eof_tail
  · eof_tail

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type} [Consume H m R E]

/-- A part of a slice ends where the slice does or before. -/
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
`hb`, then the failure or the discarding after a break. -/
local macro "slice_tail " hb:term:max : tactic => `(tactic| (
  refine Couple.bind Couple.get fun c x hx => ?_
  rw [eq_wb hx, ofSlice?_eq _ $hb]
  dsimp only
  refine Couple.bind (executeStep_couple (lexSliceInner_couple _ $hb)) fun a b e => ?_
  subst e
  rcases a with failure | flow
  · exact Couple.bind (failCall_couple _ _ _) fun _ _ e => Couple.pure (by rw [e])
  · cases flow
    · exact Couple.pure rfl
    · refine Couple.bind (Couple.modify fun c x hx => by rw [eq_wb hx]; rfl) fun _ _ _ => ?_
      exact Couple.bind (discardBytes_couple _) fun _ _ _ => Couple.pure rfl))

theorem lexSliceStep_couple (abandon recover : Location → StateT H m Unit) (slice : ByteSlice)
    (h : slice.stop < USize.size) :
    Couple Eq (BSmtLib.Lexer.Internal.lexSliceStep (R := R) (E := E) abandon recover slice)
      (Lexer.X2Contents.lexSliceStep abandon recover slice) := by
  unfold BSmtLib.Lexer.Internal.lexSliceStep Lexer.X2Contents.lexSliceStep
  refine Couple.bind Couple.get fun c x hx => ?_
  rw [eq_wb hx]
  refine Couple.ite Iff.rfl (fun _ => Couple.bind (discardBytes_couple _) fun _ _ _ =>
    Couple.pure rfl) fun _ => ?_
  refine Couple.bind Couple.get fun c x hx => ?_
  rw [eq_wb hx]
  dsimp only
  rw [show (wb x.base c).recoveryState = c.recoveryState from rfl]
  rcases c.recoveryState with _ | skip
  · slice_tail h
  · refine Couple.ite Iff.rfl (fun _ => Couple.pure rfl) fun _ => ?_
    refine Couple.bind (skipSlice_couple _ _) fun a b e => ?_
    subst e
    rcases a with _ | skipped
    · exact Couple.pure rfl
    · refine Couple.bind (Couple.modify fun c x hx => by rw [eq_wb hx]; rfl) fun _ _ _ => ?_
      refine Couple.bind Couple.get fun c x hx => ?_
      rw [currentLocation_eq hx]
      refine Couple.bind (Couple.lift _) fun _ _ e => ?_
      subst e
      slice_tail (stop_slice_lt h skipped)

end

end BSmtLib.Proofs.X2ContentsLexer

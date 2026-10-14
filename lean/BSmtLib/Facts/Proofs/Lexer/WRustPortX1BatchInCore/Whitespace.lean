import BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Finish

/-!
# The whitespace run

A whitespace run that the consumer takes is lexed by its own loop (`startWhitespaceFrom`), which
marks the line feeds it passes and puts the token into the batch the loop of the normal state
holds; both runs do the same, with the batches the loops hold.
-/

namespace BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Whitespace

open BSmtLib.Facts.Proofs.Lexer.Simulation.Relation
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)
open BSmtLib.Lexer.Internal.WRustPort.Slice (get? runEnd)
open BSmtLib.Lexer.Internal.WRustPort (Ops)
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Held
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Ops

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]
  {floor : Option Nat} {low : Nat} {strict : Bool} {o₁ o₂ : Ops H m R E}
  {LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop}

/-- What the whitespace run gives back: the index after it and the batches held by the loops,
with the states' batches without tokens; or nothing, where the run reaches the end of the slice
and the batches are put back into the states. -/
def WsQ (strict : Bool) {α β : Type} (val : α → Nat × Token.TokenBatch)
    (val' : β → Nat × Token.TokenBatch)
    (a : Option α) (b : Option β) (s t : Core.St floor low) : Prop :=
  match a, b with
  | none, none => Core.SRb strict s t
  | some x, some y => (val x).1 = (val' y).1 ∧ Core.HR (val x).2 (val' y).2 ∧ Core.SR0 s t
  | _, _ => False

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem startWhitespaceFrom_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (offset base index : Nat) (start : Span.Location) :
    ∀ k (b b' : Token.TokenBatch) («end» : Nat), input.size - «end» = k → Core.HR b b' →
      ∀ hframe hstart hend hrun hbatch hbatch',
      Core.LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Core.SR0
        (WsQ strict (·.val) (·.val))
        (Lexer.Internal.WRustPort.startWhitespaceFrom
            (ops := o₁) input offset base index «end» start b
          hframe hstart hend hrun hbatch)
        (Lexer.Internal.WRustPort.startWhitespaceFrom
            (ops := o₂) input offset base index «end» start b'
          hframe hstart hend hrun hbatch') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro b b' e hk hb hframe hstart hend hrun hbatch hbatch'
  rw [Lexer.Internal.WRustPort.startWhitespaceFrom.eq_def (ops := o₁),
    Lexer.Internal.WRustPort.startWhitespaceFrom.eq_def (ops := o₂)]
  dsimp only
  split
  · rename_i c h1
    have := Lexer.Internal.WRustPort.Slice.lt_size_of_get? h1
    have hle := Lexer.Internal.WRustPort.Slice.le_runEnd input e
        Lexer.CharClass.RUN_NON_LF_WHITESPACE
    refine SimR.dite Iff.rfl (fun hnl _ => ?_) fun hnl _ => ?_
    · exact SimR.seq (Core.markLineFeedAt_sim0 _) (ih _ (by omega) b b' _ rfl hb _ _ _ _ _ _)
    · refine Core.SimR.of_sre fun l ls => SimR.bind
        (pushBorrowed_sim ho l ls input b b' hb _ _ _ _ _
        _ _ _ _ _ _ _ _ _) fun x y => SimR.pure fun s t h => ⟨rfl, h.1, h.2.1.1, h.2.2⟩
  · refine Core.SimR.of_sre fun l ls => ?_
    exact SimR.seq (Core.extendContent_sim l ls _ _ _ _) (SimR.seq (SimR.pre (fun s t h => h.1)
      (Core.leavePending_sim l ls _ _ _ _ _ _ _ hb _ _ _ _ _ _ _ _))
      (SimR.pure fun s t h => ⟨h.1.1, h.2⟩))

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem startWhitespace_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (offset base index : Nat) (b b' : Token.TokenBatch) (hb : Core.HR b b')
    (hrun hframe hindex hbatch hbatch') :
    Core.LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) Core.SR0
      (WsQ strict (·.val) (·.val))
      (Lexer.Internal.WRustPort.startWhitespace (ops := o₁) input offset base index b hrun hframe
          hindex
        hbatch)
      (Lexer.Internal.WRustPort.startWhitespace (ops := o₂) input offset base index b' hrun hframe
          hindex
        hbatch') := by
  unfold Lexer.Internal.WRustPort.startWhitespace
  refine Core.SimR.of_sre fun l ls => SimR.bind (Core.startToken_sim l ls _ offset base index _ _)
    fun a a' => ?_
  obtain ⟨a, ha⟩ := a
  obtain ⟨a', ha'⟩ := a'
  refine SimR.of_fact' (Er := Core.ErS strict) fun (e : a = a') => ?_
  subst e
  exact SimR.pre (fun s t h => ⟨h.1.1.1, h.1.2⟩)
    (startWhitespaceFrom_sim ho input offset base index a _ b b' index rfl hb _ _ _ _ _ _)

end

end BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Whitespace

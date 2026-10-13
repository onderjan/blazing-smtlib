import BSmtLib.Proofs.WRustPortX1BatchInCore.Finish

/-!
# The whitespace run

A whitespace run that the consumer takes is lexed by its own loop (`startWhitespaceFrom`), which
marks the line feeds it passes and puts the token into the batch the loop of the normal state
holds; both runs do the same, with the batches the loops hold.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)
open BSmtLib.Proofs.Lexer.Slice (get? runEnd)
open BSmtLib.Proofs.Lexer.WRustPort (Ops)

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H R E]
  [∀ batch, ConsumeFrom H (BatchCursor batch) m]
  {floor : Option Nat} {low : Nat} {strict : Bool} {o₁ o₂ : Ops H m R E}
  {LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop}

/-- What the whitespace run gives back: the index after it and the batches held by the loops,
with the states' batches without tokens; or nothing, where the run reaches the end of the slice
and the batches are put back into the states. -/
def WsQ (strict : Bool) {α β : Type} (val : α → Nat × TokenBatch) (val' : β → Nat × TokenBatch)
    (a : Option α) (b : Option β) (s t : St floor low) : Prop :=
  match a, b with
  | none, none => SRb strict s t
  | some x, some y => (val x).1 = (val' y).1 ∧ HR (val x).2 (val' y).2 ∧ SR0 s t
  | _, _ => False

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem startWhitespaceFrom_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (offset base index : Nat) (start : Location) :
    ∀ k (b b' : TokenBatch) («end» : Nat), input.size - «end» = k → HR b b' →
      ∀ hframe hstart hend hrun hbatch hbatch',
      LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) SR0
        (WsQ strict (·.val) (·.val))
        (Lexer.WRustPort.startWhitespaceFrom (ops := o₁) input offset base index «end» start b
          hframe hstart hend hrun hbatch)
        (Lexer.WRustPort.startWhitespaceFrom (ops := o₂) input offset base index «end» start b'
          hframe hstart hend hrun hbatch') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro b b' e hk hb hframe hstart hend hrun hbatch hbatch'
  rw [Lexer.WRustPort.startWhitespaceFrom.eq_def (ops := o₁),
    Lexer.WRustPort.startWhitespaceFrom.eq_def (ops := o₂)]
  dsimp only
  split
  · rename_i c h1
    have := Lexer.Slice.lt_size_of_get? h1
    have hle := Lexer.Slice.le_runEnd input e Lexer.RUN_NON_LF_WHITESPACE
    refine SimR.dite Iff.rfl (fun hnl _ => ?_) fun hnl _ => ?_
    · exact SimR.seq (markLineFeedAt_sim0 _) (ih _ (by omega) b b' _ rfl hb _ _ _ _ _ _)
    · refine SimR.of_sre fun l ls => SimR.bind (pushBorrowed_sim ho l ls input b b' hb _ _ _ _ _
        _ _ _ _ _ _ _ _ _) fun x y => SimR.pure fun s t h => ⟨rfl, h.1, h.2.1.1, h.2.2⟩
  · refine SimR.of_sre fun l ls => ?_
    exact SimR.seq (extendContent_sim l ls _ _ _ _) (SimR.seq (SimR.pre (fun s t h => h.1)
      (leavePending_sim l ls _ _ _ _ _ _ _ hb _ _ _ _ _ _ _ _))
      (SimR.pure fun s t h => ⟨h.1.1, h.2⟩))

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem startWhitespace_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (offset base index : Nat) (b b' : TokenBatch) (hb : HR b b')
    (hrun hframe hindex hbatch hbatch') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) SR0
      (WsQ strict (·.val) (·.val))
      (Lexer.WRustPort.startWhitespace (ops := o₁) input offset base index b hrun hframe hindex
        hbatch)
      (Lexer.WRustPort.startWhitespace (ops := o₂) input offset base index b' hrun hframe hindex
        hbatch') := by
  unfold Lexer.WRustPort.startWhitespace
  refine SimR.of_sre fun l ls => SimR.bind (startToken_sim l ls _ offset base index _ _)
    fun a a' => ?_
  obtain ⟨a, ha⟩ := a
  obtain ⟨a', ha'⟩ := a'
  refine SimR.of_fact' (Er := ErS strict) fun (e : a = a') => ?_
  subst e
  exact SimR.pre (fun s t h => ⟨h.1.1.1, h.1.2⟩)
    (startWhitespaceFrom_sim ho input offset base index a _ b b' index rfl hb _ _ _ _ _ _)

end

end BSmtLib.Proofs.WRustPortX1BatchInCore

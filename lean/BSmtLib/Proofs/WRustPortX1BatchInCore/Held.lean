import BSmtLib.Proofs.WRustPortX1BatchInCore.Ops

/-!
# The batch held by the loop of the normal state

The loop of the normal state holds the batch, appends the tokens of the fast path (`pushFast`)
and of the slow path (`pushBorrowed`) to it, hands it over when it is full (`flushHeld`), and puts
it back into the lexer state where the loop ends (`leave`, `leavePending`). The batches the two
loops hold agree, have the same array of contents (the slice's) and are below the capacity
(`HR`); while the loops hold them, the batches in the two lexer states have no tokens (`SRE`).
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)
open BSmtLib.Proofs.Lexer.WRustPort (Ops)

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H R E]
  [∀ batch, ConsumeFrom H (BatchCursor batch) m]
  {floor : Option Nat} {low : Nat} {strict : Bool} {o₁ o₂ : Ops H m R E}
  {LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop}

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem pushBorrowed_sim (ho : OpsSim o₁ o₂ LRel) (l ls : Nat) (input : ByteSlice)
    (b b' : TokenBatch) (hb : HR b b') (offset base : Nat) (ty : TokenCategory)
    (contentStart contentStop : Nat) (start : Location) (tokenEnd : Nat)
    (hty hafter hend hfloor hafter' hend' hfloor') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRE l ls)
      (PushQ l ls (·.val) (·.val))
      (Lexer.WRustPort.pushBorrowed (ops := o₁) input b offset base ty contentStart contentStop
        start tokenEnd hty hafter hend hfloor)
      (Lexer.WRustPort.pushBorrowed (ops := o₂) input b' offset base ty contentStart contentStop
        start tokenEnd hty hafter' hend' hfloor') := by
  unfold Lexer.WRustPort.pushBorrowed
  refine getCore_bind_P fun s t h => ?_
  dsimp only
  rw [← h.1.1.line, ← h.1.1.lineStart]
  have hpush := hb.agree.pushLocated hb.bytes ty (input.start + contentStart)
    (input.start + contentStop) start
    { offset := offset + (tokenEnd - base), line := s.val.line,
      column := offset + (tokenEnd - base) - s.val.lineStart } hafter (.inl hend) hafter'
      (.inl hend')
  refine SimR.ite (by simp only [beq_iff_eq, hpush.len]) (fun _ => ?_) fun hne => ?_
  · refine SimR.bind (ho.flushHeld l ls _ _ hpush hb.bytes _ _ _) fun x y => ?_
    obtain ⟨x, hx1, hx2⟩ := x
    obtain ⟨y, hy1, hy2⟩ := y
    exact SimR.pure fun s' t' h' => ⟨⟨h'.1, h'.2.1, by rw [h'.2.2.1]; exact zero_lt_capacity⟩,
      h'.2.2.2⟩
  · refine SimR.pure fun s' t' h' => ?_
    refine ⟨⟨hpush, hb.bytes, ?_⟩, h'⟩
    have := hb.capacity
    simp only [beq_iff_eq] at hne
    show b.len + 1 < BATCH_CAPACITY
    have : b.len + 1 ≠ BATCH_CAPACITY := hne
    omega


end

end BSmtLib.Proofs.WRustPortX1BatchInCore

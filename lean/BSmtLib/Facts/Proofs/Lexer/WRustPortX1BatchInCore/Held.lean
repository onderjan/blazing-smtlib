module

public import BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Ops
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Token

@[expose] public section

/-!
# The batch held by the loop of the normal state

The loop of the normal state holds the batch, appends the tokens of the fast path (`pushFast`)
and of the slow path (`pushBorrowed`) to it, hands it over when it is full (`flushHeld`), and puts
it back into the lexer state where the loop ends (`leave`, `leavePending`). The batches the two
loops hold agree, have the same array of contents (the slice's) and are below the capacity
(`HR`); while the loops hold them, the batches in the two lexer states have no tokens (`SRE`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Held

open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)
open BSmtLib.Lexer.Internal.WRustPort (Ops)
open BSmtLib.Facts.Proofs.Lexer.Simulation.Relation
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Ops

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]
  {floor : Option Nat} {low : Nat} {strict : Bool} {o₁ o₂ : Ops H m R E}
  {LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop}

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem pushBorrowed_sim (ho : OpsSim o₁ o₂ LRel) (l ls : Nat) (input : ByteSlice)
    (b b' : Token.TokenBatch) (hb : Core.HR b b') (offset base : Nat) (ty : Token.TokenCategory)
    (contentStart contentStop : Nat) (start : Span.Location) (tokenEnd : Nat)
    (hty hafter hend hfloor hafter' hend' hfloor') :
    Core.LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low)
        (Core.SRE l ls)
      (Core.PushQ l ls (·.val) (·.val))
      (Lexer.Internal.WRustPort.pushBorrowed (ops := o₁) input b offset base ty contentStart
          contentStop
        start tokenEnd hty hafter hend hfloor)
      (Lexer.Internal.WRustPort.pushBorrowed (ops := o₂) input b' offset base ty contentStart
          contentStop
        start tokenEnd hty hafter' hend' hfloor') := by
  unfold Lexer.Internal.WRustPort.pushBorrowed
  refine Core.getCore_bind_P fun s t h => ?_
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
    exact SimR.pure fun s' t' h' => ⟨⟨h'.1, h'.2.1, by rw [h'.2.2.1]; exact Core.zero_lt_capacity⟩,
      h'.2.2.2⟩
  · refine SimR.pure fun s' t' h' => ?_
    refine ⟨⟨hpush, hb.bytes, ?_⟩, h'⟩
    have := hb.capacity
    simp only [beq_iff_eq] at hne
    show b.len + 1 < BATCH_CAPACITY
    have : b.len + 1 ≠ BATCH_CAPACITY := hne
    omega


end

end BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Held

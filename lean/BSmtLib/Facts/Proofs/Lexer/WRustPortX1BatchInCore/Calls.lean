module

public import BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Top
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The calls of the lexers

A lexer holds its consumer and its lexer state (`WRustPort.Lexer`); a call runs a step of `Top`
on them (`Lexer.run`). Lexers with the same consumer and lexer states related by `TopRel`
correspond (`LexRel`).

Take two lexers that correspond, and two structures of operations that simulate each other. The
two runs of the step of a call on a slice (`lexSliceStep`), or of one at the end of the input
(`lexEofStep`), over these operations are then the projections of one computation of the same
results with lexers that correspond again (`MCouple`), whether the call succeeds or fails
(`run_lexSliceStep_sim`, `run_lexEofStep_sim`).
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Calls

open BSmtLib.Facts.Proofs.Lexer.Simulation.Couple
open BSmtLib.Lexer.Internal.WRustPort (Ops)
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Ops
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Top

/-- The two lexers correspond: the same consumer, lexer states related by `TopRel`, and the same
held result. -/
def LexRel {H R E : Type} [Token.Consume H R E] {recovery : Type}
    (a b : Lexer.Internal.WRustPort.Lexer H recovery) : Prop :=
  a.handler = b.handler ∧ TopRel a.core b.core ∧ a.held = b.held

/-- The runs of a step on two lexers give the same result, with lexers that correspond. -/
def RunRel {H R E α : Type} [Token.Consume H R E] {recovery : Type}
    (a b : α × Lexer.Internal.WRustPort.Lexer H recovery) : Prop :=
  a.1 = b.1 ∧ LexRel a.2 b.2

section

variable {H R E : Type} [Token.Consume H R E] {m : Type → Type} [Monad m] [LawfulMonad m]
  {recovery : Type} {α β : Type}

theorem run_couple {Q : α → β → Core → Core → Prop} {step : Lexer.Internal.WRustPort.InnerM H m α}
    {step' : Lexer.Internal.WRustPort.InnerM H m β} (hs : ISim TopRel Q step step')
    (self self' : Lexer.Internal.WRustPort.Lexer H recovery) (h : LexRel self self') :
    MCouple (fun a b => Q a.1 b.1 a.2.core b.2.core ∧ a.2.handler = b.2.handler ∧
        a.2.held = b.2.held)
      (self.run step) (self'.run step') := by
  obtain ⟨handler, core, held⟩ := self
  obtain ⟨handler', core', held'⟩ := self'
  obtain ⟨hh, ht, hd⟩ := h
  dsimp only at hh ht hd
  subst hh hd
  obtain ⟨y, h1, h2⟩ := hs core core' ht handler
  refine ⟨(fun z => ⟨((z.val.1.1.1, ⟨z.val.1.2, z.val.1.1.2, held⟩),
    (z.val.2.1.1, ⟨z.val.2.2, z.val.2.1.2, held⟩)), ⟨z.property.1, z.property.2, rfl⟩⟩) <$> y,
    ?_, ?_⟩
  · simp only [Lexer.Internal.WRustPort.Lexer.run, h1, map_eq_pure_bind, bind_assoc, pure_bind]
  · simp only [Lexer.Internal.WRustPort.Lexer.run, h2, map_eq_pure_bind, bind_assoc, pure_bind]

/-- A step with equal results from states related by `TopRel`, run on lexers that correspond. -/
theorem run_couple_top {step step' : Lexer.Internal.WRustPort.InnerM H m α}
    (hs : ISim TopRel TopQ step step') (self self' : Lexer.Internal.WRustPort.Lexer H recovery)
    (h : LexRel self self') :
    MCouple RunRel (self.run step) (self'.run step') :=
  MCouple.mono (fun _ _ h => ⟨h.1.1, h.2.1, h.1.2, h.2.2⟩) (run_couple hs self self' h)

end

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (LexerCursor batch) m]
  {recovery : Type} {o₁ o₂ : Ops H m R E}
  {LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop}

omit [∀ batch, Token.ConsumeFrom H (LexerCursor batch) m] in
/-- Over operations that simulate each other, the step of a call on a slice, run on lexers that
correspond, gives the same result with lexers that correspond again, also where it fails. -/
theorem run_lexSliceStep_sim (ho : OpsSim o₁ o₂ LRel)
    (abandon recover : Span.Location → StateT H m Unit) (slice : ByteSlice)
    (self self' : Lexer.Internal.WRustPort.Lexer H recovery) (h : LexRel self self') :
    MCouple RunRel
      (self.run (Lexer.Internal.WRustPort.lexSliceStep (ops := o₁) (R := R)
          (E := E) abandon recover slice))
      (self'.run (Lexer.Internal.WRustPort.lexSliceStep (ops := o₂) abandon recover slice)) :=
  run_couple_top (lexSliceStep_sim ho abandon recover slice) self self' h

omit [∀ batch, Token.ConsumeFrom H (LexerCursor batch) m] in
/-- Over operations that simulate each other, the step of a call at the end of the input, run on
lexers that correspond, gives the same result with lexers that correspond again, also where it
fails. -/
theorem run_lexEofStep_sim (ho : OpsSim o₁ o₂ LRel)
    (abandon recover : Span.Location → StateT H m Unit)
    (self self' : Lexer.Internal.WRustPort.Lexer H recovery) (h : LexRel self self') :
    MCouple RunRel
      (self.run (Lexer.Internal.WRustPort.lexEofStep (ops := o₁) (R := R) (E := E) abandon recover))
      (self'.run (Lexer.Internal.WRustPort.lexEofStep (ops := o₂) abandon recover)) :=
  run_couple_top (lexEofStep_sim ho abandon recover) self self' h

end

end BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Calls

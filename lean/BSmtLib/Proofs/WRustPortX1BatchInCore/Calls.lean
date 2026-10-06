import BSmtLib.Proofs.WRustPortX1BatchInCore.Top

/-!
# The calls of the lexers

A lexer holds its consumer and its lexer state (`WRustPort.Lexer`); a call runs a step of `Top`
on them (`Lexer.run`). Lexers with the same consumer and lexer states related by `TopRel`
correspond (`LexRel`). Run over operations that simulate each other, the step of a call on a
slice (`lexSliceStep`) or at the end of the input (`lexEofStep`) run on two lexers that correspond
are the projections of one computation of the same results with lexers that correspond again
(`MCouple`), whether the call succeeds or fails: `run_lexSliceStep_sim` and `run_lexEofStep_sim`.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation
open BSmtLib.Proofs.Lexer.WRustPort (Ops)

/-- The two lexers correspond: the same consumer, and lexer states related by `TopRel`. -/
def LexRel {H : Type} {recovery : Recovery} (a b : Lexer.WRustPort.Lexer H recovery) : Prop :=
  a.handler = b.handler ∧ TopRel a.core b.core

/-- The runs of a step on two lexers give the same result, with lexers that correspond. -/
def RunRel {H α : Type} {recovery : Recovery} (a b : α × Lexer.WRustPort.Lexer H recovery) :
    Prop :=
  a.1 = b.1 ∧ LexRel a.2 b.2

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {recovery : Recovery}
  {α β : Type}

theorem run_couple {Q : α → β → Core → Core → Prop} {step : Lexer.WRustPort.InnerM H m α}
    {step' : Lexer.WRustPort.InnerM H m β} (hs : ISim TopRel Q step step')
    (self self' : Lexer.WRustPort.Lexer H recovery) (h : LexRel self self') :
    MCouple (fun a b => Q a.1 b.1 a.2.core b.2.core ∧ a.2.handler = b.2.handler)
      (self.run step) (self'.run step') := by
  obtain ⟨handler, core⟩ := self
  obtain ⟨handler', core'⟩ := self'
  obtain ⟨hh, ht⟩ := h
  dsimp only at hh ht
  subst hh
  obtain ⟨y, h1, h2⟩ := hs core core' ht handler
  refine ⟨(fun z => ⟨((z.val.1.1.1, ⟨z.val.1.2, z.val.1.1.2⟩),
    (z.val.2.1.1, ⟨z.val.2.2, z.val.2.1.2⟩)), ⟨z.property.1, z.property.2⟩⟩) <$> y, ?_, ?_⟩
  · simp only [Lexer.WRustPort.Lexer.run, h1, map_eq_pure_bind, bind_assoc, pure_bind]
  · simp only [Lexer.WRustPort.Lexer.run, h2, map_eq_pure_bind, bind_assoc, pure_bind]

/-- A step with equal results from states related by `TopRel`, run on lexers that correspond. -/
theorem run_couple_top {step step' : Lexer.WRustPort.InnerM H m α}
    (hs : ISim TopRel TopQ step step') (self self' : Lexer.WRustPort.Lexer H recovery)
    (h : LexRel self self') :
    MCouple RunRel (self.run step) (self'.run step') :=
  MCouple.mono (fun _ _ h => ⟨h.1.1, h.2, h.1.2⟩) (run_couple hs self self' h)

end

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {recovery : Recovery} {o₁ o₂ : Ops H m R E}
  {LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop}

/-- Over operations that simulate each other, the step of a call on a slice, run on lexers that
correspond, gives the same result with lexers that correspond again, also where it fails. -/
theorem run_lexSliceStep_sim (ho : OpsSim o₁ o₂ LRel)
    (abandon recover : Location → StateT H m Unit) (slice : ByteSlice)
    (self self' : Lexer.WRustPort.Lexer H recovery) (h : LexRel self self') :
    MCouple RunRel
      (self.run (Lexer.WRustPort.lexSliceStep (ops := o₁) (R := R) (E := E) abandon recover slice))
      (self'.run (Lexer.WRustPort.lexSliceStep (ops := o₂) abandon recover slice)) :=
  run_couple_top (lexSliceStep_sim ho abandon recover slice) self self' h

/-- Over operations that simulate each other, the step of a call at the end of the input, run on
lexers that correspond, gives the same result with lexers that correspond again, also where it
fails. -/
theorem run_lexEofStep_sim (ho : OpsSim o₁ o₂ LRel)
    (abandon recover : Location → StateT H m Unit)
    (self self' : Lexer.WRustPort.Lexer H recovery) (h : LexRel self self') :
    MCouple RunRel
      (self.run (Lexer.WRustPort.lexEofStep (ops := o₁) (R := R) (E := E) abandon recover))
      (self'.run (Lexer.WRustPort.lexEofStep (ops := o₂) abandon recover)) :=
  run_couple_top (lexEofStep_sim ho abandon recover) self self' h

end

end BSmtLib.Proofs.WRustPortX1BatchInCore

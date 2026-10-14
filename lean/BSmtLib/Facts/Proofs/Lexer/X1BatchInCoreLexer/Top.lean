import BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Calls

/-!
# The library's lexer and `X1BatchInCore`, call by call

For lexers with the same consumer whose states are related (`LexerRel`), `lexSlice` and `lexEof`
of `X1BatchInCore` give, with the base forgotten, what those of the library's lexer give, mapped
to `X1BatchInCore` with the base forgotten; in every lawful monad, for every consumer, with and
without recovery. The calls run their steps on the parts of the lexer, so this follows from the
couplings of the steps (`Calls`). So do the steps of the calls themselves, run by `run`, which
gives back the lexer also after a failed call (`run_lexSliceStep`, `run_lexEofStep`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Top

open BSmtLib.Facts.Proofs.Lexer.Simulation.Couple (MCouple MCouple.map)
open BSmtLib.Lexer.Internal (handler core ofParts)
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Calls
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Outer BSmtLib.Lexer.Error

section

variable {H R E : Type} [Token.Consume H R E] {recovery : Lexer.Recovery}

/-- The library's lexer as `X1BatchInCore`, with its base forgotten. -/
def lexerMap (l : BSmtLib.Lexer H recovery) : Lexer.Internal.WRustPort.Lexer H recovery :=
  { handler := handler l, core := zm (core l), held := BSmtLib.Lexer.Internal.held l }

/-- `X1BatchInCore` with its base forgotten. -/
def lexerZb (x : Lexer.Internal.WRustPort.Lexer H recovery) : Lexer.Internal.WRustPort.Lexer H
    recovery :=
  { handler := x.handler, core := zb x.core, held := x.held }

/-- What a failed call of the library's lexer gives back, mapped by `lexerMap`. -/
def afterErrorMap : {recovery : Lexer.Recovery} → BSmtLib.Lexer.AfterError H recovery →
    Lexer.Internal.WRustPort.Lexer.AfterError H recovery
  | .failFast, _ => ()
  | .recovering, l => lexerMap (recovery := .recovering) l

/-- What a failed call of `X1BatchInCore` gives back, with the base
forgotten. -/
def afterErrorZb : {recovery : Lexer.Recovery} → Lexer.Internal.WRustPort.Lexer.AfterError H
    recovery →
    Lexer.Internal.WRustPort.Lexer.AfterError H recovery
  | .failFast, _ => ()
  | .recovering, x => lexerZb (recovery := .recovering) x

/-- The lexer held by a recovering lexer whose end of the input failed and continues. -/
abbrev pendingLexer (p : BSmtLib.Lexer.PendingEof H) : BSmtLib.Lexer H .recovering :=
  BSmtLib.Lexer.Internal.pendingLexer p

/-- What a failed end of the input of the library's lexer gives back, mapped by `lexerMap`. -/
def afterEofMap : {recovery : Lexer.Recovery} →
    BSmtLib.Lexer.AfterEofError H recovery → Lexer.Internal.WRustPort.Lexer.AfterEofError H recovery
  | .failFast, _ => ()
  | .recovering, .lexer l => .lexer (lexerMap l)
  | .recovering, .pending p => .pending ⟨lexerMap (pendingLexer p)⟩

/-- What a failed end of the input of `X1BatchInCore` gives back, with the
base forgotten. -/
def afterEofZb : {recovery : Lexer.Recovery} → Lexer.Internal.WRustPort.Lexer.AfterEofError H
    recovery →
    Lexer.Internal.WRustPort.Lexer.AfterEofError H recovery
  | .failFast, _ => ()
  | .recovering, .lexer x => .lexer (lexerZb x)
  | .recovering, .pending p => .pending ⟨lexerZb p.lexer⟩

/-- The result of a call, with what it gives back mapped by `f` and what a failure gives back
mapped by `after`. -/
def resultMap {α A A' β β' : Type} (after : A → A') (f : β → β') :
    Except (α × A) β → Except (α × A') β'
  | .ok b => .ok (f b)
  | .error (e, a) => .error (e, after a)

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type} [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]

theorem lexSlice_sim {recovery : Lexer.Recovery} [Lexer.Recovery.LexRecovery recovery H m]
    (l : BSmtLib.Lexer H recovery)
    (x : Lexer.Internal.WRustPort.Lexer H recovery) (hh : x.handler = handler l)
    (hx : Rel (core l) x.core) (hd : x.held = BSmtLib.Lexer.Internal.held l) (slice : ByteSlice)
    (hs : slice.stop < USize.size) :
    resultMap afterErrorZb lexerZb <$> Lexer.Internal.X1BatchInCore.Lexer.lexSlice x slice =
      resultMap afterErrorMap lexerMap <$> BSmtLib.Lexer.lexSlice l slice := by
  have hc := lexSliceStep_couple (H := H) (m := m) (R := R) (E := E)
    (Lexer.Recovery.LexRecovery.abandon recovery)
    (Lexer.Recovery.LexRecovery.recover recovery) slice hs
  obtain ⟨xh, xc, xd⟩ := x
  simp only at hh hx hd
  subst hh hd
  rw [show l = ofParts (handler l) (core l) (BSmtLib.Lexer.Internal.held l) from rfl]
  simp only [Lexer.Internal.X1BatchInCore.Lexer.lexSlice, BSmtLib.Lexer.lexSlice,
      Lexer.Internal.WRustPort.Lexer.run,
    BSmtLib.Lexer.Internal.run, ofParts, bind_pure_comp,
    Functor.map_map]
  refine (Coupled.map_eq _ _ (fun a c h b x e hcx => ?_) hc hx (handler l)).symm
  subst e
  rcases a with err | held
  · cases recovery
    · rfl
    · exact congrArg (fun y => (Except.error (err,
        ({ handler := h, core := y, held := none } : Lexer.Internal.WRustPort.Lexer H .recovering))
            :
          Except (LexError E × Lexer.Internal.WRustPort.Lexer H .recovering)
            (Lexer.Internal.WRustPort.Lexer H .recovering))) hcx.symm
  · simp only [resultMap, lexerMap, lexerZb, BSmtLib.Lexer.Internal.withHeld,
      BSmtLib.Lexer.Internal.handler, BSmtLib.Lexer.Internal.core, BSmtLib.Lexer.Internal.held]
    rw [hcx]

theorem lexEof_sim {recovery : Lexer.Recovery} [Lexer.Recovery.LexRecovery recovery H m]
    (l : BSmtLib.Lexer H recovery) (x : Lexer.Internal.WRustPort.Lexer H recovery)
    (hh : x.handler = handler l) (hx : Rel (core l) x.core)
    (hd : x.held = BSmtLib.Lexer.Internal.held l) :
    resultMap afterEofZb (fun p => (p.1, lexerZb p.2)) <$>
        Lexer.Internal.X1BatchInCore.Lexer.lexEof x =
      resultMap afterEofMap (fun p => (p.1, lexerMap p.2)) <$> BSmtLib.Lexer.lexEof l := by
  have hc := lexEofStep_couple (H := H) (m := m) (R := R) (E := E)
    (Lexer.Recovery.LexRecovery.abandon recovery) (Lexer.Recovery.LexRecovery.recover recovery)
  obtain ⟨xh, xc, xd⟩ := x
  simp only at hh hx hd
  subst hh hd
  rw [show l = ofParts (handler l) (core l) (BSmtLib.Lexer.Internal.held l) from rfl]
  simp only [Lexer.Internal.X1BatchInCore.Lexer.lexEof, BSmtLib.Lexer.lexEof,
      Lexer.Internal.WRustPort.Lexer.run,
    BSmtLib.Lexer.Internal.run, ofParts, bind_pure_comp, Functor.map_map]
  refine (Coupled.map_eq _ _ (fun a c h b x e hcx => ?_) hc hx (handler l)).symm
  subst e
  rcases a with err | flow
  · cases recovery
    · rfl
    · dsimp only
      rcases err.continuesFrom.isSome
      all_goals
        simp only [resultMap, afterEofMap, afterEofZb, lexerMap, lexerZb,
          BSmtLib.Lexer.Internal.withHeld, BSmtLib.Lexer.Internal.handler,
          BSmtLib.Lexer.Internal.core, BSmtLib.Lexer.Internal.held,
          Lexer.Internal.WRustPort.Lexer.afterEofError]
        rw [hcx]
        rfl
  · simp only [resultMap, lexerMap, lexerZb, BSmtLib.Lexer.Internal.withHeld,
      BSmtLib.Lexer.Internal.handler, BSmtLib.Lexer.Internal.core, BSmtLib.Lexer.Internal.held]
    rw [hcx]
    rfl

end

/-! ## The runs of the steps of the calls -/

section

variable {H R E : Type} [Token.Consume H R E] {recovery : Lexer.Recovery}

/-- The library's lexer and `X1BatchInCore` are related: they have the same consumer and the same
held result, and their states are equal once the base is forgotten. -/
def LexerRel (l : BSmtLib.Lexer H recovery) (x : Lexer.Internal.WRustPort.Lexer H recovery) : Prop
    :=
  x.handler = handler l ∧ Rel (core l) x.core ∧ x.held = BSmtLib.Lexer.Internal.held l

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type} [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]

omit [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
/-- Steps that are coupled, run on related lexers by `run`, give results related as the
coupling relates them, and related lexers. -/
theorem run_couple {recovery : Lexer.Recovery} {α β : Type} {Rr : α → β → Prop}
    {f : BSmtLib.Lexer.InnerM H m α} {g : Lexer.Internal.WRustPort.InnerM H m β}
    (hc : Coupled Rr f g)
    (l : BSmtLib.Lexer H recovery) (x : Lexer.Internal.WRustPort.Lexer H recovery)
    (hlx : LexerRel l x) :
    MCouple (fun a b => Rr a.1 b.1 ∧ LexerRel a.2 b.2) (BSmtLib.Lexer.Internal.run l f)
      (x.run g) := by
  obtain ⟨xh, xc, xd⟩ := x
  obtain ⟨hh, hx, hd⟩ := hlx
  simp only at hh hx hd
  subst hh hd
  rw [show l = ofParts (handler l) (core l) (BSmtLib.Lexer.Internal.held l) from rfl]
  simp only [Lexer.Internal.WRustPort.Lexer.run, BSmtLib.Lexer.Internal.run, ofParts,
      bind_pure_comp]
  have hm : MCouple (fun a b => (Rr a.1.1 b.1.1 ∧ Rel a.1.2 b.1.2) ∧ a.2 = b.2)
      ((f.run (core l)).run (handler l)) ((g.run xc).run (handler l)) :=
    hc (core l) xc hx (handler l)
  refine MCouple.map _ _ hm fun p q hpq => ?_
  obtain ⟨⟨hr, hcx⟩, e⟩ := hpq
  exact ⟨hr, e.symm, hcx, rfl⟩

/-- The step of a call on a slice that ends below `USize.size`, run on related lexers: the two
give the same result, and related lexers, also where the call fails. -/
theorem run_lexSliceStep (abandon recover : Span.Location → StateT H m Unit)
    {recovery : Lexer.Recovery} (l : BSmtLib.Lexer H recovery)
    (x : Lexer.Internal.WRustPort.Lexer H recovery)
    (hlx : LexerRel l x) (slice : ByteSlice) (hs : slice.stop < USize.size) :
    MCouple (fun a b => a.1 = b.1 ∧ LexerRel a.2 b.2)
      (BSmtLib.Lexer.Internal.run l
        (BSmtLib.Lexer.Internal.lexSliceStep (R := R) (E := E) abandon recover slice))
      (x.run (Lexer.Internal.WRustPort.lexSliceStep
          (ops := Lexer.Internal.X1BatchInCore.ops) abandon recover
        slice)) :=
  run_couple (lexSliceStep_couple abandon recover slice hs) l x hlx

/-- The step of a call on the end of the input, run on related lexers: the two give the same
result, and related lexers, also where the call fails. -/
theorem run_lexEofStep (abandon recover : Span.Location → StateT H m Unit)
    {recovery : Lexer.Recovery} (l : BSmtLib.Lexer H recovery)
    (x : Lexer.Internal.WRustPort.Lexer H recovery)
    (hlx : LexerRel l x) :
    MCouple (fun a b => a.1 = b.1 ∧ LexerRel a.2 b.2)
      (BSmtLib.Lexer.Internal.run l
        (BSmtLib.Lexer.Internal.lexEofStep (R := R) (E := E) abandon recover))
      (x.run (Lexer.Internal.WRustPort.lexEofStep (ops := Lexer.Internal.X1BatchInCore.ops) abandon
          recover)) :=
  run_couple (lexEofStep_couple abandon recover) l x hlx

end

end BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Top

module

public import BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Calls
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.X1BatchInCore

@[expose] public section

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
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Calls
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Outer BSmtLib.Lexer.Error
open BSmtLib.Lexer.Recovery (Recovers)

section

variable {H R E : Type} [Token.Consume H R E] {recovery : Type}

/-- The library's lexer as `X1BatchInCore`, with its base forgotten. -/
def lexerMap (l : BSmtLib.Lexer H recovery) : Lexer.Internal.WRustPort.Lexer H recovery :=
  { handler := BSmtLib.Lexer.Internal.handler l, core := zm (BSmtLib.Lexer.Internal.core
      l), held := BSmtLib.Lexer.Internal.held l }

/-- `X1BatchInCore` with its base forgotten. -/
def lexerZb (x : Lexer.Internal.WRustPort.Lexer H recovery) : Lexer.Internal.WRustPort.Lexer H
    recovery :=
  { handler := x.handler, core := zb x.core, held := x.held }

/-- What a failed call of the library's lexer gives back, mapped by `lexerMap`, by whether the
lexer recovers. -/
def afterErrorMapOf : (recovers : Bool) → BSmtLib.Lexer.Internal.AfterErrorOf H recovery recovers →
    Lexer.Internal.WRustPort.Lexer.AfterErrorOf H recovery recovers
  | false, _ => ()
  | true, l => lexerMap l

/-- What a failed call of the library's lexer gives back, mapped by `lexerMap`. -/
def afterErrorMap [Recovers recovery] (a : BSmtLib.Lexer.AfterError H recovery) :
    Lexer.Internal.WRustPort.Lexer.AfterError H recovery :=
  afterErrorMapOf (Recovers.recovers recovery) a

/-- What a failed call of `X1BatchInCore` gives back, with the base forgotten, by whether the
lexer recovers. -/
def afterErrorZbOf : (recovers : Bool) →
    Lexer.Internal.WRustPort.Lexer.AfterErrorOf H recovery recovers →
    Lexer.Internal.WRustPort.Lexer.AfterErrorOf H recovery recovers
  | false, _ => ()
  | true, x => lexerZb x

/-- What a failed call of `X1BatchInCore` gives back, with the base
forgotten. -/
def afterErrorZb [Recovers recovery] (a : Lexer.Internal.WRustPort.Lexer.AfterError H recovery) :
    Lexer.Internal.WRustPort.Lexer.AfterError H recovery :=
  afterErrorZbOf (Recovers.recovers recovery) a

/-- The lexer held by a recovering lexer whose end of the input failed and continues. -/
abbrev pendingLexer (p : BSmtLib.Lexer.PendingEof H recovery) : BSmtLib.Lexer H recovery :=
  BSmtLib.Lexer.Internal.pendingLexer p

/-- What a failed end of the input of the library's lexer gives back, mapped by `lexerMap`, by
whether the lexer recovers. -/
def afterEofMapOf : (recovers : Bool) →
    BSmtLib.Lexer.Internal.AfterEofErrorOf H recovery recovers →
    Lexer.Internal.WRustPort.Lexer.AfterEofErrorOf H recovery recovers
  | false, _ => ()
  | true, .lexer l => .lexer (lexerMap l)
  | true, .pending p => .pending ⟨lexerMap (pendingLexer p)⟩

/-- What a failed end of the input of the library's lexer gives back, mapped by `lexerMap`. -/
def afterEofMap [Recovers recovery] (a : BSmtLib.Lexer.AfterEofError H recovery) :
    Lexer.Internal.WRustPort.Lexer.AfterEofError H recovery :=
  afterEofMapOf (Recovers.recovers recovery) a

/-- What a failed end of the input of `X1BatchInCore` gives back, with the base forgotten, by
whether the lexer recovers. -/
def afterEofZbOf : (recovers : Bool) →
    Lexer.Internal.WRustPort.Lexer.AfterEofErrorOf H recovery recovers →
    Lexer.Internal.WRustPort.Lexer.AfterEofErrorOf H recovery recovers
  | false, _ => ()
  | true, .lexer x => .lexer (lexerZb x)
  | true, .pending p => .pending ⟨lexerZb p.lexer⟩

/-- What a failed end of the input of `X1BatchInCore` gives back, with the
base forgotten. -/
def afterEofZb [Recovers recovery]
    (a : Lexer.Internal.WRustPort.Lexer.AfterEofError H recovery) :
    Lexer.Internal.WRustPort.Lexer.AfterEofError H recovery :=
  afterEofZbOf (Recovers.recovers recovery) a

/-- The result of a call, with what it gives back mapped by `f` and what a failure gives back
mapped by `after`. -/
def resultMap {α A A' β β' : Type} (after : A → A') (f : β → β') :
    Except (α × A) β → Except (α × A') β'
  | .ok b => .ok (f b)
  | .error (e, a) => .error (e, after a)

/-- A failed call gives back related lexers if the lexers it is made on are related, whether
the lexer recovers or not. -/
theorem afterErrorMapOf_zb (recovers : Bool) (l : BSmtLib.Lexer H recovery)
    (x : Lexer.Internal.WRustPort.Lexer H recovery) (hlx : lexerMap l = lexerZb x) :
    afterErrorMapOf recovers (BSmtLib.Lexer.Internal.afterErrorOf recovers l) =
      afterErrorZbOf recovers (Lexer.Internal.WRustPort.Lexer.afterErrorOf recovers x) := by
  cases recovers
  · rfl
  · exact hlx

/-- A failed end of the input gives back related lexers if the lexers it is made on are related,
whether the lexer recovers or not, and whether the error continues or not. -/
theorem afterEofMapOf_zb (recovers : Bool) (l : BSmtLib.Lexer H recovery)
    (x : Lexer.Internal.WRustPort.Lexer H recovery) (hlx : lexerMap l = lexerZb x)
    (continues : Bool) :
    afterEofMapOf recovers (BSmtLib.Lexer.Internal.afterEofErrorOf recovers l continues) =
      afterEofZbOf recovers
        (Lexer.Internal.WRustPort.Lexer.afterEofErrorOf recovers x continues) := by
  cases recovers
  · rfl
  · cases continues
    · exact congrArg Lexer.Internal.WRustPort.Lexer.AfterEof.lexer hlx
    · exact congrArg (fun y => Lexer.Internal.WRustPort.Lexer.AfterEof.pending ⟨y⟩) hlx

/-- A lexer with the consumer, the state and no held result, mapped by `lexerMap`, is `lexerZb`
of the same with a related state. -/
theorem lexerMap_zb (h : H) {c : Core.ZCore} {x : Core.XCore} (hcx : Rel c x)
    (held : Option (Span.Located R)) :
    lexerMap (BSmtLib.Lexer.Internal.withHeld
        (BSmtLib.Lexer.Internal.ofParts h c held : BSmtLib.Lexer H recovery) none) =
      lexerZb ({ handler := h, core := x, held := none } :
        Lexer.Internal.WRustPort.Lexer H recovery) := by
  simp only [lexerMap, lexerZb, BSmtLib.Lexer.Internal.withHeld, BSmtLib.Lexer.Internal.ofParts,
    BSmtLib.Lexer.Internal.handler, BSmtLib.Lexer.Internal.core, BSmtLib.Lexer.Internal.held]
  rw [hcx]

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type} [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]

theorem lexSlice_sim {recovery : Type} [Recovers recovery]
    [Lexer.Recovery.LexRecovery recovery H m]
    (l : BSmtLib.Lexer H recovery)
    (x : Lexer.Internal.WRustPort.Lexer H recovery)
    (hh : x.handler = BSmtLib.Lexer.Internal.handler l)
    (hx : Rel (BSmtLib.Lexer.Internal.core l) x.core) (hd : x.held = BSmtLib.Lexer.Internal.held l)
    (slice : ByteSlice)
    (hs : slice.stop < USize.size) :
    resultMap afterErrorZb lexerZb <$> Lexer.Internal.X1BatchInCore.Lexer.lexSlice x slice =
      resultMap afterErrorMap lexerMap <$> BSmtLib.Lexer.lexSlice l slice := by
  have hc := lexSliceStep_couple (H := H) (m := m) (R := R) (E := E)
    (Lexer.Recovery.LexRecovery.abandon recovery)
    (Lexer.Recovery.LexRecovery.recover recovery) slice hs
  obtain ⟨xh, xc, xd⟩ := x
  simp only at hh hx hd
  subst hh hd
  rw [show l = BSmtLib.Lexer.Internal.ofParts (BSmtLib.Lexer.Internal.handler l)
      (BSmtLib.Lexer.Internal.core l) (BSmtLib.Lexer.Internal.held l) from rfl]
  simp only [Lexer.Internal.X1BatchInCore.Lexer.lexSlice, BSmtLib.Lexer.lexSlice,
      Lexer.Internal.WRustPort.Lexer.run,
    BSmtLib.Lexer.Internal.run, BSmtLib.Lexer.Internal.ofParts, bind_pure_comp,
    Functor.map_map]
  refine (Coupled.map_eq _ _ (fun a c h b x e hcx => ?_) hc hx
      (BSmtLib.Lexer.Internal.handler l)).symm
  subst e
  rcases a with err | held
  · exact congrArg (fun a => Except.error (err, a))
      (afterErrorMapOf_zb (Recovers.recovers recovery) _ _ (lexerMap_zb h hcx _))
  · simp only [resultMap, lexerMap, lexerZb, BSmtLib.Lexer.Internal.withHeld,
      BSmtLib.Lexer.Internal.handler, BSmtLib.Lexer.Internal.core, BSmtLib.Lexer.Internal.held]
    rw [hcx]

theorem lexEof_sim {recovery : Type} [Recovers recovery]
    [Lexer.Recovery.LexRecovery recovery H m]
    (l : BSmtLib.Lexer H recovery) (x : Lexer.Internal.WRustPort.Lexer H recovery)
    (hh : x.handler = BSmtLib.Lexer.Internal.handler l)
    (hx : Rel (BSmtLib.Lexer.Internal.core l) x.core)
    (hd : x.held = BSmtLib.Lexer.Internal.held l) :
    resultMap afterEofZb (fun p => (p.1, lexerZb p.2)) <$>
        Lexer.Internal.X1BatchInCore.Lexer.lexEof x =
      resultMap afterEofMap (fun p => (p.1, lexerMap p.2)) <$> BSmtLib.Lexer.lexEof l := by
  have hc := lexEofStep_couple (H := H) (m := m) (R := R) (E := E)
    (Lexer.Recovery.LexRecovery.abandon recovery) (Lexer.Recovery.LexRecovery.recover recovery)
  obtain ⟨xh, xc, xd⟩ := x
  simp only at hh hx hd
  subst hh hd
  rw [show l = BSmtLib.Lexer.Internal.ofParts (BSmtLib.Lexer.Internal.handler l)
      (BSmtLib.Lexer.Internal.core l) (BSmtLib.Lexer.Internal.held l) from rfl]
  simp only [Lexer.Internal.X1BatchInCore.Lexer.lexEof, BSmtLib.Lexer.lexEof,
      Lexer.Internal.WRustPort.Lexer.run,
    BSmtLib.Lexer.Internal.run, BSmtLib.Lexer.Internal.ofParts, bind_pure_comp, Functor.map_map]
  refine (Coupled.map_eq _ _ (fun a c h b x e hcx => ?_) hc hx
      (BSmtLib.Lexer.Internal.handler l)).symm
  subst e
  rcases a with err | flow
  · exact congrArg (fun a => Except.error (err, a))
      (afterEofMapOf_zb (Recovers.recovers recovery) _ _ (lexerMap_zb h hcx _) _)
  · simp only [resultMap, lexerMap, lexerZb, BSmtLib.Lexer.Internal.withHeld,
      BSmtLib.Lexer.Internal.handler, BSmtLib.Lexer.Internal.core, BSmtLib.Lexer.Internal.held]
    rw [hcx]
    rfl

end

/-! ## The runs of the steps of the calls -/

section

variable {H R E : Type} [Token.Consume H R E] {recovery : Type}

/-- The library's lexer and `X1BatchInCore` are related: they have the same consumer and the same
held result, and their states are equal once the base is forgotten. -/
def LexerRel (l : BSmtLib.Lexer H recovery) (x : Lexer.Internal.WRustPort.Lexer H recovery) : Prop
    :=
  x.handler = BSmtLib.Lexer.Internal.handler l ∧ Rel
      (BSmtLib.Lexer.Internal.core l) x.core ∧ x.held = BSmtLib.Lexer.Internal.held l

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type} [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]

omit [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
/-- Steps that are coupled, run on related lexers by `run`, give results related as the
coupling relates them, and related lexers. -/
theorem run_couple {recovery : Type} {α β : Type} {Rr : α → β → Prop}
    {f : BSmtLib.Lexer.Internal.InnerM H m α} {g : Lexer.Internal.WRustPort.InnerM H m β}
    (hc : Coupled Rr f g)
    (l : BSmtLib.Lexer H recovery) (x : Lexer.Internal.WRustPort.Lexer H recovery)
    (hlx : LexerRel l x) :
    MCouple (fun a b => Rr a.1 b.1 ∧ LexerRel a.2 b.2) (BSmtLib.Lexer.Internal.run l f)
      (x.run g) := by
  obtain ⟨xh, xc, xd⟩ := x
  obtain ⟨hh, hx, hd⟩ := hlx
  simp only at hh hx hd
  subst hh hd
  rw [show l = BSmtLib.Lexer.Internal.ofParts (BSmtLib.Lexer.Internal.handler l)
      (BSmtLib.Lexer.Internal.core l) (BSmtLib.Lexer.Internal.held l) from rfl]
  simp only [Lexer.Internal.WRustPort.Lexer.run, BSmtLib.Lexer.Internal.run,
      BSmtLib.Lexer.Internal.ofParts,
      bind_pure_comp]
  have hm : MCouple (fun a b => (Rr a.1.1 b.1.1 ∧ Rel a.1.2 b.1.2) ∧ a.2 = b.2)
      ((f.run (BSmtLib.Lexer.Internal.core l)).run (BSmtLib.Lexer.Internal.handler l))
          ((g.run xc).run (BSmtLib.Lexer.Internal.handler l)) :=
    hc (BSmtLib.Lexer.Internal.core l) xc hx (BSmtLib.Lexer.Internal.handler l)
  refine MCouple.map _ _ hm fun p q hpq => ?_
  obtain ⟨⟨hr, hcx⟩, e⟩ := hpq
  exact ⟨hr, e.symm, hcx, rfl⟩

/-- The step of a call on a slice that ends below `USize.size`, run on related lexers: the two
give the same result, and related lexers, also where the call fails. -/
theorem run_lexSliceStep (abandon recover : Span.Location → StateT H m Unit)
    {recovery : Type} (l : BSmtLib.Lexer H recovery)
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
    {recovery : Type} (l : BSmtLib.Lexer H recovery)
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

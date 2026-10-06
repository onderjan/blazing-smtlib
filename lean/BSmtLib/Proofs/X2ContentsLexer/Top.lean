import BSmtLib.Proofs.X2ContentsLexer.Calls

/-!
# The library's lexer and the lexer with the content buffer, call by call

For lexers with the same consumer whose states are related, `lexSlice` and `lexEof` of the lexer
with the content buffer give, with the base forgotten, what those of the library's lexer give,
mapped to the lexer with the content buffer with the base forgotten; in every lawful monad, for
every consumer, with and without recovery. The calls run their steps on the parts of the lexer,
so this follows from the couplings of the steps (`Calls`).
-/

namespace BSmtLib.Proofs.X2ContentsLexer

open BSmtLib.Lexer.Internal (handler core ofParts)

section

variable {H : Type} {recovery : Recovery}

/-- The library's lexer as the lexer with the content buffer, with its base forgotten. -/
def lexerMap (l : BSmtLib.Lexer H recovery) : Lexer.X2Contents.Lexer H recovery :=
  { handler := handler l, core := zm (core l) }

/-- The lexer with the content buffer with its base forgotten. -/
def lexerZb (x : Lexer.X2Contents.Lexer H recovery) : Lexer.X2Contents.Lexer H recovery :=
  { handler := x.handler, core := zb x.core }

/-- What a failed call of the library's lexer gives back, mapped by `lexerMap`. -/
def afterErrorMap : {recovery : Recovery} → BSmtLib.Lexer.AfterError H recovery →
    Lexer.X2Contents.Lexer.AfterError H recovery
  | .failFast, _ => ()
  | .recovering, l => lexerMap (recovery := .recovering) l

/-- What a failed call of the lexer with the content buffer gives back, with the base
forgotten. -/
def afterErrorZb : {recovery : Recovery} → Lexer.X2Contents.Lexer.AfterError H recovery →
    Lexer.X2Contents.Lexer.AfterError H recovery
  | .failFast, _ => ()
  | .recovering, x => lexerZb (recovery := .recovering) x

/-- The lexer held by a recovering lexer whose end of the input failed and continues. -/
abbrev pendingLexer (p : BSmtLib.Lexer.PendingEof H) : BSmtLib.Lexer H .recovering :=
  BSmtLib.Lexer.Internal.pendingLexer p

/-- What a failed end of the input of the library's lexer gives back, mapped by `lexerMap`. -/
def afterEofMap : {recovery : Recovery} →
    BSmtLib.Lexer.AfterEofError H recovery → Lexer.X2Contents.Lexer.AfterEofError H recovery
  | .failFast, _ => ()
  | .recovering, .lexer l => .lexer (lexerMap l)
  | .recovering, .pending p => .pending ⟨lexerMap (pendingLexer p)⟩

/-- What a failed end of the input of the lexer with the content buffer gives back, with the
base forgotten. -/
def afterEofZb : {recovery : Recovery} → Lexer.X2Contents.Lexer.AfterEofError H recovery →
    Lexer.X2Contents.Lexer.AfterEofError H recovery
  | .failFast, _ => ()
  | .recovering, .lexer x => .lexer (lexerZb x)
  | .recovering, .pending p => .pending ⟨lexerZb p.lexer⟩

/-- The result of a call of the library's lexer, mapped by `lexerMap`. -/
def resultMap {α A : Type} {A' : Type} (after : A → A') :
    Except (α × A) (ControlFlow (Located R) × BSmtLib.Lexer H recovery) →
      Except (α × A') (ControlFlow (Located R) × Lexer.X2Contents.Lexer H recovery)
  | .ok (flow, l) => .ok (flow, lexerMap l)
  | .error (e, a) => .error (e, after a)

/-- The result of a call of the lexer with the content buffer, with the base forgotten. -/
def resultZb {α A : Type} (after : A → A) :
    Except (α × A) (ControlFlow (Located R) × Lexer.X2Contents.Lexer H recovery) →
      Except (α × A) (ControlFlow (Located R) × Lexer.X2Contents.Lexer H recovery)
  | .ok (flow, x) => .ok (flow, lexerZb x)
  | .error (e, a) => .error (e, after a)

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {R E : Type} [Consume H m R E]

theorem lexSlice_sim {recovery : Recovery} [LexRecovery recovery H m]
    (l : BSmtLib.Lexer H recovery)
    (x : Lexer.X2Contents.Lexer H recovery) (hh : x.handler = handler l)
    (hx : Rel (core l) x.core) (slice : ByteSlice) (hs : slice.stop < USize.size) :
    resultZb afterErrorZb <$> Lexer.X2Contents.Lexer.lexSlice (R := R) (E := E) x slice =
      resultMap afterErrorMap <$> BSmtLib.Lexer.lexSlice l slice := by
  have hc := lexSliceStep_couple (H := H) (m := m) (R := R) (E := E)
    (LexRecovery.abandon recovery)
    (LexRecovery.recover recovery) slice hs
  obtain ⟨xh, xc⟩ := x
  simp only at hh hx
  subst hh
  rw [show l = ofParts (handler l) (core l) from rfl]
  simp only [Lexer.X2Contents.Lexer.lexSlice, BSmtLib.Lexer.lexSlice, Lexer.X2Contents.Lexer.run,
    BSmtLib.Lexer.Internal.run, ofParts, bind_pure_comp,
    Functor.map_map]
  refine (Couple.map_eq _ _ (fun a c h b x e hcx => ?_) hc hx (handler l)).symm
  subst e
  rcases a with err | flow
  · cases recovery
    · rfl
    · exact congrArg (fun y => (Except.error (err,
        ({ handler := h, core := y } : Lexer.X2Contents.Lexer H .recovering)) :
          Except (LexError E × Lexer.X2Contents.Lexer H .recovering)
            (ControlFlow (Located R) × Lexer.X2Contents.Lexer H .recovering))) hcx.symm
  · simp only [resultMap, resultZb, lexerMap, lexerZb]
    rw [hcx]
    rfl

theorem lexEof_sim {recovery : Recovery} [LexRecovery recovery H m]
    (l : BSmtLib.Lexer H recovery) (x : Lexer.X2Contents.Lexer H recovery)
    (hh : x.handler = handler l) (hx : Rel (core l) x.core) :
    resultZb afterEofZb <$> Lexer.X2Contents.Lexer.lexEof (R := R) (E := E) x =
      resultMap afterEofMap <$> BSmtLib.Lexer.lexEof l := by
  have hc := lexEofStep_couple (H := H) (m := m) (R := R) (E := E)
    (LexRecovery.abandon recovery) (LexRecovery.recover recovery)
  obtain ⟨xh, xc⟩ := x
  simp only at hh hx
  subst hh
  rw [show l = ofParts (handler l) (core l) from rfl]
  simp only [Lexer.X2Contents.Lexer.lexEof, BSmtLib.Lexer.lexEof, Lexer.X2Contents.Lexer.run,
    BSmtLib.Lexer.Internal.run, ofParts, bind_pure_comp, Functor.map_map]
  refine (Couple.map_eq _ _ (fun a c h b x e hcx => ?_) hc hx (handler l)).symm
  subst e
  rcases a with err | flow
  · cases recovery
    · rfl
    · dsimp only
      rcases hk : err.continuesFrom.isSome
      · exact congrArg (fun y => (Except.error (err, .lexer
          ({ handler := h, core := y } : Lexer.X2Contents.Lexer H .recovering)) :
            Except (LexError E × Lexer.X2Contents.Lexer.AfterEof H)
              (ControlFlow (Located R) × Lexer.X2Contents.Lexer H .recovering))) hcx.symm
      · exact congrArg (fun y => (Except.error (err, .pending ⟨
          ({ handler := h, core := y } : Lexer.X2Contents.Lexer H .recovering)⟩) :
            Except (LexError E × Lexer.X2Contents.Lexer.AfterEof H)
              (ControlFlow (Located R) × Lexer.X2Contents.Lexer H .recovering))) hcx.symm
  · simp only [resultMap, resultZb, lexerMap, lexerZb]
    rw [hcx]
    rfl

end

end BSmtLib.Proofs.X2ContentsLexer

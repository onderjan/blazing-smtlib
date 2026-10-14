import BSmtLib.Facts.Proofs.Parser.Drive
import BSmtLibSpec.Facts.Proofs.Parser.Equations

/-!
# Lemmas about the monads, the spec's tokens and calls

`ExceptT.adapt`, which turns a failure of the traversal into the parser's, commutes with the
monad's operations; the traversal's tokens and handler calls are the parser's ticks and calls.
-/

namespace BSmtLib.Facts.Proofs.Parser.Lemmas

open BSmtLib.Parser
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Drive

section

variable {m : Type → Type} [Monad m] [LawfulMonad m] {ε ε' ε'' α β : Type}

@[simp]
theorem adapt_pure (f : ε → ε') (a : α) : ExceptT.adapt f (pure a : ExceptT ε m α) = pure a := by
  apply ExceptT.ext
  simp [ExceptT.run_adapt, Except.mapError]

@[simp]
theorem adapt_lift (f : ε → ε') (x : m α) :
    ExceptT.adapt f (ExceptT.lift x : ExceptT ε m α) = ExceptT.lift x := by
  apply ExceptT.ext
  simp [ExceptT.run_adapt, Except.mapError]

@[simp]
theorem adapt_bind (f : ε → ε') (x : ExceptT ε m α) (g : α → ExceptT ε m β) :
    ExceptT.adapt f (x >>= g) = ExceptT.adapt f x >>= fun a => ExceptT.adapt f (g a) := by
  apply ExceptT.ext
  simp only [ExceptT.run_adapt, ExceptT.run_bind, map_bind, bind_map_left]
  congr 1
  funext result
  cases result <;> simp [Except.mapError]

@[simp]
theorem adapt_map (f : ε → ε') (g : α → β) (x : ExceptT ε m α) :
    ExceptT.adapt f (g <$> x) = g <$> ExceptT.adapt f x := by
  rw [map_eq_pure_bind, adapt_bind, map_eq_pure_bind]
  simp

@[simp]
theorem adapt_adapt (f : ε → ε') (g : ε' → ε'') (x : ExceptT ε m α) :
    ExceptT.adapt g (ExceptT.adapt f x) = ExceptT.adapt (g ∘ f) x := by
  apply ExceptT.ext
  simp only [ExceptT.run_adapt, Functor.map_map]
  congr 1
  funext result
  cases result <;> rfl

@[simp]
theorem adapt_throw (f : ε → ε') (e : ε) :
    ExceptT.adapt f (throw e : ExceptT ε m α) = throw (f e) := by
  apply ExceptT.ext
  simp [ExceptT.run_adapt, Except.mapError, ExceptT.run_throw]

omit [LawfulMonad m] in
/-- Tokens taken with no call due at the first one's arrival are taken plainly. -/
@[simp]
theorem takeAllArriving_pure (points : Points m) (tokens : List BSmtLibSpec.Grammar.SyntaxToken) :
    takeAllArriving points (pure () : Run m ε Unit) tokens = takeAll points tokens := by
  cases tokens <;> rfl

omit [LawfulMonad m] in
/-- A token received with no call due at its arrival is taken plainly. -/
@[simp]
theorem receive_token_pure (points : Points m) (token : BSmtLibSpec.Grammar.SyntaxToken) :
    receive points (.token token) (pure () : Run m ε Unit) = take points token := rfl

omit [LawfulMonad m] in
theorem takeAllArriving_cons (points : Points m) (atArrival : Run m ε Unit)
    (token : BSmtLibSpec.Grammar.SyntaxToken) (tokens : List BSmtLibSpec.Grammar.SyntaxToken) :
    takeAllArriving points atArrival (token :: tokens) =
      (do receive points (.token token) atArrival; takeAll points tokens) := rfl

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {points : Points (StateT H m)} {α : Type}

omit [Monad m] [LawfulMonad m] in
@[simp]
theorem causeOf_comp_handler :
    (causeOf ∘ Cause.handler : Traits.Handler.Error H → ParseErrorCause (Traits.Handler.Error H)) =
      ParseErrorCause.handler := rfl

omit [LawfulMonad m] in
/-- A handler call in a parse is the handler's action, its failure the handler's. -/
theorem call_eq (action : ExceptT (Traits.Handler.Error H) (StateT H m) α) :
    Parser.call action = ExceptT.adapt ParseErrorCause.handler action := rfl

@[simp]
theorem adaptRun_pure (a : α) :
    adaptRun (pure a : Run (StateT H m) (Traits.Handler.Error H) α) = pure a :=
  adapt_pure _ _

@[simp]
theorem adaptRun_bind {β : Type} (x : Run (StateT H m) (Traits.Handler.Error H) α)
    (f : α → Run (StateT H m) (Traits.Handler.Error H) β) :
    adaptRun (x >>= f) = adaptRun x >>= fun a => adaptRun (f a) :=
  adapt_bind _ _ _

@[simp]
theorem adaptRun_map {β : Type} (f : α → β) (x : Run (StateT H m) (Traits.Handler.Error H) α) :
    adaptRun (f <$> x) = f <$> adaptRun x :=
  adapt_map _ _ _

@[simp]
theorem adaptRun_lift (x : StateT H m α) :
    adaptRun (ExceptT.lift x : Run (StateT H m) (Traits.Handler.Error H) α) = ExceptT.lift x :=
  adapt_lift _ _

/-- The traversal's handler call, as the parser's call. -/
@[simp]
theorem adaptRun_call {values : Values} {returns : Returns}
    (h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) values)
    (request : Call values returns) :
    adaptRun (Traversal.call h request) = Parser.call (h.call request) := by
  simp [adaptRun, Traversal.call, call_eq]

/-- The traversal's token, as the parser's tick of a token standing for it. -/
theorem adaptRun_take {token : Input} {syntaxToken : BSmtLibSpec.Grammar.SyntaxToken}
    (h : Bridge.received token = some (.token syntaxToken)) :
    adaptRun (take points syntaxToken : Run (StateT H m) (Traits.Handler.Error H) Unit) =
      tick points token := by
  simp [take, receive, tick, arriveAt, processAt, h]

/-- The traversal's token with calls due at its arrival, as the parser's tick with those calls. -/
theorem adaptRun_receive {token : Input} {syntaxToken : BSmtLibSpec.Grammar.SyntaxToken}
    (h : Bridge.received token = some (.token syntaxToken))
    (atArrival : Run (StateT H m) (Traits.Handler.Error H) Unit) :
    adaptRun (receive points (.token syntaxToken) atArrival) =
      tickFirst points (adaptRun atArrival) token := by
  simp [receive, tickFirst, arriveAt, processAt, h]

/-- The traversal's tokens, as the parser's ticks of the tokens standing for them. -/
theorem adaptRun_takeAll {tokens : List Input} {syntaxTokens : List BSmtLibSpec.Grammar.SyntaxToken}
    (h : Stands tokens syntaxTokens) :
    adaptRun (takeAll points syntaxTokens : Run (StateT H m) (Traits.Handler.Error H) Unit) =
      ticks points tokens := by
  induction syntaxTokens generalizing tokens with
  | nil =>
    have : tokens = [] := List.map_eq_nil_iff.mp h
    subst this
    exact adapt_pure _ _
  | cons first rest ih =>
    cases tokens with
    | nil => simp [Stands] at h
    | cons token tokens =>
      simp only [Stands, List.map_cons, List.cons.injEq] at h
      have ih' := ih (tokens := tokens) h.2
      show adaptRun (take points first >>= fun _ => takeAll points rest) = _
      rw [adaptRun_bind, ticks_cons, adaptRun_take h.1, ih']

end

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] [Traits.Handler H m]
variable {h : Traversal.Handler (StateT H m) (Traits.Handler.Error H) (valuesOf H)}

open BSmtLibSpec.Facts.Proofs.Parser (Program.callSort Program.callSExpr Program.callAttribute
    Program.callTerm Program.callScope Program.callUnit)

@[simp]
theorem adaptRun_callSort (request : Call (valuesOf H) .sort) :
    adaptRun (α := Traits.Handler.«Sort» H) (Program.callSort h request) =
      Parser.call (Bridge.callSort h request) := by
  unfold Program.callSort Bridge.callSort adaptRun Traversal.call
  exact adapt_adapt _ _ _

@[simp]
theorem adaptRun_callSExpr (request : Call (valuesOf H) .sExpr) :
    adaptRun (α := Traits.Handler.SExpr H) (Program.callSExpr h request) =
      Parser.call (Bridge.callSExpr h request) := by
  unfold Program.callSExpr Bridge.callSExpr adaptRun Traversal.call
  exact adapt_adapt _ _ _

@[simp]
theorem adaptRun_callAttribute (request : Call (valuesOf H) .attribute) :
    adaptRun (α := Traits.Handler.Attribute H) (Program.callAttribute h request) =
      Parser.call (Bridge.callAttribute h request) := by
  unfold Program.callAttribute Bridge.callAttribute adaptRun Traversal.call
  exact adapt_adapt _ _ _

@[simp]
theorem adaptRun_callTerm (request : Call (valuesOf H) .term) :
    adaptRun (α := Traits.Handler.Term H) (Program.callTerm h request) =
      Parser.call (Bridge.callTerm h request) := by
  unfold Program.callTerm Bridge.callTerm adaptRun Traversal.call
  exact adapt_adapt _ _ _

@[simp]
theorem adaptRun_callScope (request : Call (valuesOf H) .scope) :
    adaptRun (α := Traits.Handler.Scope H) (Program.callScope h request) =
      Parser.call (Bridge.callScope h request) := by
  unfold Program.callScope Bridge.callScope adaptRun Traversal.call
  exact adapt_adapt _ _ _

@[simp]
theorem adaptRun_callUnit (request : Call (valuesOf H) .nothing) :
    adaptRun (Program.callUnit h request) = Parser.call (Bridge.callUnit h request) := by
  unfold Program.callUnit Bridge.callUnit adaptRun Traversal.call
  exact adapt_adapt _ _ _

end

end BSmtLib.Facts.Proofs.Parser.Lemmas

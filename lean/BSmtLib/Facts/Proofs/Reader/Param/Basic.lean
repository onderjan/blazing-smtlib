module

public import BSmtLib.Lexer

@[expose] public section

/-!
# Runs of the library's lexer with two consumers

The library's lexer (`BSmtLib.Lexer`) is generic in its consumer: the consumer's type `H`, the
monad `m` it runs in, and the types `R` and `E` of its results and errors. Its code reads the
consumer only through each call of `ConsumeFrom.consume`, the consumer's `Consume.isConcrete`,
and the recovery actions it is given; it passes the consumer's results and errors on without
looking into them. So two runs of the same code with two consumers are related wherever the
two consumers' calls are.

This module states that relation. A `Relator` relates computations in the two consumers' monads
`StateT H₁ m₁` and `StateT H₂ m₂`: it is closed under `pure` and `bind`, and otherwise arbitrary,
so that it can carry an invariant between the two consumers' states, or relate the runs only
under a condition on the first one. A `Link` adds the relations between the two result types and
between the two error types. Over them, `SSim` relates two actions on a shared state in the
consumers' monads (the lexer's state is the same on both sides), and `XSim` two such actions that
may fail; `LSim` is `XSim` for the lexer's steps, whose failures are its interruptions.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Basic

open BSmtLib.Lexer
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Lexer.Error

/-! ## Relators -/

/-- A relation between computations of two state monads, lifted from relations between their
values: closed under `pure` and `bind`, and monotone in the relation of the values. -/
structure Relator (H₁ : Type) (m₁ : Type → Type) (H₂ : Type) (m₂ : Type → Type) [Monad m₁]
    [Monad m₂] where
  /-- The computations are related with values related by the relation. -/
  rel : {α β : Type} → (α → β → Prop) → StateT H₁ m₁ α → StateT H₂ m₂ β → Prop
  pure {α β : Type} {Q : α → β → Prop} {a : α} {b : β} :
    Q a b → rel Q (Pure.pure a) (Pure.pure b)
  bind {α β γ δ : Type} {Q : α → β → Prop} {Q' : γ → δ → Prop} {x : StateT H₁ m₁ α}
    {y : StateT H₂ m₂ β} {f : α → StateT H₁ m₁ γ} {g : β → StateT H₂ m₂ δ} :
    rel Q x y → (∀ a b, Q a b → rel Q' (f a) (g b)) → rel Q' (x >>= f) (y >>= g)
  mono {α β : Type} {Q Q' : α → β → Prop} {x : StateT H₁ m₁ α} {y : StateT H₂ m₂ β} :
    (∀ a b, Q a b → Q' a b) → rel Q x y → rel Q' x y

/-! ## Relations between the lexer's values -/

/-- Results related by `Q`, or failures related by `Qe`. -/
def ERel {ε₁ ε₂ α β : Type} (Qe : ε₁ → ε₂ → Prop) (Q : α → β → Prop) :
    Except ε₁ α → Except ε₂ β → Prop
  | .ok a, .ok b => Q a b
  | .error e, .error e' => Qe e e'
  | _, _ => False

/-- The same lexical error kind, or consumer errors related by `RE`. -/
def CauseRel {E₁ E₂ : Type} (RE : E₁ → E₂ → Prop) : LexerErrorKind E₁ → LexerErrorKind E₂ → Prop
  | .lexical e, .lexical e' => e = e'
  | .consumer e, .consumer e' => RE e e'
  | _, _ => False

/-- The same answer of a consumer, with results related by `RR`. -/
def FlowRel {R₁ R₂ : Type} (RR : R₁ → R₂ → Prop) : ControlFlow R₁ → ControlFlow R₂ → Prop
  | .continue, .continue => True
  | .break r, .break r' => RR r r'
  | _, _ => False

/-- Options that are both none, or both some with values related by `Q`. -/
def ORel {α β : Type} (Q : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => Q a b
  | _, _ => False

/-- The same location, with values related by `RR`. -/
def LocRel {R₁ R₂ : Type} (RR : R₁ → R₂ → Prop) (a : Span.Located R₁)
    (b : Span.Located R₂) : Prop :=
  RR a.value b.value ∧ a.location = b.location

/-- The same stop of the consumer, with results related by `RR`. -/
def StopRel {R₁ R₂ : Type} (RR : R₁ → R₂ → Prop) : Stop R₁ → Stop R₂ → Prop
  | .relex, .relex => True
  | .finished r, .finished r' => RR r r'
  | .discarded r, .discarded r' => ORel RR r r'
  | _, _ => False

/-- The same interruption with the same span at the same location, with results related by `RR`
and consumer errors by `RE`. -/
def IRel {R₁ R₂ E₁ E₂ : Type} {floor : Option Nat} (RR : R₁ → R₂ → Prop) (RE : E₁ → E₂ → Prop)
    (i : Interrupted R₁ E₁ floor) (j : Interrupted R₂ E₂ floor) : Prop :=
  i.location = j.location ∧ i.span = j.span ∧ ERel (CauseRel RE) (StopRel RR) i.result j.result

/-- Failures with the same span at the same location, with causes related. -/
def FailRel {E₁ E₂ : Type} (RE : E₁ → E₂ → Prop) (a : Failure E₁) (b : Failure E₂) : Prop :=
  CauseRel RE a.kind b.kind ∧ a.span = b.span ∧ a.location = b.location

/-- Lexer errors with causes related and the same span, continuing from the same location. -/
def LexErrRel {E₁ E₂ : Type} (RE : E₁ → E₂ → Prop) (a : LexerError E₁) (b : LexerError E₂) : Prop :=
  CauseRel RE a.kind b.kind ∧ a.span = b.span ∧ a.continuesFrom = b.continuesFrom

/-! ## The link between two consumers -/

/-- What relates two consumers: a relator between their monads, and relations between their
results and between their errors. -/
structure Link (H₁ : Type) (m₁ : Type → Type) (R₁ E₁ : Type) (H₂ : Type) (m₂ : Type → Type)
    (R₂ E₂ : Type) [Monad m₁] [Monad m₂] where
  rc : Relator H₁ m₁ H₂ m₂
  rr : R₁ → R₂ → Prop
  re : E₁ → E₂ → Prop

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  (L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂)

/-- Two actions on a shared state and the consumers' states: from the same state, related
values and the same state. -/
def SSim {S α β : Type} (Q : α → β → Prop) (f : StateT S (StateT H₁ m₁) α)
    (g : StateT S (StateT H₂ m₂) β) : Prop :=
  ∀ s, L.rc.rel (fun a b => Q a.1 b.1 ∧ a.2 = b.2) (f.run s) (g.run s)

/-- Two actions that may fail: related values, or failures related by `Qe`. -/
def XSim {S ε₁ ε₂ α β : Type} (Qe : ε₁ → ε₂ → Prop) (Q : α → β → Prop)
    (f : ExceptT ε₁ (StateT S (StateT H₁ m₁)) α) (g : ExceptT ε₂ (StateT S (StateT H₂ m₂)) β) :
    Prop :=
  SSim L (ERel Qe Q) f.run g.run

/-- Two steps of the lexer: related values, or related interruptions. -/
abbrev LSim {S α β : Type} {floor : Option Nat} (Q : α → β → Prop)
    (f : ExceptT (Interrupted R₁ E₁ floor) (StateT S (StateT H₁ m₁)) α)
    (g : ExceptT (Interrupted R₂ E₂ floor) (StateT S (StateT H₂ m₂)) β) : Prop :=
  XSim L (IRel L.rr L.re) Q f g

/-! ### Actions on the shared state -/

section SSim

variable {L} {S α β γ δ : Type}

theorem SSim.pure {Q : α → β → Prop} {a : α} {b : β} (h : Q a b) :
    SSim (S := S) L Q (Pure.pure a) (Pure.pure b) := fun _ =>
  L.rc.pure ⟨h, rfl⟩

theorem SSim.bind {Q : α → β → Prop} {Q' : γ → δ → Prop} {x : StateT S (StateT H₁ m₁) α}
    {y : StateT S (StateT H₂ m₂) β} {f : α → StateT S (StateT H₁ m₁) γ}
    {g : β → StateT S (StateT H₂ m₂) δ} (hx : SSim L Q x y)
    (hk : ∀ a b, Q a b → SSim L Q' (f a) (g b)) : SSim L Q' (x >>= f) (y >>= g) := fun s =>
  L.rc.bind (hx s) fun p q h => by
    obtain ⟨hq, he⟩ := h
    show L.rc.rel _ ((f p.1).run p.2) ((g q.1).run q.2)
    rw [he]
    exact hk _ _ hq q.2

theorem SSim.mono {Q Q' : α → β → Prop} {x : StateT S (StateT H₁ m₁) α}
    {y : StateT S (StateT H₂ m₂) β} (hQ : ∀ a b, Q a b → Q' a b) (h : SSim L Q x y) :
    SSim L Q' x y := fun s =>
  L.rc.mono (fun _ _ h => ⟨hQ _ _ h.1, h.2⟩) (h s)

theorem SSim.get : SSim (S := S) L Eq (MonadStateOf.get : StateT S (StateT H₁ m₁) S)
    (MonadStateOf.get : StateT S (StateT H₂ m₂) S) := fun _ =>
  L.rc.pure ⟨rfl, rfl⟩

theorem SSim.set (s : S) : SSim L Eq (MonadStateOf.set s : StateT S (StateT H₁ m₁) PUnit)
    (MonadStateOf.set s : StateT S (StateT H₂ m₂) PUnit) := fun _ =>
  L.rc.pure ⟨rfl, rfl⟩

theorem SSim.modifyGet (f : S → α × S) :
    SSim L Eq (MonadStateOf.modifyGet f : StateT S (StateT H₁ m₁) α)
      (MonadStateOf.modifyGet f : StateT S (StateT H₂ m₂) α) := fun _ =>
  L.rc.pure ⟨rfl, rfl⟩

/-- Related actions of the consumers, lifted to the shared state. -/
theorem SSim.lift {Q : α → β → Prop} {x : StateT H₁ m₁ α} {y : StateT H₂ m₂ β}
    (h : L.rc.rel Q x y) :
    SSim (S := S) L Q (StateT.lift x) (StateT.lift y) := fun s => by
  show L.rc.rel _ (x >>= fun a => Pure.pure (a, s)) (y >>= fun b => Pure.pure (b, s))
  exact L.rc.bind h fun _ _ hab => L.rc.pure ⟨hab, rfl⟩

/-- The runs of actions on the state from the same state. -/
theorem SSim.run {Q : α → β → Prop} {f : StateT S (StateT H₁ m₁) α}
    {g : StateT S (StateT H₂ m₂) β} (h : SSim L Q f g) (s : S) :
    L.rc.rel (fun a b => Q a.1 b.1 ∧ a.2 = b.2) (f.run s) (g.run s) :=
  h s

end SSim

/-! ### Actions that may fail -/

section XSim

variable {L} {S ε₁ ε₂ α β γ δ : Type} {Qe : ε₁ → ε₂ → Prop}

theorem XSim.pure {Q : α → β → Prop} {a : α} {b : β} (h : Q a b) :
    XSim (S := S) L Qe Q (Pure.pure a) (Pure.pure b) :=
  SSim.pure (Q := ERel Qe Q) (a := .ok a) (b := .ok b) h

theorem XSim.throw {e₁ : ε₁} {e₂ : ε₂} (h : Qe e₁ e₂) :
    XSim (S := S) (α := α) (β := β) L Qe Q (throw e₁) (throw e₂) :=
  SSim.pure (Q := ERel Qe Q) (a := .error e₁) (b := .error e₂) h

theorem XSim.bind {Q : α → β → Prop} {Q' : γ → δ → Prop}
    {x : ExceptT ε₁ (StateT S (StateT H₁ m₁)) α} {y : ExceptT ε₂ (StateT S (StateT H₂ m₂)) β}
    {f : α → ExceptT ε₁ (StateT S (StateT H₁ m₁)) γ}
    {g : β → ExceptT ε₂ (StateT S (StateT H₂ m₂)) δ} (hx : XSim L Qe Q x y)
    (hk : ∀ a b, Q a b → XSim L Qe Q' (f a) (g b)) : XSim L Qe Q' (x >>= f) (y >>= g) := by
  unfold XSim
  rw [ExceptT.run_bind, ExceptT.run_bind]
  refine SSim.bind hx fun r r' h => ?_
  match r, r', h with
  | .ok a, .ok b, h => exact hk a b h
  | .error e, .error e', h => exact SSim.pure (Q := ERel Qe Q') (a := .error e) (b := .error e') h

theorem XSim.mono {Q Q' : α → β → Prop} {x : ExceptT ε₁ (StateT S (StateT H₁ m₁)) α}
    {y : ExceptT ε₂ (StateT S (StateT H₂ m₂)) β} (hQ : ∀ a b, Q a b → Q' a b)
    (h : XSim L Qe Q x y) : XSim L Qe Q' x y :=
  SSim.mono (fun r r' h => match r, r', h with
    | .ok _, .ok _, h => hQ _ _ h
    | .error _, .error _, h => h) h

/-- Actions on the state that do not fail, lifted. -/
theorem XSim.lift {Q : α → β → Prop} {x : StateT S (StateT H₁ m₁) α}
    {y : StateT S (StateT H₂ m₂) β} (h : SSim L Q x y) :
    XSim L Qe Q (ExceptT.lift x) (ExceptT.lift y) := by
  unfold XSim
  rw [ExceptT.run_lift, ExceptT.run_lift]
  show SSim L _ (x >>= fun a => Pure.pure (Except.ok a)) (y >>= fun b => Pure.pure (Except.ok b))
  exact SSim.bind h fun a b hab => SSim.pure (Q := ERel Qe Q) (a := .ok a) (b := .ok b) hab

/-- A failing action with its handler. -/
theorem XSim.tryCatch {Q : α → α → Prop} {x : ExceptT ε₁ (StateT S (StateT H₁ m₁)) α}
    {y : ExceptT ε₂ (StateT S (StateT H₂ m₂)) α}
    {f : ε₁ → ExceptT ε₁ (StateT S (StateT H₁ m₁)) α}
    {g : ε₂ → ExceptT ε₂ (StateT S (StateT H₂ m₂)) α} (hx : XSim L Qe (· = ·) x y)
    (hk : ∀ a b, Qe a b → XSim L Qe Q (f a) (g b))
    (hpure : ∀ a, Q a a) : XSim L Qe Q (tryCatch x f) (tryCatch y g) := by
  unfold XSim
  show SSim L _ (x.run >>= fun r => match r with
      | .ok a => Pure.pure (.ok a) | .error e => (f e).run)
    (y.run >>= fun r => match r with
      | .ok a => Pure.pure (.ok a) | .error e => (g e).run)
  refine SSim.bind hx fun r r' h => ?_
  match r, r', h with
  | .ok a, .ok b, h =>
    cases h
    exact SSim.pure (Q := ERel Qe Q) (a := .ok a) (b := .ok a) (hpure a)
  | .error e, .error e', h => exact hk e e' h

end XSim

end

end BSmtLib.Facts.Proofs.Reader.Param.Basic

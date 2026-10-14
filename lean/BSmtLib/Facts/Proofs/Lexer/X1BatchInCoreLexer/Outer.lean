import BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Finish

/-!
# The outer steps of the library's lexer and of `X1BatchInCore`

Between the calls of a lexer, the base of its state means nothing: every call that lexes a slice
sets it before reading it, the end of the input sets it to zero, and the other steps read only
the current location, which does not depend on it. So the two lexers are related between calls
by `Rel`: their states are equal once the base is forgotten (`zb`, `zm`). The steps that run
between calls (`InnerM`, without interruptions) are related by a coupling (`Coupled`, which is
`Simulation.ISim` from related states to results related as asked and related states): run from
related states, they give such results and states and the same consumer, as the values of one run
of pairs. This module gives the rules by which couplings are built.
-/

namespace BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Outer

open BSmtLib.Facts.Proofs.Lexer.Simulation.Couple (ISim ISim.pure ISim.bind ISim.mono ISim.ite
    ISim.get ISim.modify ISim.set ISim.lift)
open BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Core

/-- The state with its base forgotten. -/
def zb (x : XCore) : XCore := { x with base := 0 }

/-- The state of the library's lexer as one of `X1BatchInCore`, with its base
forgotten. -/
def zm (c : ZCore) : XCore := zb (coreMap 0 c)

/-- The states are equal but for the base. -/
def Rel (c : ZCore) (x : XCore) : Prop := zb x = zm c

/-- The state of the library's lexer with the base `k`. -/
def wb (k : Nat) (c : ZCore) : XCore := { coreMap 0 c with base := k }

theorem zb_coreMap (s : Nat) (c : ZCore) : zb (coreMap s c) = zm c := rfl

theorem rel_coreMap (s : Nat) (c : ZCore) : Rel c (coreMap s c) := rfl

theorem rel_wb (k : Nat) (c : ZCore) : Rel c (wb k c) := rfl

theorem eq_wb {c : ZCore} {x : XCore} (h : Rel c x) : x = wb x.base c := by
  have : ({ zb x with base := x.base } : XCore) = { zm c with base := x.base } := by rw [h]
  exact this

/-- The states are related if their fields other than the base are equal. -/
theorem rel_mk {c : ZCore} {x : XCore} (h1 : x.version = c.version)
    (h2 : x.initialVersion = c.initialVersion) (h3 : x.state = c.state)
    (h4 : x.discardedFrom = c.discardedFrom) (h4' : x.holding = c.holding)
    (h5 : x.recovers = c.recovers)
    (h6 : x.consumedDepth = c.consumedDepth) (h7 : x.lexedDepth = c.lexedDepth)
    (h8 : x.recoveryState = c.recoveryState) (h9 : x.tokenStart = c.tokenStart)
    (h10 : x.tokenContent = c.tokenContent) (h11 : x.offset = c.offset) (h12 : x.line = c.line)
    (h13 : x.lineStart = c.lineStart) (h14 : x.batch = c.batch) : Rel c x := by
  obtain ⟨⟩ := x
  obtain ⟨⟩ := c
  simp only at h1 h2 h3 h4 h4' h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  subst h1 h2 h3 h4 h4' h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  rfl

theorem rel_of_eq {c : ZCore} {x x' : XCore} (h : Rel c x) (e : zb x' = zb x) : Rel c x' :=
  e.trans h

section

variable {H : Type} {m : Type → Type} [Monad m]

/-- What a step between calls returns when run from the states. -/
abbrev runI {S α : Type} (f : StateT S (StateT H m) α) (s : S) (h : H) : m ((α × S) × H) :=
  (f.run s).run h

/--
The step `f` of the library's lexer and the step `g` of the lexer with the batch kept in its
state, run from related states with the same consumer, are the two sides of one run of pairs
whose results are related by `Rr`, whose states are related and whose consumers are the same
(`Simulation.ISim`).
-/
abbrev Coupled {α β : Type} (Rr : α → β → Prop) (f : StateT ZCore (StateT H m) α)
    (g : StateT XCore (StateT H m) β) : Prop :=
  ISim Rel (fun a b c x => Rr a b ∧ Rel c x) f g

variable [LawfulMonad m] {α β γ δ : Type}

theorem Coupled.pure {Rr : α → β → Prop} {a : α} {b : β} (hr : Rr a b) :
    Coupled (H := H) (m := m) Rr (Pure.pure a) (Pure.pure b) :=
  ISim.pure fun _ _ hx => ⟨hr, hx⟩

theorem Coupled.bind {Rr : α → β → Prop} {Rr₂ : γ → δ → Prop}
    {f : StateT ZCore (StateT H m) α} {g : StateT XCore (StateT H m) β}
    {k : α → StateT ZCore (StateT H m) γ} {k' : β → StateT XCore (StateT H m) δ}
    (hf : Coupled Rr f g) (hk : ∀ a b, Rr a b → Coupled Rr₂ (k a) (k' b)) :
    Coupled Rr₂ (f >>= k) (g >>= k') :=
  ISim.bind hf fun a b c x h => hk a b h.1 c x h.2

theorem Coupled.mono {Rr Rr' : α → β → Prop} {f : StateT ZCore (StateT H m) α}
    {g : StateT XCore (StateT H m) β} (hr : ∀ a b, Rr a b → Rr' a b) (hf : Coupled Rr f g) :
    Coupled Rr' f g :=
  ISim.mono (fun _ _ h => h) (fun a b _ _ h => ⟨hr a b h.1, h.2⟩) hf

omit [LawfulMonad m] in
theorem Coupled.ite {Rr : α → β → Prop} {p q : Prop} [Decidable p] [Decidable q] (e : p ↔ q)
    {f₁ f₂ : StateT ZCore (StateT H m) α} {g₁ g₂ : StateT XCore (StateT H m) β}
    (h₁ : p → Coupled Rr f₁ g₁) (h₂ : ¬p → Coupled Rr f₂ g₂) :
    Coupled Rr (if p then f₁ else f₂) (if q then g₁ else g₂) :=
  ISim.ite e h₁ h₂

/-- A coupling gives equal values of maps that agree on the pairs it relates. -/
theorem Coupled.map_eq {Rr : α → β → Prop} {f : StateT ZCore (StateT H m) α}
    {g : StateT XCore (StateT H m) β} {ζ : Type} (F : (α × ZCore) × H → ζ)
    (G : (β × XCore) × H → ζ)
    (e : ∀ a c h b x, Rr a b → Rel c x → F ((a, c), h) = G ((b, x), h))
    (hf : Coupled Rr f g) {c : ZCore} {x : XCore} (hx : Rel c x) (h : H) :
    F <$> runI f c h = G <$> runI g x h := by
  obtain ⟨y, h1, h2⟩ := hf c x hx h
  simp only [runI]
  rw [h1, h2, Functor.map_map, Functor.map_map]
  refine congrArg (· <$> y) (funext fun p => ?_)
  obtain ⟨⟨⟨⟨a, c'⟩, h'⟩, ⟨⟨b, x'⟩, h''⟩⟩, ⟨hr, hc⟩, hh⟩ := p
  dsimp only at hr hc hh ⊢
  subst hh
  exact e a c' h' b x' hr hc

theorem Coupled.get :
    Coupled (H := H) (m := m) Rel (getThe ZCore) (getThe XCore) :=
  ISim.mono (fun _ _ h => h) (fun a b s t h => by
    obtain ⟨hP, ha, hb⟩ := h
    subst ha hb
    exact ⟨hP, hP⟩) ISim.get

theorem Coupled.modify {f : ZCore → ZCore} {g : XCore → XCore}
    (e : ∀ c x, Rel c x → Rel (f c) (g x)) :
    Coupled (H := H) (m := m) (fun _ _ => True) (modifyThe ZCore f) (modifyThe XCore g) :=
  ISim.modify f g fun c x hx => ⟨trivial, e c x hx⟩

theorem Coupled.set {c' : ZCore} {x' : XCore} (e : Rel c' x') :
    Coupled (H := H) (m := m) (fun _ _ => True)
      (MonadStateOf.set c' : StateT ZCore (StateT H m) PUnit)
      (MonadStateOf.set x' : StateT XCore (StateT H m) PUnit) :=
  ISim.set c' x' fun _ _ _ => ⟨trivial, e⟩

/-- An action of the consumer, the same on both sides. -/
theorem Coupled.lift (a : StateT H m α) :
    Coupled Eq (monadLift a : StateT ZCore (StateT H m) α)
      (monadLift a : StateT XCore (StateT H m) α) :=
  ISim.lift a

/-- A step of `X1BatchInCore` that does not depend on the base, given
from the states mapped by `φ` exactly. -/
theorem Coupled.of_exact {Rr : α → β → Prop} {f : StateT ZCore (StateT H m) α}
    {g : StateT XCore (StateT H m) β} (φ ψ : ZCore → XCore) (ρ : α → β)
    (he : ∀ c h, (fun r => ((ρ r.1.1, ψ r.1.2), r.2)) <$> runI f c h = runI g (φ c) h)
    (hg : ∀ c x h, Rel c x → runI g x h = runI g (φ c) h)
    (hψ : ∀ c, Rel c (ψ c)) (hρ : ∀ a, Rr a (ρ a)) : Coupled Rr f g := by
  intro c x hx h
  refine ⟨(fun r => ⟨(r, ((ρ r.1.1, ψ r.1.2), r.2)), ⟨hρ _, hψ _⟩, rfl⟩) <$> runI f c h, ?_, ?_⟩
  · simp
  · change runI g x h = _
    rw [hg c x h hx, ← he, Functor.map_map]

end

end BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer.Outer

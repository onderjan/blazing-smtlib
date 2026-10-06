import BSmtLib.Proofs.X2ContentsLexer.Finish

/-!
# The outer steps of the library's lexer and of the lexer with the content buffer

Between the calls of a lexer, the base of its state means nothing: every call that lexes a slice
sets it before reading it, the end of the input sets it to zero, and the other steps read only
the current location, which does not depend on it. So the two lexers are related between calls
by `Rel`: their states are equal once the base is forgotten (`zb`, `zm`). The steps that run
between calls (`InnerM`, without interruptions) are related by a coupling (`Couple`): run from
related states, they give results related as asked, related states and the same consumer, as
the values of one run of pairs. This module gives the rules by which couplings are built.
-/

namespace BSmtLib.Proofs.X2ContentsLexer

/-- The state with its base forgotten. -/
def zb (x : XCore) : XCore := { x with base := 0 }

/-- The state of the library's lexer as one of the lexer with the content buffer, with its base
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
    (h4 : x.discard = c.discard) (h5 : x.recovers = c.recovers)
    (h6 : x.consumedDepth = c.consumedDepth) (h7 : x.lexedDepth = c.lexedDepth)
    (h8 : x.recoveryState = c.recoveryState) (h9 : x.tokenStart = c.tokenStart)
    (h10 : x.tokenContent = c.tokenContent) (h11 : x.offset = c.offset) (h12 : x.line = c.line)
    (h13 : x.lineStart = c.lineStart) (h14 : x.batch = c.batch) : Rel c x := by
  obtain ⟨⟩ := x
  obtain ⟨⟩ := c
  simp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  rfl

theorem rel_of_eq {c : ZCore} {x x' : XCore} (h : Rel c x) (e : zb x' = zb x) : Rel c x' :=
  e.trans h

section

variable {H : Type} {m : Type → Type} [Monad m]

/-- What a step between calls returns when run from the states. -/
abbrev runI {S α : Type} (f : StateT S (StateT H m) α) (s : S) (h : H) : m ((α × S) × H) :=
  (f.run s).run h

/--
The step `f` of the library's lexer and the step `g` of the lexer with the content buffer,
run from related states with the same consumer, are the two sides of one run of pairs whose
results are related by `Rr`, whose states are related and whose consumers are the same.
-/
def Couple {α β : Type} (Rr : α → β → Prop) (f : StateT ZCore (StateT H m) α)
    (g : StateT XCore (StateT H m) β) : Prop :=
  ∀ c x, Rel c x → ∀ h, ∃ y : m {p : ((α × ZCore) × H) × ((β × XCore) × H) //
      Rr p.1.1.1 p.2.1.1 ∧ Rel p.1.1.2 p.2.1.2 ∧ p.1.2 = p.2.2},
    runI f c h = (fun p => p.val.1) <$> y ∧ runI g x h = (fun p => p.val.2) <$> y

variable [LawfulMonad m] {α β γ δ : Type}

theorem Couple.pure {Rr : α → β → Prop} {a : α} {b : β} (hr : Rr a b) :
    Couple (H := H) (m := m) Rr (Pure.pure a) (Pure.pure b) := by
  intro c x hx h
  exact ⟨Pure.pure ⟨(((a, c), h), ((b, x), h)), hr, hx, rfl⟩, by simp [runI], by simp [runI]⟩

theorem Couple.bind {Rr : α → β → Prop} {Rr₂ : γ → δ → Prop}
    {f : StateT ZCore (StateT H m) α} {g : StateT XCore (StateT H m) β}
    {k : α → StateT ZCore (StateT H m) γ} {k' : β → StateT XCore (StateT H m) δ}
    (hf : Couple Rr f g) (hk : ∀ a b, Rr a b → Couple Rr₂ (k a) (k' b)) :
    Couple Rr₂ (f >>= k) (g >>= k') := by
  intro c x hx h
  obtain ⟨y, hy1, hy2⟩ := hf c x hx h
  have hk' : ∀ p : {p : ((α × ZCore) × H) × ((β × XCore) × H) //
      Rr p.1.1.1 p.2.1.1 ∧ Rel p.1.1.2 p.2.1.2 ∧ p.1.2 = p.2.2},
      ∃ y' : m {p : ((γ × ZCore) × H) × ((δ × XCore) × H) //
        Rr₂ p.1.1.1 p.2.1.1 ∧ Rel p.1.1.2 p.2.1.2 ∧ p.1.2 = p.2.2},
        runI (k p.val.1.1.1) p.val.1.1.2 p.val.1.2 = (fun q => q.val.1) <$> y' ∧
        runI (k' p.val.2.1.1) p.val.2.1.2 p.val.2.2 = (fun q => q.val.2) <$> y' := by
    intro ⟨⟨⟨⟨a, c'⟩, h'⟩, ⟨⟨b, x'⟩, h''⟩⟩, hr, hc, hh⟩
    dsimp only at hr hc hh ⊢
    subst hh
    exact hk a b hr c' x' hc h'
  obtain ⟨Y, hY⟩ := Classical.skolem.mp hk'
  refine ⟨y >>= Y, ?_, ?_⟩
  · simp only [runI, StateT.run_bind] at hy1 ⊢
    rw [hy1, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun p => (hY p).1)
  · simp only [runI, StateT.run_bind] at hy2 ⊢
    rw [hy2, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun p => (hY p).2)

theorem Couple.mono {Rr Rr' : α → β → Prop} {f : StateT ZCore (StateT H m) α}
    {g : StateT XCore (StateT H m) β} (hr : ∀ a b, Rr a b → Rr' a b) (hf : Couple Rr f g) :
    Couple Rr' f g := by
  intro c x hx h
  obtain ⟨y, h1, h2⟩ := hf c x hx h
  refine ⟨(fun p => ⟨p.val, hr _ _ p.property.1, p.property.2⟩) <$> y, ?_, ?_⟩
  · rw [h1, Functor.map_map]
  · rw [h2, Functor.map_map]

omit [LawfulMonad m] in
theorem Couple.ite {Rr : α → β → Prop} {p q : Prop} [Decidable p] [Decidable q] (e : p ↔ q)
    {f₁ f₂ : StateT ZCore (StateT H m) α} {g₁ g₂ : StateT XCore (StateT H m) β}
    (h₁ : p → Couple Rr f₁ g₁) (h₂ : ¬p → Couple Rr f₂ g₂) :
    Couple Rr (if p then f₁ else f₂) (if q then g₁ else g₂) := by
  by_cases hp : p
  · simp only [hp, e.mp hp, ↓reduceIte]; exact h₁ hp
  · have : ¬q := fun h => hp (e.mpr h)
    simp only [hp, this, ↓reduceIte]; exact h₂ hp

/-- A coupling gives equal values of maps that agree on the pairs it relates. -/
theorem Couple.map_eq {Rr : α → β → Prop} {f : StateT ZCore (StateT H m) α}
    {g : StateT XCore (StateT H m) β} {ζ : Type} (F : (α × ZCore) × H → ζ)
    (G : (β × XCore) × H → ζ)
    (e : ∀ a c h b x, Rr a b → Rel c x → F ((a, c), h) = G ((b, x), h))
    (hf : Couple Rr f g) {c : ZCore} {x : XCore} (hx : Rel c x) (h : H) :
    F <$> runI f c h = G <$> runI g x h := by
  obtain ⟨y, h1, h2⟩ := hf c x hx h
  rw [h1, h2, Functor.map_map, Functor.map_map]
  refine congrArg (· <$> y) (funext fun p => ?_)
  obtain ⟨⟨⟨⟨a, c'⟩, h'⟩, ⟨⟨b, x'⟩, h''⟩⟩, hr, hc, hh⟩ := p
  dsimp only at hr hc hh ⊢
  subst hh
  exact e a c' h' b x' hr hc

theorem Couple.get :
    Couple (H := H) (m := m) Rel (getThe ZCore) (getThe XCore) := by
  intro c x hx h
  exact ⟨Pure.pure ⟨(((c, c), h), ((x, x), h)), hx, hx, rfl⟩,
    by simp only [map_pure]; rfl,
    by simp only [map_pure]; rfl⟩

theorem Couple.modify {f : ZCore → ZCore} {g : XCore → XCore}
    (e : ∀ c x, Rel c x → Rel (f c) (g x)) :
    Couple (H := H) (m := m) (fun _ _ => True) (modifyThe ZCore f) (modifyThe XCore g) := by
  intro c x hx h
  exact ⟨Pure.pure ⟨((((), f c), h), (((), g x), h)), trivial, e c x hx, rfl⟩,
    by simp only [map_pure]; rfl,
    by simp only [map_pure]; rfl⟩

theorem Couple.set {c' : ZCore} {x' : XCore} (e : Rel c' x') :
    Couple (H := H) (m := m) (fun _ _ => True)
      (MonadStateOf.set c' : StateT ZCore (StateT H m) PUnit)
      (MonadStateOf.set x' : StateT XCore (StateT H m) PUnit) := by
  intro c x hx h
  exact ⟨Pure.pure ⟨((((), c'), h), (((), x'), h)), trivial, e, rfl⟩,
    by simp only [map_pure]; rfl,
    by simp only [map_pure]; rfl⟩

/-- An action of the consumer, the same on both sides. -/
theorem Couple.lift (a : StateT H m α) :
    Couple Eq (monadLift a : StateT ZCore (StateT H m) α)
      (monadLift a : StateT XCore (StateT H m) α) := by
  intro c x hx h
  refine ⟨(fun r => ⟨(((r.1, c), r.2), ((r.1, x), r.2)), rfl, hx, rfl⟩) <$> a.run h, ?_, ?_⟩ <;>
    simp [runI, monadLift, MonadLift.monadLift]

/-- A step of the lexer with the content buffer that does not depend on the base, given from
the states mapped by `φ` exactly. -/
theorem Couple.of_exact {Rr : α → β → Prop} {f : StateT ZCore (StateT H m) α}
    {g : StateT XCore (StateT H m) β} (φ ψ : ZCore → XCore) (ρ : α → β)
    (he : ∀ c h, (fun r => ((ρ r.1.1, ψ r.1.2), r.2)) <$> runI f c h = runI g (φ c) h)
    (hg : ∀ c x h, Rel c x → runI g x h = runI g (φ c) h)
    (hψ : ∀ c, Rel c (ψ c)) (hρ : ∀ a, Rr a (ρ a)) : Couple Rr f g := by
  intro c x hx h
  refine ⟨(fun r => ⟨(r, ((ρ r.1.1, ψ r.1.2), r.2)), hρ _, hψ _, rfl⟩) <$> runI f c h, ?_, ?_⟩
  · simp
  · rw [hg c x h hx, ← he, Functor.map_map]

end

end BSmtLib.Proofs.X2ContentsLexer

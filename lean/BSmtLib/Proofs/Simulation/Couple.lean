import BSmtLib.Proofs.Simulation.Steps

/-!
# Coupled computations

Where the two lexers' states are not related by a map, their computations are related by a
coupling: two computations correspond when they are the projections of one computation of pairs
of related values (`MCouple`). In a monad other than `Id` the two runs are not values but
computations, so the statement is that both are the projections of one computation of pairs: the
two runs agree on every effect of the monad.

The loops over a slice and the calls of the lexers run in the consumer's monad `StateT H m`, with
the lexer states passed along as values: two such actions correspond when, run from the same
consumer state, their runs are coupled with values related and the same consumer state
afterwards (`Couple`). Two actions on the lexers' states and the consumer correspond when, run
from states related by `P`, they are coupled with values and states related by `Q` (`ISim`).
-/

namespace BSmtLib.Proofs.Simulation

/-! ## Computations in a monad -/

/-- The computations `a` and `b` are the projections of one computation of pairs related by
`Rel`. -/
def MCouple {m : Type → Type} [Monad m] {α β : Type} (Rel : α → β → Prop) (a : m α) (b : m β) :
    Prop :=
  ∃ y : m {p : α × β // Rel p.1 p.2}, a = (fun p => p.val.1) <$> y ∧ b = (fun p => p.val.2) <$> y

section

variable {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ δ : Type}

theorem MCouple.map {Rel : α → β → Prop} {Rel' : γ → δ → Prop} {a : m α} {b : m β}
    (f : α → γ) (g : β → δ) (h : MCouple Rel a b) (hfg : ∀ x y, Rel x y → Rel' (f x) (g y)) :
    MCouple Rel' (f <$> a) (g <$> b) := by
  obtain ⟨y, h1, h2⟩ := h
  refine ⟨(fun p => ⟨(f p.val.1, g p.val.2), hfg _ _ p.property⟩) <$> y, ?_, ?_⟩
  · rw [h1, Functor.map_map, Functor.map_map]
  · rw [h2, Functor.map_map, Functor.map_map]

theorem MCouple.mono {Rel Rel' : α → β → Prop} {a : m α} {b : m β}
    (hR : ∀ x y, Rel x y → Rel' x y) (h : MCouple Rel a b) : MCouple Rel' a b := by
  obtain ⟨y, h1, h2⟩ := h
  refine ⟨(fun p => ⟨p.val, hR _ _ p.property⟩) <$> y, ?_, ?_⟩
  · rw [h1, Functor.map_map]
  · rw [h2, Functor.map_map]

theorem MCouple.bind {Rel : α → β → Prop} {Rel' : γ → δ → Prop} {a : m α} {b : m β}
    {k : α → m γ} {k' : β → m δ} (h : MCouple Rel a b)
    (hk : ∀ x y, Rel x y → MCouple Rel' (k x) (k' y)) : MCouple Rel' (a >>= k) (b >>= k') := by
  obtain ⟨y, h1, h2⟩ := h
  have hk' : ∀ p : {p : α × β // Rel p.1 p.2}, ∃ y' : m {q : γ × δ // Rel' q.1 q.2},
      k p.val.1 = (fun q => q.val.1) <$> y' ∧ k' p.val.2 = (fun q => q.val.2) <$> y' :=
    fun p => hk _ _ p.property
  obtain ⟨Y, hY⟩ := Classical.skolem.mp hk'
  refine ⟨y >>= Y, ?_, ?_⟩
  · rw [h1, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun p => (hY p).1)
  · rw [h2, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun p => (hY p).2)

theorem MCouple.pure {Rel : α → β → Prop} {x : α} {y : β} (h : Rel x y) :
    MCouple (m := m) Rel (Pure.pure x) (Pure.pure y) :=
  ⟨Pure.pure ⟨(x, y), h⟩, by simp, by simp⟩

/-- Equal computations. -/
theorem MCouple.refl (a : m α) : MCouple (fun x y => x = y) a a :=
  ⟨(fun x => ⟨(x, x), rfl⟩) <$> a, by simp, by simp⟩

end

/-! ## Actions of the consumer -/

section

variable {H : Type} {m : Type → Type} [Monad m] {α β γ δ : Type}

/-- The two actions, run from the same consumer state, are the projections of one computation
of pairs of values related by `Rel`, with the consumer state they both end with. -/
def Couple (Rel : α → β → Prop) (a : StateT H m α) (b : StateT H m β) : Prop :=
  ∀ h, MCouple (fun x y => Rel x.1 y.1 ∧ x.2 = y.2) (a.run h) (b.run h)

variable [LawfulMonad m]

theorem Couple.pure {Rel : α → β → Prop} {x : α} {y : β} (h : Rel x y) :
    Couple (m := m) (H := H) Rel (Pure.pure x) (Pure.pure y) := fun s => by
  simp only [StateT.run_pure]
  exact MCouple.pure ⟨h, rfl⟩

theorem Couple.bind {Rel : α → β → Prop} {Rel₂ : γ → δ → Prop} {a : StateT H m α}
    {b : StateT H m β} {k : α → StateT H m γ} {k' : β → StateT H m δ} (hab : Couple Rel a b)
    (hk : ∀ x y, Rel x y → Couple Rel₂ (k x) (k' y)) : Couple Rel₂ (a >>= k) (b >>= k') := by
  intro s
  simp only [StateT.run_bind]
  refine MCouple.bind (hab s) fun x y hxy => ?_
  obtain ⟨hr, he⟩ := hxy
  rw [he]
  exact hk _ _ hr y.2

theorem Couple.mono {Rel Rel' : α → β → Prop} {a : StateT H m α} {b : StateT H m β}
    (hR : ∀ x y, Rel x y → Rel' x y) (h : Couple Rel a b) : Couple Rel' a b := fun s =>
  MCouple.mono (fun _ _ hxy => ⟨hR _ _ hxy.1, hxy.2⟩) (h s)

/-- Mapped actions. -/
theorem Couple.map {Rel : α → β → Prop} {Rel' : γ → δ → Prop} {a : StateT H m α}
    {b : StateT H m β} (f : α → γ) (g : β → δ) (h : Couple Rel a b)
    (hfg : ∀ x y, Rel x y → Rel' (f x) (g y)) : Couple Rel' (f <$> a) (g <$> b) := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact Couple.bind h fun x y hxy => Couple.pure (hfg x y hxy)

omit [LawfulMonad m] in
/-- A `dite` on the same condition. -/
theorem Couple.dite {Rel : α → β → Prop} {c : Prop} [Decidable c] {a : c → StateT H m α}
    {b : ¬c → StateT H m α} {a' : c → StateT H m β} {b' : ¬c → StateT H m β}
    (ha : ∀ h, Couple Rel (a h) (a' h)) (hb : ∀ h, Couple Rel (b h) (b' h)) :
    Couple Rel (if h : c then a h else b h) (if h : c then a' h else b' h) := by
  by_cases h : c
  · rw [dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true (eq_true h)]
    exact ha h
  · rw [dite_eq_right_of_eq_false (eq_false h), dite_eq_right_of_eq_false (eq_false h)]
    exact hb h

/-- Equal actions. -/
theorem Couple.refl (a : StateT H m α) : Couple (fun x y => x = y) a a := fun _ =>
  MCouple.mono (fun _ _ e => ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩) (MCouple.refl _)

end

/-! ## Actions on the lexers' states -/

section

variable {H : Type} {m : Type → Type} [Monad m] {S T α β γ δ : Type}

/-- The action `f` of the first lexer on its state and the consumer and the action `g` of the
second, run from states related by `P` and the same consumer state, are the projections of one
computation of results and states related by `Q`. -/
def ISim (P : S → T → Prop) (Q : α → β → S → T → Prop)
    (f : StateT S (StateT H m) α) (g : StateT T (StateT H m) β) : Prop :=
  ∀ s t, P s t → Couple (fun a b => Q a.1 b.1 a.2 b.2) (f.run s) (g.run t)

variable [LawfulMonad m] {P : S → T → Prop}

theorem ISim.pure {Q : α → β → S → T → Prop} {a : α} {b : β}
    (hq : ∀ s t, P s t → Q a b s t) :
    ISim (H := H) (m := m) P Q (Pure.pure a) (Pure.pure b) := fun s t h => by
  simp only [StateT.run_pure]
  exact Couple.pure (hq s t h)

theorem ISim.bind {Q : α → β → S → T → Prop} {Q₂ : γ → δ → S → T → Prop}
    {f : StateT S (StateT H m) α} {g : StateT T (StateT H m) β}
    {k : α → StateT S (StateT H m) γ} {k' : β → StateT T (StateT H m) δ}
    (hf : ISim P Q f g) (hk : ∀ a b, ISim (Q a b) Q₂ (k a) (k' b)) :
    ISim P Q₂ (f >>= k) (g >>= k') := fun s t h => by
  simp only [StateT.run_bind]
  exact Couple.bind (hf s t h) fun a b hab => hk a.1 b.1 a.2 b.2 hab

theorem ISim.seq {P' : S → T → Prop} {Q₂ : γ → δ → S → T → Prop}
    {f : StateT S (StateT H m) PUnit} {g : StateT T (StateT H m) PUnit}
    {k : StateT S (StateT H m) γ} {k' : StateT T (StateT H m) δ}
    (hf : ISim P (fun _ _ => P') f g) (hk : ISim P' Q₂ k k') :
    ISim P Q₂ (f >>= fun _ => k) (g >>= fun _ => k') :=
  ISim.bind hf fun _ _ => hk

theorem ISim.get :
    ISim (H := H) (m := m) P (fun a b s t => P s t ∧ a = s ∧ b = t) (getThe S)
      (getThe T) := fun s t h => by
  show Couple _ (Pure.pure (s, s)) (Pure.pure (t, t))
  exact Couple.pure ⟨h, rfl, rfl⟩

/-- A step after reading the two states, which keeps the precondition. -/
theorem ISim.get_bind {Q : α → β → S → T → Prop}
    {k : S → StateT S (StateT H m) α} {k' : T → StateT T (StateT H m) β}
    (hk : ∀ s t, P s t → ISim P Q (k s) (k' t)) :
    ISim P Q (getThe S >>= k) (getThe T >>= k') :=
  ISim.bind ISim.get fun s t => fun s' t' h => by
    obtain ⟨hP, rfl, rfl⟩ := h
    exact hk s t hP s t hP

theorem ISim.modify {Q : Unit → Unit → S → T → Prop} (f : S → S) (g : T → T)
    (h : ∀ s t, P s t → Q () () (f s) (g t)) :
    ISim (H := H) (m := m) P Q (modifyThe S f) (modifyThe T g) := fun s t hP => by
  show Couple _ (Pure.pure (PUnit.unit, f s)) (Pure.pure (PUnit.unit, g t))
  exact Couple.pure (h s t hP)

theorem ISim.set {Q : Unit → Unit → S → T → Prop} (s' : S) (t' : T)
    (h : ∀ s t, P s t → Q () () s' t') :
    ISim (H := H) (m := m) P Q (MonadStateOf.set s' : StateT S (StateT H m) PUnit)
      (MonadStateOf.set t' : StateT T (StateT H m) PUnit) := fun s t hP => by
  show Couple _ (Pure.pure (PUnit.unit, s')) (Pure.pure (PUnit.unit, t'))
  exact Couple.pure (h s t hP)

/-- The same action of the consumer. -/
theorem ISim.lift (a : StateT H m γ) :
    ISim (H := H) (m := m) P (fun r r' s t => r = r' ∧ P s t) (monadLift a) (monadLift a) :=
  fun s t h => by
    show Couple _ (a >>= fun r => Pure.pure (r, s)) (a >>= fun r => Pure.pure (r, t))
    exact Couple.bind (Couple.refl a) fun r r' e => Couple.pure ⟨e, h⟩

omit [LawfulMonad m] in
theorem ISim.ite {Q : α → β → S → T → Prop} {c c' : Prop} [Decidable c] [Decidable c']
    {f f' : StateT S (StateT H m) α} {g g' : StateT T (StateT H m) β} (hc : c ↔ c')
    (hf : c → ISim P Q f g) (hg : ¬c → ISim P Q f' g') :
    ISim P Q (if c then f else f') (if c' then g else g') := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left (hc.mp h)]
    exact hf h
  · rw [ite_eq_right h, ite_eq_right (mt hc.mpr h)]
    exact hg h

theorem ISim.mono {P' : S → T → Prop} {Q Q' : α → β → S → T → Prop}
    {f : StateT S (StateT H m) α} {g : StateT T (StateT H m) β}
    (hP : ∀ s t, P' s t → P s t) (hQ : ∀ a b s t, Q a b s t → Q' a b s t)
    (h : ISim P Q f g) : ISim P' Q' f g := fun s t hs =>
  Couple.mono (fun _ _ hab => hQ _ _ _ _ hab) (h s t (hP s t hs))

omit [LawfulMonad m] in
theorem ISim.intro {Q : α → β → S → T → Prop}
    {f : StateT S (StateT H m) α} {g : StateT T (StateT H m) β}
    (h : ∀ s t, P s t → ISim (fun s' t' => s' = s ∧ t' = t) Q f g) : ISim P Q f g :=
  fun s t hP => h s t hP s t ⟨rfl, rfl⟩

end

end BSmtLib.Proofs.Simulation

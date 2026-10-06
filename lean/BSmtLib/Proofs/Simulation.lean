import BSmtLib.Token

/-!
# Simulation of one lexer's steps by another's

The lexers of the chain from `WRustPort` to the library's lexer run their steps in the same
monad shape: an exception `ε` (the interruption) over a state of the lexer `S` over the state of
the consumer `H`. Two such lexers whose states correspond by a map `φ` lex alike when each step of
the first, followed by `φ` on its state and `ψ` on its result, is the step of the second started
from the mapped state (`Sim`). This module gives the rules by which `Sim` is shown for code built
by `bind`, `pure`, `throw`, `if`, reads and changes of the state, and actions of the consumer.
-/

namespace BSmtLib.Proofs.Simulation

universe u

variable {m : Type → Type} [Monad m] {H ε : Type}

/-- The monad of a step: an exception over the lexer's state over the consumer's. -/
abbrev M (m : Type → Type) (H ε S : Type) := ExceptT ε (StateT S (StateT H m))

/-- What a step returns when run from the states. -/
abbrev runM {S α : Type} (f : M m H ε S α) (s : S) (h : H) : m ((Except ε α × S) × H) :=
  ((f.run.run s).run h)

/-- The result of a step with the maps applied. -/
def mapOut {S T α β : Type} (φ : S → T) (ψ : α → β) :
    (Except ε α × S) × H → (Except ε β × T) × H :=
  fun x => ((x.1.1.map ψ, φ x.1.2), x.2)

/--
The step `f` of the first lexer is simulated by the step `g` of the second: run from any states,
`f` gives what `g` gives from the state mapped by `φ`, with `φ` on the state and `ψ` on the result.
-/
def Sim {S T α β : Type} (φ : S → T) (ψ : α → β) (f : M m H ε S α) (g : M m H ε T β) : Prop :=
  ∀ s h, mapOut φ ψ <$> runM f s h = runM g (φ s) h

section

variable [LawfulMonad m] {S T α β γ δ : Type} {φ : S → T}

theorem Sim.pure {ψ : α → β} {a : α} {b : β} (e : ψ a = b) :
    Sim (m := m) (H := H) (ε := ε) φ ψ (Pure.pure a) (Pure.pure b) := by
  intro s h
  subst e
  simp [runM, mapOut, Except.map]

theorem Sim.throw {ψ : α → β} (x : ε) :
    Sim (m := m) (H := H) φ ψ (MonadExcept.throw x : M m H ε S α) (MonadExcept.throw x) := by
  intro s h
  simp [runM, mapOut, MonadExcept.throw, throwThe, MonadExceptOf.throw, ExceptT.mk,
    ExceptT.run, Except.map]

theorem Sim.bind {ψ : α → β} {χ : γ → δ} {f : M m H ε S α} {g : M m H ε T β}
    {k : α → M m H ε S γ} {k' : β → M m H ε T δ} (hf : Sim φ ψ f g)
    (hk : ∀ a, Sim φ χ (k a) (k' (ψ a))) : Sim φ χ (f >>= k) (g >>= k') := by
  intro s h
  have hf' := hf s h
  simp only [runM, ExceptT.run_bind, StateT.run_bind] at hf' ⊢
  rw [← hf']
  simp only [map_bind, bind_map_left]
  refine congrArg (_ >>= ·) (funext fun x => ?_)
  obtain ⟨⟨r, s'⟩, h'⟩ := x
  cases r with
  | error e => simp [mapOut, Except.map]
  | ok a =>
    have := hk a s' h'
    simp only [runM] at this
    simpa [mapOut, Except.map] using this

omit [LawfulMonad m] in
/-- Two steps that are the same up to the result's map: the map of the result can be changed
for an equal one. -/
theorem Sim.congr {ψ ψ' : α → β} {f : M m H ε S α} {g : M m H ε T β} (e : ∀ a, ψ a = ψ' a)
    (h : Sim φ ψ f g) : Sim φ ψ' f g := by
  have : ψ = ψ' := funext e
  subst this
  exact h

omit [LawfulMonad m] in
theorem Sim.ite {ψ : α → β} {c c' : Prop} [Decidable c] [Decidable c'] (e : c ↔ c')
    {f₁ f₂ : M m H ε S α} {g₁ g₂ : M m H ε T β} (h₁ : c → Sim φ ψ f₁ g₁)
    (h₂ : ¬c → Sim φ ψ f₂ g₂) :
    Sim φ ψ (if c then f₁ else f₂) (if c' then g₁ else g₂) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte, e.mp hc]; exact h₁ hc
  · have : ¬c' := fun h => hc (e.mpr h)
    simp only [hc, ↓reduceIte, this]; exact h₂ hc

/-- A change of the state that `φ` carries over. -/
theorem Sim.modifyGet {ψ : α → β} {f : S → α × S} {g : T → β × T}
    (e : ∀ s, g (φ s) = (ψ (f s).1, φ (f s).2)) :
    Sim (m := m) (H := H) (ε := ε) φ ψ (modifyGetThe S f) (modifyGetThe T g) := by
  intro s h
  simp [runM, mapOut, modifyGetThe, MonadStateOf.modifyGet, e, Except.map,
    ExceptT.run, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk]

/-- A change of the state that `φ` carries over. -/
theorem Sim.modify {f : S → S} {g : T → T} (e : ∀ s, g (φ s) = φ (f s)) :
    Sim (m := m) (H := H) (ε := ε) φ id (modifyThe S f) (modifyThe T g) :=
  Sim.modifyGet (f := fun s => (PUnit.unit, f s)) (g := fun t => (PUnit.unit, g t))
    fun s => by simp [e]

/-- A read of the state, whose value is mapped by `φ`. -/
theorem Sim.get : Sim (m := m) (H := H) (ε := ε) φ φ (getThe S) (getThe T) := by
  intro s h
  show mapOut φ φ <$> ((Except.ok <$> (MonadState.get : StateT S (StateT H m) S)).run s).run h =
    ((Except.ok <$> (MonadState.get : StateT T (StateT H m) T)).run (φ s)).run h
  simp [mapOut, Except.map]

/-- An action of the consumer, which does not touch the lexer's state. -/
theorem Sim.lift {ψ : α → β} {a : StateT H m α} {b : StateT H m β}
    (e : ∀ h, (fun x => (ψ x.1, x.2)) <$> a.run h = b.run h) :
    Sim (m := m) (ε := ε) φ ψ (monadLift a : M m H ε S α) (monadLift b) := by
  intro s h
  show mapOut φ ψ <$> ((Except.ok <$> StateT.lift a : StateT S (StateT H m) _).run s).run h =
    ((Except.ok <$> StateT.lift b : StateT T (StateT H m) _).run (φ s)).run h
  simp only [StateT.run_map, StateT.run_lift, StateT.run_bind, StateT.run_pure, map_bind,
    bind_map_left, ← e h]
  simp [mapOut, Except.map]

end

/-! ## Simulation under conditions on the state

`Sim` holds from every state. Where the two lexers agree only from the states that the first
reaches, `SimP P Q` says that the first step from a state satisfying `P` is simulated, and that
every value `a` it returns comes with a state satisfying `Q a`. The run of the first step is
then the values of a run in the subtype of the results that satisfy `Q`, and the run of the
second is those values mapped (`Good`). -/

/-- A result of a step whose value, if it has one, comes with a state satisfying `Q`. -/
def Good {S α : Type} (Q : α → S → Prop) (x : (Except ε α × S) × H) : Prop :=
  ∀ a, x.1.1 = .ok a → Q a x.1.2

/--
The step `f` of the first lexer from a state satisfying `P` is simulated by the step `g` of the
second, and each of its values `a` comes with a state satisfying `Q a`.
-/
def SimP {S T α β : Type} (P : S → Prop) (Q : α → S → Prop) (φ : S → T) (ψ : α → β)
    (f : M m H ε S α) (g : M m H ε T β) : Prop :=
  ∀ s, P s → ∀ h, ∃ y : m {x : (Except ε α × S) × H // Good Q x},
    runM f s h = Subtype.val <$> y ∧ runM g (φ s) h = (fun x => mapOut φ ψ x.val) <$> y

section

variable [LawfulMonad m] {S T α β γ δ : Type} {φ : S → T}

omit [LawfulMonad m] in
theorem runM_bind {f : M m H ε S α} {k : α → M m H ε S γ} (s : S) (h : H) :
    runM (f >>= k) s h = runM f s h >>= fun x =>
      match x.1.1 with
      | .ok a => runM (k a) x.1.2 x.2
      | .error e => pure ((.error e, x.1.2), x.2) := by
  simp only [runM, ExceptT.run_bind, StateT.run_bind]
  refine congrArg (_ >>= ·) (funext fun x => ?_)
  obtain ⟨⟨r, s'⟩, h'⟩ := x
  cases r <;> simp

theorem SimP.pure {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {a : α} {b : β}
    (hq : ∀ s, P s → Q a s) (e : ψ a = b) :
    SimP (m := m) (H := H) (ε := ε) P Q φ ψ (Pure.pure a) (Pure.pure b) := by
  intro s hs h
  refine ⟨Pure.pure ⟨((.ok a, s), h), fun a' ha => by cases ha; exact hq s hs⟩, ?_, ?_⟩
  · simp [runM]
  · subst e; simp [runM, mapOut, Except.map]

theorem SimP.throw {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} (x : ε) :
    SimP (m := m) (H := H) P Q φ ψ (MonadExcept.throw x : M m H ε S α)
      (MonadExcept.throw x) := by
  intro s _ h
  refine ⟨Pure.pure ⟨((.error x, s), h), fun _ ha => by cases ha⟩, ?_, ?_⟩ <;>
    simp [runM, mapOut, MonadExcept.throw, throwThe, MonadExceptOf.throw, ExceptT.mk,
      ExceptT.run, Except.map]

theorem SimP.throw_eq {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {x y : ε} (e : x = y) :
    SimP (m := m) (H := H) P Q φ ψ (MonadExcept.throw x : M m H ε S α)
      (MonadExcept.throw y) := by
  subst e
  exact SimP.throw x

theorem SimP.bind {P : S → Prop} {Q : α → S → Prop} {Q₂ : γ → S → Prop} {ψ : α → β}
    {χ : γ → δ} {f : M m H ε S α} {g : M m H ε T β} {k : α → M m H ε S γ}
    {k' : β → M m H ε T δ} (hf : SimP P Q φ ψ f g)
    (hk : ∀ a, SimP (Q a) Q₂ φ χ (k a) (k' (ψ a))) :
    SimP P Q₂ φ χ (f >>= k) (g >>= k') := by
  intro s hs h
  obtain ⟨y, hy1, hy2⟩ := hf s hs h
  have hk' : ∀ x : {x : (Except ε α × S) × H // Good Q x},
      ∃ y' : m {x' : (Except ε γ × S) × H // Good Q₂ x'},
        (match x.val.1.1 with
          | .ok a => runM (k a) x.val.1.2 x.val.2
          | .error e => Pure.pure ((.error e, x.val.1.2), x.val.2)) = Subtype.val <$> y' ∧
        (match (mapOut φ ψ x.val).1.1 with
          | .ok b => runM (k' b) (mapOut φ ψ x.val).1.2 (mapOut φ ψ x.val).2
          | .error e => Pure.pure ((.error e, (mapOut φ ψ x.val).1.2), (mapOut φ ψ x.val).2)) =
          (fun x' => mapOut φ χ x'.val) <$> y' := by
    intro ⟨⟨⟨r, s'⟩, h'⟩, hx⟩
    cases r with
    | ok a =>
      obtain ⟨y', h1, h2⟩ := hk a s' (hx a rfl) h'
      exact ⟨y', h1, by simpa [mapOut, Except.map] using h2⟩
    | error e =>
      refine ⟨Pure.pure ⟨((.error e, s'), h'), fun _ ha => by cases ha⟩, ?_, ?_⟩ <;>
        simp [mapOut, Except.map]
  obtain ⟨Y, hY⟩ := Classical.skolem.mp hk'
  refine ⟨y >>= Y, ?_, ?_⟩
  · rw [runM_bind, hy1, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun x => (hY x).1)
  · rw [runM_bind, hy2, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun x => (hY x).2)

/-- `bind` with a first step that keeps the precondition. -/
theorem SimP.seq {P : S → Prop} {Q₂ : γ → S → Prop} {ψ : α → β}
    {χ : γ → δ} {f : M m H ε S α} {g : M m H ε T β} {k : α → M m H ε S γ}
    {k' : β → M m H ε T δ} (hf : SimP P (fun _ => P) φ ψ f g)
    (hk : ∀ a, SimP P Q₂ φ χ (k a) (k' (ψ a))) :
    SimP P Q₂ φ χ (f >>= k) (g >>= k') :=
  SimP.bind hf hk

/-- A precondition can be strengthened and a postcondition weakened. -/
theorem SimP.mono {P P' : S → Prop} {Q Q' : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g : M m H ε T β} (hP : ∀ s, P' s → P s) (hQ : ∀ a s, Q a s → Q' a s)
    (hf : SimP P Q φ ψ f g) : SimP P' Q' φ ψ f g := by
  intro s hs h
  obtain ⟨y, h1, h2⟩ := hf s (hP s hs) h
  refine ⟨(fun x => ⟨x.val, fun a ha => hQ _ _ (x.property a ha)⟩) <$> y, ?_, ?_⟩
  · rw [h1, Functor.map_map]
  · rw [h2, Functor.map_map]

omit [LawfulMonad m] in
/-- The map of the result can be changed for one equal on it. -/
theorem SimP.congr {P : S → Prop} {Q : α → S → Prop} {ψ ψ' : α → β} {f : M m H ε S α}
    {g : M m H ε T β} (e : ∀ a, ψ a = ψ' a) (hf : SimP P Q φ ψ f g) : SimP P Q φ ψ' f g := by
  have : ψ = ψ' := funext e
  subst this
  exact hf

omit [LawfulMonad m] in
theorem SimP.ite {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {c c' : Prop} [Decidable c]
    [Decidable c'] (e : c ↔ c') {f₁ f₂ : M m H ε S α} {g₁ g₂ : M m H ε T β}
    (h₁ : c → SimP P Q φ ψ f₁ g₁) (h₂ : ¬c → SimP P Q φ ψ f₂ g₂) :
    SimP P Q φ ψ (if c then f₁ else f₂) (if c' then g₁ else g₂) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte, e.mp hc]; exact h₁ hc
  · have : ¬c' := fun h => hc (e.mpr h)
    simp only [hc, ↓reduceIte, this]; exact h₂ hc

omit [LawfulMonad m] in
/-- A fact in the precondition that does not depend on the state can be taken out of it. -/
theorem SimP.of_fact {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g : M m H ε T β} {F : Prop} (h : F → SimP P Q φ ψ f g) :
    SimP (fun s => P s ∧ F) Q φ ψ f g :=
  fun s hs => h hs.2 s hs.1

omit [LawfulMonad m] in
/-- The second step can be replaced by an equal one. -/
theorem SimP.congr_g {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g g' : M m H ε T β} (e : g = g') (h : SimP P Q φ ψ f g) : SimP P Q φ ψ f g' := by
  subst e
  exact h

omit [LawfulMonad m] in
theorem SimP.dite {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {c c' : Prop} [Decidable c]
    [Decidable c'] (e : c ↔ c') {f₁ : c → M m H ε S α} {f₂ : ¬c → M m H ε S α}
    {g₁ : c' → M m H ε T β} {g₂ : ¬c' → M m H ε T β}
    (h₁ : ∀ hc hc', SimP P Q φ ψ (f₁ hc) (g₁ hc'))
    (h₂ : ∀ hc hc', SimP P Q φ ψ (f₂ hc) (g₂ hc')) :
    SimP P Q φ ψ (if hc : c then f₁ hc else f₂ hc) (if hc' : c' then g₁ hc' else g₂ hc') := by
  by_cases hc : c
  · simp only [hc, dite_true, e.mp hc]; exact h₁ hc (e.mp hc)
  · have : ¬c' := fun h => hc (e.mpr h)
    simp only [hc, dite_false, this]; exact h₂ hc this

/-- A change of the state that `φ` carries over from the states satisfying `P`. -/
theorem SimP.modifyGet {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : S → α × S}
    {g : T → β × T} (e : ∀ s, P s → g (φ s) = (ψ (f s).1, φ (f s).2))
    (hq : ∀ s, P s → Q (f s).1 (f s).2) :
    SimP (m := m) (H := H) (ε := ε) P Q φ ψ (modifyGetThe S f) (modifyGetThe T g) := by
  intro s hs h
  refine ⟨Pure.pure ⟨((.ok (f s).1, (f s).2), h), fun a ha => by cases ha; exact hq s hs⟩, ?_,
    ?_⟩
  · simp [runM, modifyGetThe, MonadStateOf.modifyGet, ExceptT.run, monadLift,
      MonadLift.monadLift, ExceptT.lift, ExceptT.mk]
  · simp [runM, mapOut, modifyGetThe, MonadStateOf.modifyGet, e s hs, Except.map,
      ExceptT.run, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk]

/-- A change of the state that `φ` carries over from the states satisfying `P`. -/
theorem SimP.modify {P : S → Prop} {Q : Unit → S → Prop} {f : S → S} {g : T → T}
    (e : ∀ s, P s → g (φ s) = φ (f s)) (hq : ∀ s, P s → Q () (f s)) :
    SimP (m := m) (H := H) (ε := ε) P Q φ id (modifyThe S f) (modifyThe T g) :=
  SimP.modifyGet (f := fun s => (PUnit.unit, f s)) (g := fun t => (PUnit.unit, g t))
    (fun s hs => by simp [e s hs]) hq

/-- A read of the state, whose value is mapped by `φ`. -/
theorem SimP.get {P : S → Prop} {Q : S → S → Prop} (hq : ∀ s, P s → Q s s) :
    SimP (m := m) (H := H) (ε := ε) P Q φ φ (getThe S) (getThe T) := by
  intro s hs h
  refine ⟨Pure.pure ⟨((.ok s, s), h), fun a ha => by cases ha; exact hq s hs⟩, ?_, ?_⟩
  · show ((Except.ok <$> (MonadState.get : StateT S (StateT H m) S)).run s).run h = _
    simp
  · show ((Except.ok <$> (MonadState.get : StateT T (StateT H m) T)).run (φ s)).run h = _
    simp [mapOut, Except.map]

/-- An action of the consumer, which does not touch the lexer's state. -/
theorem SimP.lift {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {a : StateT H m α}
    {b : StateT H m β} (e : ∀ h, (fun x => (ψ x.1, x.2)) <$> a.run h = b.run h)
    (hq : ∀ x s, P s → Q x s) :
    SimP (m := m) (ε := ε) P Q φ ψ (monadLift a : M m H ε S α) (monadLift b) := by
  intro s hs h
  refine ⟨(fun x => ⟨((.ok x.1, s), x.2), fun a' ha => by cases ha; exact hq _ s hs⟩) <$> a.run h,
    ?_, ?_⟩
  · show ((Except.ok <$> StateT.lift a : StateT S (StateT H m) _).run s).run h = _
    simp only [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map]
  · show ((Except.ok <$> StateT.lift b : StateT T (StateT H m) _).run (φ s)).run h = _
    simp only [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map, ← e h]
    simp [mapOut, Except.map]

/-- A step that is simulated from every state is simulated under any conditions it keeps. -/
theorem SimP.of_sim {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g : M m H ε T β} (hf : Sim φ ψ f g)
    (hq : ∀ s, P s → ∀ h, ∃ y : m {x : (Except ε α × S) × H // Good Q x},
      runM f s h = Subtype.val <$> y) :
    SimP P Q φ ψ f g := by
  intro s hs h
  obtain ⟨y, hy⟩ := hq s hs h
  exact ⟨y, hy, by rw [← hf s h, hy, Functor.map_map]⟩

end

end BSmtLib.Proofs.Simulation

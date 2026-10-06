import BSmtLib.Token

/-!
# Simulation of one lexer's steps by another's, by a map of the states

The lexers of the chain from `WRustPort` to the library's lexer run their steps in the same
monad shape: an exception `ε` (the interruption) over a state of the lexer `S` over the state of
the consumer `H`. Two such lexers whose states correspond by a map `φ` lex alike when each step of
the first, followed by `φ` on its state and `ψ` on its result, is the step of the second started
from the mapped state (`Sim`); under conditions on the states, with an invariant for the states
the steps are interrupted in, `SimF` and `SimP`. This module gives the rules by which they are
shown for code built by `bind`, `pure`, `throw`, `tryCatch`, `if`, reads and changes of the
state, and actions of the consumer.
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

/-! ## Runs of a step -/

section

variable {S α γ : Type}

theorem runM_bind {f : M m H ε S α} {k : α → M m H ε S γ} (s : S) (h : H) :
    runM (f >>= k) s h = runM f s h >>= fun x =>
      match x.1.1 with
      | .ok a => runM (k a) x.1.2 x.2
      | .error e => pure ((.error e, x.1.2), x.2) := by
  simp only [runM, ExceptT.run_bind, StateT.run_bind]
  refine congrArg (_ >>= ·) (funext fun x => ?_)
  obtain ⟨⟨r, s'⟩, h'⟩ := x
  cases r <;> simp

theorem runM_tryCatch {f : M m H ε S α} {k : ε → M m H ε S α} (s : S) (h : H) :
    runM (tryCatch f k) s h = runM f s h >>= fun x =>
      match x.1.1 with
      | .ok a => Pure.pure ((.ok a, x.1.2), x.2)
      | .error e => runM (k e) x.1.2 x.2 := by
  simp only [runM, tryCatch, MonadExcept.tryCatch, tryCatchThe, MonadExceptOf.tryCatch,
    ExceptT.tryCatch, ExceptT.run, ExceptT.mk, StateT.run_bind]
  refine congrArg (_ >>= ·) (funext fun x => ?_)
  obtain ⟨⟨r, s'⟩, h'⟩ := x
  cases r <;> simp

theorem runM_pure (a : α) (s : S) (h : H) :
    runM (Pure.pure a : M m H ε S α) s h = Pure.pure ((.ok a, s), h) := by
  simp [runM]

theorem runM_throw (e : ε) (s : S) (h : H) :
    runM (MonadExcept.throw e : M m H ε S α) s h = Pure.pure ((.error e, s), h) := by
  simp [runM, MonadExcept.throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.run]

variable [LawfulMonad m]

theorem runM_modifyGet (f : S → α × S) (s : S) (h : H) :
    runM (modifyGetThe S f : M m H ε S α) s h = Pure.pure ((.ok (f s).1, (f s).2), h) := by
  simp [runM, modifyGetThe, MonadStateOf.modifyGet, ExceptT.run, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.mk]

theorem runM_get (s : S) (h : H) :
    runM (getThe S : M m H ε S S) s h = Pure.pure ((.ok s, s), h) := by
  show ((Except.ok <$> (MonadState.get : StateT S (StateT H m) S)).run s).run h = _
  simp

/-- Nothing runs after an interruption. -/
theorem throw_bind (e : ε) (k : α → M m H ε S γ) :
    (MonadExcept.throw e >>= k : M m H ε S γ) = MonadExcept.throw e := by
  apply ExceptT.ext
  rw [ExceptT.run_bind]
  simp [ExceptT.run_throw]

theorem runM_lift (a : StateT H m α) (s : S) (h : H) :
    runM (monadLift a : M m H ε S α) s h = (fun x => ((.ok x.1, s), x.2)) <$> a.run h := by
  show ((Except.ok <$> StateT.lift a : StateT S (StateT H m) _).run s).run h = _
  simp only [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map]

end

/-! ## Simulation under conditions on the state

`Sim` holds from every state. Where the two lexers agree only from the states that the first
reaches, `SimF I P Q` says that the first step from a state satisfying `P` is simulated, that
every value `a` it returns comes with a state satisfying `Q a`, and that every interruption
comes with a state satisfying the invariant `I`, from which a caller may go on. The run of the
first step is then the values of a run in the subtype of the results that satisfy these
(`GoodF`), and the run of the second is those values mapped. `SimP P Q` is `SimF` without an
invariant. -/

/-- A result of a step: its value, if it has one, comes with a state satisfying `Q`, and its
interruption, if it is interrupted, with a state satisfying `I`. -/
abbrev GoodF {S α : Type} (I : S → Prop) (Q : α → S → Prop) (x : (Except ε α × S) × H) : Prop :=
  (∀ a, x.1.1 = .ok a → Q a x.1.2) ∧ (∀ e, x.1.1 = .error e → I x.1.2)

/--
The step `f` of the first lexer from a state satisfying `P` is simulated by the step `g` of the
second, each of its values `a` comes with a state satisfying `Q a`, and each of its
interruptions with a state satisfying `I`.
-/
def SimF {S T α β : Type} (I : S → Prop) (P : S → Prop) (Q : α → S → Prop) (φ : S → T)
    (ψ : α → β) (f : M m H ε S α) (g : M m H ε T β) : Prop :=
  ∀ s, P s → ∀ h, ∃ y : m {x : (Except ε α × S) × H // GoodF I Q x},
    runM f s h = Subtype.val <$> y ∧ runM g (φ s) h = (fun x => mapOut φ ψ x.val) <$> y

section

variable [LawfulMonad m] {S T α β γ δ : Type} {φ : S → T} {I : S → Prop}

theorem SimF.pure {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {a : α} {b : β}
    (hq : ∀ s, P s → Q a s) (e : ψ a = b) :
    SimF (m := m) (H := H) (ε := ε) I P Q φ ψ (Pure.pure a) (Pure.pure b) := by
  intro s hs h
  refine ⟨Pure.pure ⟨((.ok a, s), h), fun a' ha => by cases ha; exact hq s hs,
    fun _ he => by cases he⟩, ?_, ?_⟩
  · simp [runM]
  · subst e; simp [runM, mapOut, Except.map]

theorem SimF.throw {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} (hi : ∀ s, P s → I s)
    (x : ε) :
    SimF (m := m) (H := H) I P Q φ ψ (MonadExcept.throw x : M m H ε S α)
      (MonadExcept.throw x) := by
  intro s hs h
  refine ⟨Pure.pure ⟨((.error x, s), h), ⟨(fun _ ha => nomatch ha), fun _ _ => hi s hs⟩⟩, ?_,
    ?_⟩ <;>
    simp [runM, mapOut, MonadExcept.throw, throwThe, MonadExceptOf.throw, ExceptT.mk,
      ExceptT.run, Except.map]

theorem SimF.bind {P : S → Prop} {Q : α → S → Prop} {Q₂ : γ → S → Prop} {ψ : α → β}
    {χ : γ → δ} {f : M m H ε S α} {g : M m H ε T β} {k : α → M m H ε S γ}
    {k' : β → M m H ε T δ} (hf : SimF I P Q φ ψ f g)
    (hk : ∀ a, SimF I (Q a) Q₂ φ χ (k a) (k' (ψ a))) :
    SimF I P Q₂ φ χ (f >>= k) (g >>= k') := by
  intro s hs h
  obtain ⟨y, hy1, hy2⟩ := hf s hs h
  have hk' : ∀ x : {x : (Except ε α × S) × H // GoodF I Q x},
      ∃ y' : m {x' : (Except ε γ × S) × H // GoodF I Q₂ x'},
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
      obtain ⟨y', h1, h2⟩ := hk a s' (hx.1 a rfl) h'
      exact ⟨y', h1, by simpa [mapOut, Except.map] using h2⟩
    | error e =>
      refine ⟨Pure.pure ⟨((.error e, s'), h'), ⟨(fun _ ha => nomatch ha),
        fun _ _ => hx.2 e rfl⟩⟩, ?_, ?_⟩ <;> simp [mapOut, Except.map]
  obtain ⟨Y, hY⟩ := Classical.skolem.mp hk'
  refine ⟨y >>= Y, ?_, ?_⟩
  · rw [runM_bind, hy1, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun x => (hY x).1)
  · rw [runM_bind, hy2, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun x => (hY x).2)

/-- `bind` with a first step that keeps the precondition. -/
theorem SimF.seq {P : S → Prop} {Q₂ : γ → S → Prop} {ψ : α → β}
    {χ : γ → δ} {f : M m H ε S α} {g : M m H ε T β} {k : α → M m H ε S γ}
    {k' : β → M m H ε T δ} (hf : SimF I P (fun _ => P) φ ψ f g)
    (hk : ∀ a, SimF I P Q₂ φ χ (k a) (k' (ψ a))) :
    SimF I P Q₂ φ χ (f >>= k) (g >>= k') :=
  SimF.bind hf hk

/-- A precondition can be strengthened and a postcondition weakened. -/
theorem SimF.mono {P P' : S → Prop} {Q Q' : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g : M m H ε T β} (hP : ∀ s, P' s → P s) (hQ : ∀ a s, Q a s → Q' a s)
    (hf : SimF I P Q φ ψ f g) : SimF I P' Q' φ ψ f g := by
  intro s hs h
  obtain ⟨y, h1, h2⟩ := hf s (hP s hs) h
  refine ⟨(fun x => ⟨x.val, fun a ha => hQ _ _ (x.property.1 a ha), x.property.2⟩) <$> y, ?_,
    ?_⟩
  · rw [h1, Functor.map_map]
  · rw [h2, Functor.map_map]

omit [LawfulMonad m] in
theorem SimF.ite {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {c c' : Prop} [Decidable c]
    [Decidable c'] (e : c ↔ c') {f₁ f₂ : M m H ε S α} {g₁ g₂ : M m H ε T β}
    (h₁ : c → SimF I P Q φ ψ f₁ g₁) (h₂ : ¬c → SimF I P Q φ ψ f₂ g₂) :
    SimF I P Q φ ψ (if c then f₁ else f₂) (if c' then g₁ else g₂) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte, e.mp hc]; exact h₁ hc
  · have : ¬c' := fun h => hc (e.mpr h)
    simp only [hc, ↓reduceIte, this]; exact h₂ hc

omit [LawfulMonad m] in
theorem SimF.dite {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {c c' : Prop} [Decidable c]
    [Decidable c'] (e : c ↔ c') {f₁ : c → M m H ε S α} {f₂ : ¬c → M m H ε S α}
    {g₁ : c' → M m H ε T β} {g₂ : ¬c' → M m H ε T β}
    (h₁ : ∀ hc hc', SimF I P Q φ ψ (f₁ hc) (g₁ hc'))
    (h₂ : ∀ hc hc', SimF I P Q φ ψ (f₂ hc) (g₂ hc')) :
    SimF I P Q φ ψ (if hc : c then f₁ hc else f₂ hc) (if hc' : c' then g₁ hc' else g₂ hc') := by
  by_cases hc : c
  · simp only [hc, dite_true, e.mp hc]; exact h₁ hc (e.mp hc)
  · have : ¬c' := fun h => hc (e.mpr h)
    simp only [hc, dite_false, this]; exact h₂ hc this

omit [LawfulMonad m] in
/-- A fact in the precondition that does not depend on the state can be taken out of it. -/
theorem SimF.of_fact {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g : M m H ε T β} {F : Prop} (h : F → SimF I P Q φ ψ f g) :
    SimF I (fun s => P s ∧ F) Q φ ψ f g :=
  fun s hs => h hs.2 s hs.1

/-- A change of the state that `φ` carries over from the states satisfying `P`. -/
theorem SimF.modifyGet {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : S → α × S}
    {g : T → β × T} (e : ∀ s, P s → g (φ s) = (ψ (f s).1, φ (f s).2))
    (hq : ∀ s, P s → Q (f s).1 (f s).2) :
    SimF (m := m) (H := H) (ε := ε) I P Q φ ψ (modifyGetThe S f) (modifyGetThe T g) := by
  intro s hs h
  refine ⟨Pure.pure ⟨((.ok (f s).1, (f s).2), h), fun a ha => by cases ha; exact hq s hs,
    fun _ he => by cases he⟩, ?_, ?_⟩
  · simp [runM, modifyGetThe, MonadStateOf.modifyGet, ExceptT.run, monadLift,
      MonadLift.monadLift, ExceptT.lift, ExceptT.mk]
  · simp [runM, mapOut, modifyGetThe, MonadStateOf.modifyGet, e s hs, Except.map,
      ExceptT.run, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk]

/-- A change of the state that `φ` carries over from the states satisfying `P`. -/
theorem SimF.modify {P : S → Prop} {Q : Unit → S → Prop} {f : S → S} {g : T → T}
    (e : ∀ s, P s → g (φ s) = φ (f s)) (hq : ∀ s, P s → Q () (f s)) :
    SimF (m := m) (H := H) (ε := ε) I P Q φ id (modifyThe S f) (modifyThe T g) :=
  SimF.modifyGet (f := fun s => (PUnit.unit, f s)) (g := fun t => (PUnit.unit, g t))
    (fun s hs => by simp [e s hs]) hq

/-- A read of the state, whose value is mapped by `φ`. -/
theorem SimF.get {P : S → Prop} {Q : S → S → Prop} (hq : ∀ s, P s → Q s s) :
    SimF (m := m) (H := H) (ε := ε) I P Q φ φ (getThe S) (getThe T) := by
  intro s hs h
  refine ⟨Pure.pure ⟨((.ok s, s), h), fun a ha => by cases ha; exact hq s hs,
    fun _ he => by cases he⟩, ?_, ?_⟩
  · show ((Except.ok <$> (MonadState.get : StateT S (StateT H m) S)).run s).run h = _
    simp
  · show ((Except.ok <$> (MonadState.get : StateT T (StateT H m) T)).run (φ s)).run h = _
    simp [mapOut, Except.map]

/-- An action of the consumer whose results come with a property: the property holds with the
state afterwards, which the action does not touch. -/
theorem SimF.liftGood {P : S → Prop} {Q' : α → Prop} {ψ : α → β} {a : StateT H m α}
    {b : StateT H m β} (e : ∀ h, (fun x => (ψ x.1, x.2)) <$> a.run h = b.run h)
    (hg : ∀ h, ∃ y : m {z : α × H // Q' z.1}, a.run h = Subtype.val <$> y) :
    SimF (m := m) (ε := ε) I P (fun x s => P s ∧ Q' x) φ ψ (monadLift a : M m H ε S α)
      (monadLift b) := by
  intro s hs h
  obtain ⟨y, hy⟩ := hg h
  refine ⟨(fun z => ⟨((.ok z.val.1, s), z.val.2), fun a' ha => by
    cases ha; exact ⟨hs, z.property⟩, fun _ he => by cases he⟩) <$> y, ?_, ?_⟩
  · show ((Except.ok <$> StateT.lift a : StateT S (StateT H m) _).run s).run h = _
    simp only [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map, hy]
  · show ((Except.ok <$> StateT.lift b : StateT T (StateT H m) _).run (φ s)).run h = _
    simp only [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map, ← e h, hy]
    simp [mapOut, Except.map]

/-- An action of the consumer, which does not touch the lexer's state. -/
theorem SimF.lift {P : S → Prop} {ψ : α → β} {a : StateT H m α} {b : StateT H m β}
    (e : ∀ h, (fun x => (ψ x.1, x.2)) <$> a.run h = b.run h) :
    SimF (m := m) (ε := ε) I P (fun _ => P) φ ψ (monadLift a : M m H ε S α) (monadLift b) :=
  SimF.mono (fun _ h => h) (fun _ _ h => h.1)
    (SimF.liftGood (Q' := fun _ => True) e fun h =>
      ⟨(fun z => ⟨z, trivial⟩) <$> a.run h, by simp⟩)

omit [LawfulMonad m] in
/-- The first step can be replaced by a variable equal to it, so that `split` reaches the
second. -/
theorem SimF.hide_left {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g : M m H ε T β} (h : ∀ F, F = f → SimF I P Q φ ψ F g) : SimF I P Q φ ψ f g :=
  h f rfl

/-- A bind whose continuations read their argument only through `o`: the first steps need only
be simulated through `o`, and the continuations on the same argument. -/
theorem SimF.bind_obs {ω : Type} [Nonempty α] {P Q : S → Prop} {Q₂ : γ → S → Prop}
    {χ : γ → δ} (o : α → ω) {f : M m H ε S α} {g : M m H ε T α} {k : α → M m H ε S γ}
    {k' : α → M m H ε T δ}
    (hf : SimF I P (fun _ => Q) φ id (o <$> f) (o <$> g))
    (hk : ∀ x y, o x = o y → k x = k y) (hk' : ∀ x y, o x = o y → k' x = k' y)
    (hs : ∀ x, SimF I Q Q₂ φ χ (k x) (k' x)) :
    SimF I P Q₂ φ χ (f >>= k) (g >>= k') := by
  classical
  let pick : ω → α := fun w =>
    if hw : ∃ y, o y = w then Classical.choose hw else Classical.choice ‹_›
  have hpick : ∀ x, o (pick (o x)) = o x := fun x => by
    simp only [pick, show ∃ y, o y = o x from ⟨x, rfl⟩, dite_true]
    exact Classical.choose_spec (⟨x, rfl⟩ : ∃ y, o y = o x)
  have e1 : f >>= k = (o <$> f) >>= fun w => k (pick w) := by
    rw [bind_map_left]
    exact congrArg (f >>= ·) (funext fun x => hk _ _ (hpick x).symm)
  have e2 : g >>= k' = (o <$> g) >>= fun w => k' (pick w) := by
    rw [bind_map_left]
    exact congrArg (g >>= ·) (funext fun x => hk' _ _ (hpick x).symm)
  rw [e1, e2]
  exact SimF.bind hf fun w => hs (pick w)

/-- A step whose interruption is caught: the handler runs from the state of the interruption,
which satisfies the invariant. -/
theorem SimF.tryCatch {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g : M m H ε T β} {k : ε → M m H ε S α} {k' : ε → M m H ε T β}
    (hf : SimF I P Q φ ψ f g) (hk : ∀ e, SimF I I Q φ ψ (k e) (k' e)) :
    SimF I P Q φ ψ (tryCatch f k) (tryCatch g k') := by
  intro s hs h
  obtain ⟨y, hy1, hy2⟩ := hf s hs h
  have hk' : ∀ x : {x : (Except ε α × S) × H // GoodF I Q x},
      ∃ y' : m {x' : (Except ε α × S) × H // GoodF I Q x'},
        (match x.val.1.1 with
          | .ok a => Pure.pure ((.ok a, x.val.1.2), x.val.2)
          | .error e => runM (k e) x.val.1.2 x.val.2) = Subtype.val <$> y' ∧
        (match (mapOut φ ψ x.val).1.1 with
          | .ok b => Pure.pure ((.ok b, (mapOut φ ψ x.val).1.2), (mapOut φ ψ x.val).2)
          | .error e => runM (k' e) (mapOut φ ψ x.val).1.2 (mapOut φ ψ x.val).2) =
          (fun x' => mapOut φ ψ x'.val) <$> y' := by
    intro ⟨⟨⟨r, s'⟩, h'⟩, hx⟩
    cases r with
    | ok a =>
      refine ⟨Pure.pure ⟨((.ok a, s'), h'), fun _ ha => by cases ha; exact hx.1 a rfl,
        fun _ he => by cases he⟩, ?_, ?_⟩ <;> simp [mapOut, Except.map]
    | error e =>
      obtain ⟨y', h1, h2⟩ := hk e s' (hx.2 e rfl) h'
      exact ⟨y', h1, by simpa [mapOut, Except.map] using h2⟩
  obtain ⟨Y, hY⟩ := Classical.skolem.mp hk'
  refine ⟨y >>= Y, ?_, ?_⟩
  · rw [runM_tryCatch, hy1, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun x => (hY x).1)
  · rw [runM_tryCatch, hy2, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun x => (hY x).2)


/-- A simulation under conditions, as an equation from a state that satisfies them. -/
theorem SimF.eq {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g : M m H ε T β} (hf : SimF I P Q φ ψ f g) {s : S} (hs : P s) (h : H) :
    mapOut φ ψ <$> runM f s h = runM g (φ s) h := by
  obtain ⟨y, h1, h2⟩ := hf s hs h
  rw [h1, h2, Functor.map_map]

end

/-- A result of a step whose value, if it has one, comes with a state satisfying `Q`. -/
def Good {S α : Type} (Q : α → S → Prop) (x : (Except ε α × S) × H) : Prop :=
  ∀ a, x.1.1 = .ok a → Q a x.1.2

/--
The step `f` of the first lexer from a state satisfying `P` is simulated by the step `g` of the
second, and each of its values `a` comes with a state satisfying `Q a`: `SimF` without an
invariant for the states of the interruptions.
-/
abbrev SimP {S T α β : Type} (P : S → Prop) (Q : α → S → Prop) (φ : S → T) (ψ : α → β)
    (f : M m H ε S α) (g : M m H ε T β) : Prop :=
  SimF (fun _ => True) P Q φ ψ f g

section

variable [LawfulMonad m] {S T α β γ δ : Type} {φ : S → T}

theorem SimP.pure {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {a : α} {b : β}
    (hq : ∀ s, P s → Q a s) (e : ψ a = b) :
    SimP (m := m) (H := H) (ε := ε) P Q φ ψ (Pure.pure a) (Pure.pure b) :=
  SimF.pure hq e

theorem SimP.throw {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} (x : ε) :
    SimP (m := m) (H := H) P Q φ ψ (MonadExcept.throw x : M m H ε S α)
      (MonadExcept.throw x) :=
  SimF.throw (fun _ _ => trivial) x

theorem SimP.throw_eq {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {x y : ε} (e : x = y) :
    SimP (m := m) (H := H) P Q φ ψ (MonadExcept.throw x : M m H ε S α)
      (MonadExcept.throw y) := by
  subst e
  exact SimP.throw x

theorem SimP.bind {P : S → Prop} {Q : α → S → Prop} {Q₂ : γ → S → Prop} {ψ : α → β}
    {χ : γ → δ} {f : M m H ε S α} {g : M m H ε T β} {k : α → M m H ε S γ}
    {k' : β → M m H ε T δ} (hf : SimP P Q φ ψ f g)
    (hk : ∀ a, SimP (Q a) Q₂ φ χ (k a) (k' (ψ a))) :
    SimP P Q₂ φ χ (f >>= k) (g >>= k') :=
  SimF.bind hf hk

/-- `bind` with a first step that keeps the precondition. -/
theorem SimP.seq {P : S → Prop} {Q₂ : γ → S → Prop} {ψ : α → β}
    {χ : γ → δ} {f : M m H ε S α} {g : M m H ε T β} {k : α → M m H ε S γ}
    {k' : β → M m H ε T δ} (hf : SimP P (fun _ => P) φ ψ f g)
    (hk : ∀ a, SimP P Q₂ φ χ (k a) (k' (ψ a))) :
    SimP P Q₂ φ χ (f >>= k) (g >>= k') :=
  SimF.bind hf hk

/-- A precondition can be strengthened and a postcondition weakened. -/
theorem SimP.mono {P P' : S → Prop} {Q Q' : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g : M m H ε T β} (hP : ∀ s, P' s → P s) (hQ : ∀ a s, Q a s → Q' a s)
    (hf : SimP P Q φ ψ f g) : SimP P' Q' φ ψ f g :=
  SimF.mono hP hQ hf

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
    SimP P Q φ ψ (if c then f₁ else f₂) (if c' then g₁ else g₂) :=
  SimF.ite e h₁ h₂

omit [LawfulMonad m] in
/-- A fact in the precondition that does not depend on the state can be taken out of it. -/
theorem SimP.of_fact {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g : M m H ε T β} {F : Prop} (h : F → SimP P Q φ ψ f g) :
    SimP (fun s => P s ∧ F) Q φ ψ f g :=
  SimF.of_fact h

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
    SimP P Q φ ψ (if hc : c then f₁ hc else f₂ hc) (if hc' : c' then g₁ hc' else g₂ hc') :=
  SimF.dite e h₁ h₂

/-- A change of the state that `φ` carries over from the states satisfying `P`. -/
theorem SimP.modifyGet {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : S → α × S}
    {g : T → β × T} (e : ∀ s, P s → g (φ s) = (ψ (f s).1, φ (f s).2))
    (hq : ∀ s, P s → Q (f s).1 (f s).2) :
    SimP (m := m) (H := H) (ε := ε) P Q φ ψ (modifyGetThe S f) (modifyGetThe T g) :=
  SimF.modifyGet e hq

/-- A change of the state that `φ` carries over from the states satisfying `P`. -/
theorem SimP.modify {P : S → Prop} {Q : Unit → S → Prop} {f : S → S} {g : T → T}
    (e : ∀ s, P s → g (φ s) = φ (f s)) (hq : ∀ s, P s → Q () (f s)) :
    SimP (m := m) (H := H) (ε := ε) P Q φ id (modifyThe S f) (modifyThe T g) :=
  SimF.modify e hq

/-- A read of the state, whose value is mapped by `φ`. -/
theorem SimP.get {P : S → Prop} {Q : S → S → Prop} (hq : ∀ s, P s → Q s s) :
    SimP (m := m) (H := H) (ε := ε) P Q φ φ (getThe S) (getThe T) :=
  SimF.get hq

/-- An action of the consumer, which does not touch the lexer's state. -/
theorem SimP.lift {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {a : StateT H m α}
    {b : StateT H m β} (e : ∀ h, (fun x => (ψ x.1, x.2)) <$> a.run h = b.run h)
    (hq : ∀ x s, P s → Q x s) :
    SimP (m := m) (ε := ε) P Q φ ψ (monadLift a : M m H ε S α) (monadLift b) :=
  SimF.mono (fun _ h => h) (fun x s h => hq x s h.1)
    (SimF.liftGood (Q' := fun _ => True) e fun h =>
      ⟨(fun z => ⟨z, trivial⟩) <$> a.run h, by simp⟩)

/-- A step whose interruption is caught: the handler runs from the state of the interruption,
which is any state. -/
theorem SimP.tryCatch {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g : M m H ε T β} {k : ε → M m H ε S α} {k' : ε → M m H ε T β}
    (hf : SimP P Q φ ψ f g) (hk : ∀ e, SimP (fun _ => True) Q φ ψ (k e) (k' e)) :
    SimP P Q φ ψ (tryCatch f k) (tryCatch g k') :=
  SimF.tryCatch hf hk

/-- A simulation under conditions, as an equation from a state that satisfies them. -/
theorem SimP.eq {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g : M m H ε T β} (hf : SimP P Q φ ψ f g) {s : S} (hs : P s) (h : H) :
    mapOut φ ψ <$> runM f s h = runM g (φ s) h :=
  SimF.eq hf hs h

/-- A step that is simulated from every state is simulated under any conditions it keeps. -/
theorem SimP.of_sim {P : S → Prop} {Q : α → S → Prop} {ψ : α → β} {f : M m H ε S α}
    {g : M m H ε T β} (hf : Sim φ ψ f g)
    (hq : ∀ s, P s → ∀ h, ∃ y : m {x : (Except ε α × S) × H // Good Q x},
      runM f s h = Subtype.val <$> y) :
    SimP P Q φ ψ f g := by
  intro s hs h
  obtain ⟨y, hy⟩ := hq s hs h
  refine ⟨(fun x => ⟨x.val, x.property, fun _ _ => trivial⟩) <$> y, ?_, ?_⟩
  · rw [hy, Functor.map_map]
  · rw [← hf s h, hy, Functor.map_map, Functor.map_map]

end

end BSmtLib.Proofs.Simulation

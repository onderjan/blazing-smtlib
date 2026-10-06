import BSmtLib.Proofs.Simulation

/-!
# Simulation of one lexer's steps by another's under a relation of states

`Simulation.SimP` relates the steps of two lexers by a map of the first lexer's states to the
second's. Where neither lexer's state determines the other's, the states are related instead:
`SimR Er P Q f g` says that the steps `f` and `g`, run from states related by `P` with the same
consumer state, give the same consumer state and either values related by `Q` with their states,
or the same interruption with states related by `Er`. In a monad other than `Id` the two runs
are not values but computations, so the statement is that both are the projections of one
computation of pairs of outcomes that are so related (`GoodR`): the two runs agree on every
effect of the monad, which only the consumer has.

The rules by which `SimR` is shown for code built by `bind`, `pure`, `throw`, `tryCatch`, `if`,
reads and changes of the state, and actions of the consumer follow, as for `SimP`; and rules for
a step of one lexer that the other does not take (`bind_left`, `bind_right`).
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation (M runM runM_bind)

variable {m : Type → Type} [Monad m] {H ε : Type}

/-- The outcomes of two steps run from the same consumer state, with the consumer state they
both end with. -/
abbrev Pair (H ε S T α β : Type) := (Except ε α × S) × (Except ε β × T) × H

/-- The outcome of the first step. -/
abbrev Pair.left {S T α β : Type} (o : Pair H ε S T α β) : (Except ε α × S) × H :=
  (o.1, o.2.2)

/-- The outcome of the second step. -/
abbrev Pair.right {S T α β : Type} (o : Pair H ε S T α β) : (Except ε β × T) × H :=
  (o.2.1, o.2.2)

/-- The two outcomes correspond: values related by `Q` with their states, or the same
interruption with states related by `Er`. -/
def GoodR' {S T α β : Type} (Er : S → T → Prop) (Q : α → β → S → T → Prop)
    (x : Except ε α × S) (y : Except ε β × T) : Prop :=
  match x.1, y.1 with
  | .ok a, .ok b => Q a b x.2 y.2
  | .error e, .error e' => e = e' ∧ Er x.2 y.2
  | _, _ => False

/-- `GoodR'` of the two outcomes of a pair. -/
def GoodR {S T α β : Type} (Er : S → T → Prop) (Q : α → β → S → T → Prop)
    (o : Pair H ε S T α β) : Prop :=
  GoodR' Er Q o.1 o.2.1

/--
The step `f` of the first lexer and the step `g` of the second, run from states related by `P`
with the same consumer state, are the projections of one computation of corresponding outcomes.
-/
def SimR {S T α β : Type} (Er : S → T → Prop) (P : S → T → Prop) (Q : α → β → S → T → Prop)
    (f : M m H ε S α) (g : M m H ε T β) : Prop :=
  ∀ s t, P s t → ∀ h, ∃ y : m {o : Pair H ε S T α β // GoodR Er Q o},
    runM f s h = (fun o => o.val.left) <$> y ∧ runM g t h = (fun o => o.val.right) <$> y

section

variable {S T α β γ δ : Type} {Er : S → T → Prop}

omit [Monad m] in
@[simp] theorem goodR_ok_ok {Q : α → β → S → T → Prop} {a : α} {b : β} {s : S} {t : T} {h : H} :
    GoodR (ε := ε) Er Q (((.ok a, s), (.ok b, t), h)) ↔ Q a b s t := Iff.rfl

omit [Monad m] in
@[simp] theorem goodR_error_error {Q : α → β → S → T → Prop} {e e' : ε} {s : S} {t : T}
    {h : H} : GoodR (ε := ε) Er Q (((.error e, s), (.error e', t), h)) ↔ e = e' ∧ Er s t :=
  Iff.rfl

variable [LawfulMonad m]

omit [LawfulMonad m] in
theorem runM_pure (a : α) (s : S) (h : H) :
    runM (Pure.pure a : M m H ε S α) s h = Pure.pure ((.ok a, s), h) := by
  simp [runM]

omit [LawfulMonad m] in
theorem runM_throw (e : ε) (s : S) (h : H) :
    runM (MonadExcept.throw e : M m H ε S α) s h = Pure.pure ((.error e, s), h) := by
  simp [runM, MonadExcept.throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.run]

theorem runM_modifyGet (f : S → α × S) (s : S) (h : H) :
    runM (modifyGetThe S f : M m H ε S α) s h = Pure.pure ((.ok (f s).1, (f s).2), h) := by
  simp [runM, modifyGetThe, MonadStateOf.modifyGet, ExceptT.run, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.mk]

theorem runM_get (s : S) (h : H) :
    runM (getThe S : M m H ε S S) s h = Pure.pure ((.ok s, s), h) := by
  show ((Except.ok <$> (MonadState.get : StateT S (StateT H m) S)).run s).run h = _
  simp

/-- Nothing runs after an interruption. -/
theorem throw_bind (e : ε) (k : α → M m H ε S β) :
    (MonadExcept.throw e >>= k : M m H ε S β) = MonadExcept.throw e := by
  apply ExceptT.ext
  rw [ExceptT.run_bind]
  simp [ExceptT.run_throw]

theorem runM_lift (a : StateT H m α) (s : S) (h : H) :
    runM (monadLift a : M m H ε S α) s h = (fun x => ((.ok x.1, s), x.2)) <$> a.run h := by
  show ((Except.ok <$> StateT.lift a : StateT S (StateT H m) _).run s).run h = _
  simp only [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map]

/-- The computation of a single pair of outcomes. -/
private def single {Q : α → β → S → T → Prop} (o : Pair H ε S T α β)
    (ho : GoodR (H := H) (ε := ε) Er Q o) : m {o : Pair H ε S T α β // GoodR Er Q o} :=
  Pure.pure ⟨o, ho⟩

theorem SimR.pure {P : S → T → Prop} {Q : α → β → S → T → Prop} {a : α} {b : β}
    (hq : ∀ s t, P s t → Q a b s t) :
    SimR (m := m) (H := H) (ε := ε) Er P Q (Pure.pure a) (Pure.pure b) := by
  intro s t hst h
  refine ⟨single ((.ok a, s), (.ok b, t), h) (hq s t hst), ?_, ?_⟩ <;>
    simp [runM_pure, single]

theorem SimR.throw {P : S → T → Prop} {Q : α → β → S → T → Prop} {e e' : ε} (he : e = e')
    (hq : ∀ s t, P s t → Er s t) :
    SimR (m := m) (H := H) Er P Q (MonadExcept.throw e : M m H ε S α) (MonadExcept.throw e') := by
  intro s t hst h
  refine ⟨single ((.error e, s), (.error e', t), h) ⟨he, hq s t hst⟩, ?_, ?_⟩ <;>
    simp [runM_throw, single]

theorem SimR.bind {P : S → T → Prop} {Q : α → β → S → T → Prop}
    {Q₂ : γ → δ → S → T → Prop} {f : M m H ε S α} {g : M m H ε T β} {k : α → M m H ε S γ}
    {k' : β → M m H ε T δ} (hf : SimR Er P Q f g)
    (hk : ∀ a b, SimR Er (Q a b) Q₂ (k a) (k' b)) : SimR Er P Q₂ (f >>= k) (g >>= k') := by
  intro s t hst h
  obtain ⟨y, hy1, hy2⟩ := hf s t hst h
  have hk' : ∀ o : {o : Pair H ε S T α β // GoodR Er Q o},
      ∃ y' : m {o' : Pair H ε S T γ δ // GoodR Er Q₂ o'},
        (match o.val.left.1.1 with
          | .ok a => runM (k a) o.val.left.1.2 o.val.left.2
          | .error e => Pure.pure ((.error e, o.val.left.1.2), o.val.left.2)) =
          (fun o' => o'.val.left) <$> y' ∧
        (match o.val.right.1.1 with
          | .ok b => runM (k' b) o.val.right.1.2 o.val.right.2
          | .error e => Pure.pure ((.error e, o.val.right.1.2), o.val.right.2)) =
          (fun o' => o'.val.right) <$> y' := by
    intro ⟨⟨⟨r, s'⟩, ⟨r', t'⟩, h'⟩, ho⟩
    cases r with
    | ok a =>
      cases r' with
      | ok b =>
        obtain ⟨y', h1, h2⟩ := hk a b s' t' ho h'
        exact ⟨y', h1, h2⟩
      | error e' => exact absurd ho id
    | error e =>
      cases r' with
      | ok b => exact absurd ho id
      | error e' =>
        refine ⟨single ((.error e, s'), (.error e', t'), h') ho, ?_, ?_⟩ <;>
          simp [single]
  obtain ⟨Y, hY⟩ := Classical.skolem.mp hk'
  refine ⟨y >>= Y, ?_, ?_⟩
  · rw [runM_bind, hy1, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun o => (hY o).1)
  · rw [runM_bind, hy2, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun o => (hY o).2)

omit [LawfulMonad m] in
theorem runM_tryCatch (f : M m H ε S α) (k : ε → M m H ε S α) (s : S) (h : H) :
    runM (tryCatch f k) s h = runM f s h >>= fun x =>
      match x.1.1 with
      | .ok a => Pure.pure ((.ok a, x.1.2), x.2)
      | .error e => runM (k e) x.1.2 x.2 := by
  simp only [runM, tryCatch]
  refine congrArg (_ >>= ·) (funext fun x => ?_)
  obtain ⟨⟨r, s'⟩, h'⟩ := x
  cases r <;> rfl

/-- A step whose interruptions are caught: the handlers run from the states the interruptions
are thrown from. -/
theorem SimR.tryCatch {Er' : S → T → Prop} {P : S → T → Prop} {Q : α → β → S → T → Prop}
    {f : M m H ε S α} {g : M m H ε T β} {k : ε → M m H ε S α} {k' : ε → M m H ε T β}
    (hf : SimR Er P Q f g) (hk : ∀ e, SimR Er' Er Q (k e) (k' e)) :
    SimR Er' P Q (tryCatch f k) (tryCatch g k') := by
  intro s t hst h
  obtain ⟨y, hy1, hy2⟩ := hf s t hst h
  have hk' : ∀ o : {o : Pair H ε S T α β // GoodR Er Q o},
      ∃ y' : m {o' : Pair H ε S T α β // GoodR Er' Q o'},
        (match o.val.left.1.1 with
          | .ok a => Pure.pure ((.ok a, o.val.left.1.2), o.val.left.2)
          | .error e => runM (k e) o.val.left.1.2 o.val.left.2) =
          (fun o' => o'.val.left) <$> y' ∧
        (match o.val.right.1.1 with
          | .ok b => Pure.pure ((.ok b, o.val.right.1.2), o.val.right.2)
          | .error e => runM (k' e) o.val.right.1.2 o.val.right.2) =
          (fun o' => o'.val.right) <$> y' := by
    intro ⟨⟨⟨r, s'⟩, ⟨r', t'⟩, h'⟩, ho⟩
    cases r with
    | ok a =>
      cases r' with
      | ok b =>
        refine ⟨single ((.ok a, s'), (.ok b, t'), h') ho, ?_, ?_⟩ <;>
          simp [single]
      | error e' => exact absurd ho id
    | error e =>
      cases r' with
      | ok b => exact absurd ho id
      | error e' =>
        obtain ⟨rfl, hEr⟩ := ho
        obtain ⟨y', h1, h2⟩ := hk e s' t' hEr h'
        exact ⟨y', h1, h2⟩
  obtain ⟨Y, hY⟩ := Classical.skolem.mp hk'
  refine ⟨y >>= Y, ?_, ?_⟩
  · rw [runM_tryCatch, hy1, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun o => (hY o).1)
  · rw [runM_tryCatch, hy2, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun o => (hY o).2)

/-- A precondition can be strengthened and the postconditions weakened. -/
theorem SimR.mono {Er' : S → T → Prop} {P P' : S → T → Prop} {Q Q' : α → β → S → T → Prop}
    {f : M m H ε S α} {g : M m H ε T β} (hP : ∀ s t, P' s t → P s t)
    (hQ : ∀ a b s t, Q a b s t → Q' a b s t) (hE : ∀ s t, Er s t → Er' s t)
    (hf : SimR Er P Q f g) : SimR Er' P' Q' f g := by
  intro s t hst h
  obtain ⟨y, h1, h2⟩ := hf s t (hP s t hst) h
  refine ⟨(fun o => ⟨o.val, ?_⟩) <$> y, ?_, ?_⟩
  · obtain ⟨⟨⟨r, s'⟩, ⟨r', t'⟩, h'⟩, ho⟩ := o
    cases r <;> cases r' <;> simp only [GoodR, GoodR'] at ho ⊢ <;>
      first | exact ⟨ho.1, hE _ _ ho.2⟩ | exact hQ _ _ _ _ ho | exact ho
  · rw [h1, Functor.map_map]
  · rw [h2, Functor.map_map]

theorem SimR.pre {P P' : S → T → Prop} {Q : α → β → S → T → Prop} {f : M m H ε S α}
    {g : M m H ε T β} (hP : ∀ s t, P' s t → P s t) (hf : SimR Er P Q f g) :
    SimR Er P' Q f g :=
  SimR.mono hP (fun _ _ _ _ h => h) (fun _ _ h => h) hf

theorem SimR.post {P : S → T → Prop} {Q Q' : α → β → S → T → Prop} {f : M m H ε S α}
    {g : M m H ε T β} (hQ : ∀ a b s t, Q a b s t → Q' a b s t) (hf : SimR Er P Q f g) :
    SimR Er P Q' f g :=
  SimR.mono (fun _ _ h => h) hQ (fun _ _ h => h) hf

omit [LawfulMonad m] in
/-- Facts of the related states can be used to show the simulation. -/
theorem SimR.intro {P : S → T → Prop} {Q : α → β → S → T → Prop} {f : M m H ε S α}
    {g : M m H ε T β}
    (hf : ∀ s₀ t₀, P s₀ t₀ → SimR Er (fun s t => P s t ∧ s = s₀ ∧ t = t₀) Q f g) :
    SimR Er P Q f g :=
  fun s t hst h => hf s t hst s t ⟨hst, rfl, rfl⟩ h

omit [LawfulMonad m] in
/-- A fact that does not depend on the states can be taken out of the precondition. -/
theorem SimR.of_fact {P : S → T → Prop} {Q : α → β → S → T → Prop} {f : M m H ε S α}
    {g : M m H ε T β} {F : Prop} (h : F → SimR Er P Q f g) :
    SimR Er (fun s t => P s t ∧ F) Q f g :=
  fun s t hst => h hst.2 s t hst.1

omit [LawfulMonad m] in
/-- A fact that does not depend on the states can be taken out of the precondition. -/
theorem SimR.of_fact' {P : S → T → Prop} {Q : α → β → S → T → Prop} {f : M m H ε S α}
    {g : M m H ε T β} {F : Prop} (h : F → SimR Er P Q f g) :
    SimR Er (fun s t => F ∧ P s t) Q f g :=
  fun s t hst => h hst.1 s t hst.2

omit [LawfulMonad m] in
/-- From no states. -/
theorem SimR.of_false {P : S → T → Prop} {Q : α → β → S → T → Prop} {f : M m H ε S α}
    {g : M m H ε T β} (h : ∀ s t, ¬P s t) : SimR Er P Q f g :=
  fun s t hst => absurd hst (h s t)

omit [LawfulMonad m] in
theorem SimR.ite {P : S → T → Prop} {Q : α → β → S → T → Prop} {c c' : Prop} [Decidable c]
    [Decidable c'] (e : c ↔ c') {f₁ f₂ : M m H ε S α} {g₁ g₂ : M m H ε T β}
    (h₁ : c → SimR Er P Q f₁ g₁) (h₂ : ¬c → SimR Er P Q f₂ g₂) :
    SimR Er P Q (if c then f₁ else f₂) (if c' then g₁ else g₂) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte, e.mp hc]; exact h₁ hc
  · have : ¬c' := fun h => hc (e.mpr h)
    simp only [hc, ↓reduceIte, this]; exact h₂ hc

omit [LawfulMonad m] in
theorem SimR.dite {P : S → T → Prop} {Q : α → β → S → T → Prop} {c c' : Prop} [Decidable c]
    [Decidable c'] (e : c ↔ c') {f₁ : c → M m H ε S α} {f₂ : ¬c → M m H ε S α}
    {g₁ : c' → M m H ε T β} {g₂ : ¬c' → M m H ε T β}
    (h₁ : ∀ hc hc', SimR Er P Q (f₁ hc) (g₁ hc'))
    (h₂ : ∀ hc hc', SimR Er P Q (f₂ hc) (g₂ hc')) :
    SimR Er P Q (if hc : c then f₁ hc else f₂ hc) (if hc' : c' then g₁ hc' else g₂ hc') := by
  by_cases hc : c
  · simp only [hc, dite_true, e.mp hc]; exact h₁ hc (e.mp hc)
  · have : ¬c' := fun h => hc (e.mpr h)
    simp only [hc, dite_false, this]; exact h₂ hc this

/-- Changes of the two states. -/
theorem SimR.modifyGet {P : S → T → Prop} {Q : α → β → S → T → Prop} {f : S → α × S}
    {g : T → β × T} (hq : ∀ s t, P s t → Q (f s).1 (g t).1 (f s).2 (g t).2) :
    SimR (m := m) (H := H) (ε := ε) Er P Q (modifyGetThe S f) (modifyGetThe T g) := by
  intro s t hst h
  refine ⟨single ((.ok (f s).1, (f s).2), (.ok (g t).1, (g t).2), h) (hq s t hst), ?_, ?_⟩ <;>
    simp [runM_modifyGet, single]

/-- Changes of the two states. -/
theorem SimR.modify {P : S → T → Prop} {Q : Unit → Unit → S → T → Prop} {f : S → S}
    {g : T → T} (hq : ∀ s t, P s t → Q () () (f s) (g t)) :
    SimR (m := m) (H := H) (ε := ε) Er P Q (modifyThe S f) (modifyThe T g) :=
  SimR.modifyGet (f := fun s => (PUnit.unit, f s)) (g := fun t => (PUnit.unit, g t)) hq

/-- Reads of the two states. -/
theorem SimR.get {P : S → T → Prop} {Q : S → T → S → T → Prop}
    (hq : ∀ s t, P s t → Q s t s t) :
    SimR (m := m) (H := H) (ε := ε) Er P Q (getThe S) (getThe T) := by
  intro s t hst h
  refine ⟨single ((.ok s, s), (.ok t, t), h) (hq s t hst), ?_, ?_⟩ <;>
    simp [runM_get, single]

/-- A change of the first state only. -/
theorem SimR.modifyGet_left {P : S → T → Prop} {Q : α → β → S → T → Prop} {f : S → α × S}
    {b : β} (hq : ∀ s t, P s t → Q (f s).1 b (f s).2 t) :
    SimR (m := m) (H := H) (ε := ε) Er P Q (modifyGetThe S f) (Pure.pure b) := by
  intro s t hst h
  refine ⟨single ((.ok (f s).1, (f s).2), (.ok b, t), h) (hq s t hst), ?_, ?_⟩ <;>
    simp [runM_modifyGet, runM_pure, single]

/-- A change of the second state only. -/
theorem SimR.modifyGet_right {P : S → T → Prop} {Q : α → β → S → T → Prop} {a : α}
    {g : T → β × T} (hq : ∀ s t, P s t → Q a (g t).1 s (g t).2) :
    SimR (m := m) (H := H) (ε := ε) Er P Q (Pure.pure a) (modifyGetThe T g) := by
  intro s t hst h
  refine ⟨single ((.ok a, s), (.ok (g t).1, (g t).2), h) (hq s t hst), ?_, ?_⟩ <;>
    simp [runM_modifyGet, runM_pure, single]

/-- A read of the first state only. -/
theorem SimR.get_left {P : S → T → Prop} {Q : S → β → S → T → Prop} {b : β}
    (hq : ∀ s t, P s t → Q s b s t) :
    SimR (m := m) (H := H) (ε := ε) Er P Q (getThe S) (Pure.pure b) := by
  intro s t hst h
  refine ⟨single ((.ok s, s), (.ok b, t), h) (hq s t hst), ?_, ?_⟩ <;>
    simp [runM_get, runM_pure, single]

/-- A read of the second state only. -/
theorem SimR.get_right {P : S → T → Prop} {Q : α → T → S → T → Prop} {a : α}
    (hq : ∀ s t, P s t → Q a t s t) :
    SimR (m := m) (H := H) (ε := ε) Er P Q (Pure.pure a) (getThe T) := by
  intro s t hst h
  refine ⟨single ((.ok a, s), (.ok t, t), h) (hq s t hst), ?_, ?_⟩ <;>
    simp [runM_get, runM_pure, single]

/-- The simulation with the two steps exchanged. -/
theorem SimR.swap {P : S → T → Prop} {Q : α → β → S → T → Prop} {f : M m H ε S α}
    {g : M m H ε T β}
    (h : SimR (fun t s => Er s t) (fun t s => P s t) (fun b a t s => Q a b s t) g f) :
    SimR Er P Q f g := by
  intro s t hst h₀
  obtain ⟨y, h1, h2⟩ := h t s hst h₀
  refine ⟨(fun o => ⟨((o.val.2.1, o.val.1, o.val.2.2)), ?_⟩) <$> y, ?_, ?_⟩
  · obtain ⟨⟨⟨r, t'⟩, ⟨r', s'⟩, h'⟩, ho⟩ := o
    cases r <;> cases r' <;> simp only [GoodR, GoodR'] at ho ⊢ <;>
      first | exact ⟨ho.1.symm, ho.2⟩ | exact ho
  · rw [h2, Functor.map_map]
  · rw [h1, Functor.map_map]

/-- A change of the first state that the second lexer does not make, followed by a step. -/
theorem SimR.modifyGet_bind_left {P : S → T → Prop} {Q : γ → δ → S → T → Prop}
    {f : S → α × S} {k : α → M m H ε S γ} {g : M m H ε T δ}
    (hk : ∀ s t, P s t → SimR Er (fun s' t' => s' = (f s).2 ∧ t' = t) Q (k (f s).1) g) :
    SimR Er P Q (modifyGetThe S f >>= k) g := by
  intro s t hst h
  obtain ⟨y, h1, h2⟩ := hk s t hst _ _ ⟨rfl, rfl⟩ h
  refine ⟨y, ?_, h2⟩
  rw [runM_bind, runM_modifyGet, pure_bind]
  exact h1

/-- A change of the second state that the first lexer does not make, followed by a step. -/
theorem SimR.modifyGet_bind_right {P : S → T → Prop} {Q : γ → δ → S → T → Prop}
    {f : M m H ε S γ} {g : T → β × T} {k' : β → M m H ε T δ}
    (hk : ∀ s t, P s t → SimR Er (fun s' t' => s' = s ∧ t' = (g t).2) Q f (k' (g t).1)) :
    SimR Er P Q f (modifyGetThe T g >>= k') := by
  intro s t hst h
  obtain ⟨y, h1, h2⟩ := hk s t hst _ _ ⟨rfl, rfl⟩ h
  refine ⟨y, h1, ?_⟩
  rw [runM_bind, runM_modifyGet, pure_bind]
  exact h2

/-- A change of the first state that the second lexer does not make, followed by a step. -/
theorem SimR.modify_bind_left {P : S → T → Prop} {Q : γ → δ → S → T → Prop}
    {f : S → S} {k : PUnit → M m H ε S γ} {g : M m H ε T δ}
    (hk : ∀ s t, P s t → SimR Er (fun s' t' => s' = f s ∧ t' = t) Q (k ⟨⟩) g) :
    SimR Er P Q (modifyThe S f >>= k) g :=
  SimR.modifyGet_bind_left (f := fun s => (PUnit.unit, f s)) hk

/-- A change of the second state that the first lexer does not make, followed by a step. -/
theorem SimR.modify_bind_right {P : S → T → Prop} {Q : γ → δ → S → T → Prop}
    {f : M m H ε S γ} {g : T → T} {k' : PUnit → M m H ε T δ}
    (hk : ∀ s t, P s t → SimR Er (fun s' t' => s' = s ∧ t' = g t) Q f (k' ⟨⟩)) :
    SimR Er P Q f (modifyThe T g >>= k') :=
  SimR.modifyGet_bind_right (g := fun t => (PUnit.unit, g t)) hk

/-- A read of the first state that the second lexer does not make, followed by a step. -/
theorem SimR.get_bind_left {P : S → T → Prop} {Q : γ → δ → S → T → Prop}
    {k : S → M m H ε S γ} {g : M m H ε T δ}
    (hk : ∀ s t, P s t → SimR Er (fun s' t' => s' = s ∧ t' = t) Q (k s) g) :
    SimR Er P Q (getThe S >>= k) g := by
  intro s t hst h
  obtain ⟨y, h1, h2⟩ := hk s t hst _ _ ⟨rfl, rfl⟩ h
  refine ⟨y, ?_, h2⟩
  rw [runM_bind, runM_get, pure_bind]
  exact h1

/-- A read of the second state that the first lexer does not make, followed by a step. -/
theorem SimR.get_bind_right {P : S → T → Prop} {Q : γ → δ → S → T → Prop}
    {f : M m H ε S γ} {k' : T → M m H ε T δ}
    (hk : ∀ s t, P s t → SimR Er (fun s' t' => s' = s ∧ t' = t) Q f (k' t)) :
    SimR Er P Q f (getThe T >>= k') := by
  intro s t hst h
  obtain ⟨y, h1, h2⟩ := hk s t hst _ _ ⟨rfl, rfl⟩ h
  refine ⟨y, h1, ?_⟩
  rw [runM_bind, runM_get, pure_bind]
  exact h2

/--
Actions of the consumer, which do not touch the lexer's states: they correspond if they are the
projections of one computation of pairs of results related by `R`.
-/
theorem SimR.lift {P : S → T → Prop} {Q : α → β → S → T → Prop} {a : StateT H m α}
    {b : StateT H m β} {Rab : α → β → Prop}
    (e : ∀ h, ∃ y : m {z : α × β × H // Rab z.1 z.2.1},
      a.run h = (fun z => (z.val.1, z.val.2.2)) <$> y ∧
        b.run h = (fun z => (z.val.2.1, z.val.2.2)) <$> y)
    (hq : ∀ x y s t, P s t → Rab x y → Q x y s t) :
    SimR (m := m) (ε := ε) Er P Q (monadLift a : M m H ε S α) (monadLift b) := by
  intro s t hst h
  obtain ⟨y, h1, h2⟩ := e h
  refine ⟨(fun z => ⟨((.ok z.val.1, s), (.ok z.val.2.1, t), z.val.2.2),
    hq _ _ s t hst z.property⟩) <$> y, ?_, ?_⟩
  · rw [runM_lift, h1, Functor.map_map, Functor.map_map]
  · rw [runM_lift, h2, Functor.map_map, Functor.map_map]

/-- Equal actions of the consumer. -/
theorem SimR.lift_eq {P : S → T → Prop} {Q : α → α → S → T → Prop} (a : StateT H m α)
    (hq : ∀ x s t, P s t → Q x x s t) :
    SimR (m := m) (ε := ε) Er P Q (monadLift a : M m H ε S α) (monadLift a) :=
  SimR.lift (Rab := fun x y => x = y)
    (fun h => ⟨(fun z => ⟨(z.1, z.1, z.2), rfl⟩) <$> a.run h, by simp, by simp⟩)
    fun x _ s t hst e => e ▸ hq x s t hst

/-- `bind` after a step whose two values are equal. -/
theorem SimR.bind_eq {P P' : S → T → Prop} {Q₂ : γ → δ → S → T → Prop} {f : M m H ε S α}
    {g : M m H ε T α} {k : α → M m H ε S γ} {k' : α → M m H ε T δ}
    (hf : SimR Er P (fun a b s t => a = b ∧ P' s t) f g)
    (hk : ∀ a, SimR Er P' Q₂ (k a) (k' a)) : SimR Er P Q₂ (f >>= k) (g >>= k') :=
  SimR.bind hf fun a _ s t hst h => by
    obtain ⟨rfl, hst'⟩ := hst
    exact hk a s t hst' h

/-- `bind` after steps without a value. -/
theorem SimR.seq {P P' : S → T → Prop} {Q₂ : γ → δ → S → T → Prop} {f : M m H ε S PUnit}
    {g : M m H ε T PUnit} {k : PUnit → M m H ε S γ} {k' : PUnit → M m H ε T δ}
    (hf : SimR Er P (fun _ _ => P') f g)
    (hk : SimR Er P' Q₂ (k ⟨⟩) (k' ⟨⟩)) : SimR Er P Q₂ (f >>= k) (g >>= k') :=
  SimR.bind hf fun _ _ => hk

/-- A step of the first lexer, written with a final `pure`. -/
theorem SimR.of_bind_pure_left {P : S → T → Prop} {Q : α → β → S → T → Prop}
    {f : M m H ε S α} {g : M m H ε T β} (h : SimR Er P Q (f >>= fun a => Pure.pure a) g) :
    SimR Er P Q f g := by
  rwa [bind_pure] at h

/-- A step of the second lexer, written with a final `pure`. -/
theorem SimR.of_bind_pure_right {P : S → T → Prop} {Q : α → β → S → T → Prop}
    {f : M m H ε S α} {g : M m H ε T β} (h : SimR Er P Q f (g >>= fun b => Pure.pure b)) :
    SimR Er P Q f g := by
  rwa [bind_pure] at h

end

/-! ## Coupled actions of the consumer

The loops over a slice and the calls of the lexer run in the consumer's monad, with the lexer
states passed along as values. Two such actions correspond when they are the projections of one
computation of pairs of related values (`Couple`). -/

section

variable {α β γ δ : Type}

/-- The two actions, run from the same consumer state, are the projections of one computation
of pairs of values related by `Rel`, with the consumer state they both end with. -/
def Couple (Rel : α → β → Prop) (a : StateT H m α) (b : StateT H m β) : Prop :=
  ∀ h, ∃ y : m {z : α × β × H // Rel z.1 z.2.1},
    a.run h = (fun z => (z.val.1, z.val.2.2)) <$> y ∧
      b.run h = (fun z => (z.val.2.1, z.val.2.2)) <$> y

variable [LawfulMonad m]

theorem Couple.pure {Rel : α → β → Prop} {x : α} {y : β} (h : Rel x y) :
    Couple (m := m) (H := H) Rel (Pure.pure x) (Pure.pure y) := fun s =>
  ⟨Pure.pure ⟨(x, y, s), h⟩, by simp, by simp⟩

theorem Couple.bind {Rel : α → β → Prop} {Rel₂ : γ → δ → Prop} {a : StateT H m α}
    {b : StateT H m β} {k : α → StateT H m γ} {k' : β → StateT H m δ} (hab : Couple Rel a b)
    (hk : ∀ x y, Rel x y → Couple Rel₂ (k x) (k' y)) : Couple Rel₂ (a >>= k) (b >>= k') := by
  intro s
  obtain ⟨y, h1, h2⟩ := hab s
  have hk' : ∀ z : {z : α × β × H // Rel z.1 z.2.1},
      ∃ y' : m {z' : γ × δ × H // Rel₂ z'.1 z'.2.1},
        (k z.val.1).run z.val.2.2 = (fun z' => (z'.val.1, z'.val.2.2)) <$> y' ∧
        (k' z.val.2.1).run z.val.2.2 = (fun z' => (z'.val.2.1, z'.val.2.2)) <$> y' :=
    fun z => hk _ _ z.property _
  obtain ⟨Y, hY⟩ := Classical.skolem.mp hk'
  refine ⟨y >>= Y, ?_, ?_⟩
  · rw [StateT.run_bind, h1, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun z => (hY z).1)
  · rw [StateT.run_bind, h2, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun z => (hY z).2)

theorem Couple.mono {Rel Rel' : α → β → Prop} {a : StateT H m α} {b : StateT H m β}
    (hR : ∀ x y, Rel x y → Rel' x y) (h : Couple Rel a b) : Couple Rel' a b := by
  intro s
  obtain ⟨y, h1, h2⟩ := h s
  refine ⟨(fun z => ⟨z.val, hR _ _ z.property⟩) <$> y, ?_, ?_⟩
  · rw [h1, Functor.map_map]
  · rw [h2, Functor.map_map]

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
theorem Couple.refl (a : StateT H m α) : Couple (fun x y => x = y) a a := fun s =>
  ⟨(fun z => ⟨(z.1, z.1, z.2), rfl⟩) <$> a.run s, by simp, by simp⟩

/-- A step of the lexers run from related states. -/
theorem SimR.couple {S T : Type} {Er P : S → T → Prop} {Q : α → β → S → T → Prop}
    {f : M m H ε S α} {g : M m H ε T β} (hf : SimR Er P Q f g) {s : S} {t : T} (hst : P s t) :
    Couple (GoodR' Er Q) (f.run.run s) (g.run.run t) := by
  intro h
  obtain ⟨y, h1, h2⟩ := hf s t hst h
  refine ⟨(fun o => ⟨(o.val.1, o.val.2.1, o.val.2.2), o.property⟩) <$> y, ?_, ?_⟩
  · show runM f s h = _
    rw [h1, Functor.map_map]
  · show runM g t h = _
    rw [h2, Functor.map_map]

end

/-- Splits the first `if` or `match` of the first step, and then the first of the second. -/
macro "split_both" : tactic =>
  `(tactic| (split <;> (refine SimR.swap ?_; split <;> refine SimR.swap ?_)))

end BSmtLib.Proofs.WRustPortX1BatchInCore

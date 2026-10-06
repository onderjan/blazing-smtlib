import BSmtLib.Proofs.X1BatchInCoreX2Contents.Steps

/-!
# The loops over a slice, in both lexers

The loops over a slice run the steps of the lexers from states they pass along by hand, in the
monad of the consumer. Two such computations of the two lexers are related by `SimH`: run from
any state of the consumer, the first gives values with a property, and the second gives the same
values mapped. The steps' simulations give it from a state whose content buffer fits its array
(`SimH.ofSimF`), also for the state a step is interrupted in, from which the loops go on.
-/

namespace BSmtLib.Proofs.X1BatchInCoreX2Contents

open BSmtLib.Proofs.Simulation

section SimH

variable {m : Type → Type} [Monad m] [LawfulMonad m] {H : Type}

/-- Run from any state of the consumer, `a` gives values that satisfy `Q`, and `b` gives the same
values mapped by `ψ`, with the same states of the consumer. -/
def SimH {α β : Type} (Q : α → Prop) (ψ : α → β) (a : StateT H m α) (b : StateT H m β) : Prop :=
  ∀ h, ∃ y : m {x : α × H // Q x.1},
    a.run h = Subtype.val <$> y ∧ b.run h = (fun x => (ψ x.val.1, x.val.2)) <$> y

theorem SimH.pure {α β : Type} {Q : α → Prop} {ψ : α → β} {a : α} {b : β} (hq : Q a)
    (e : ψ a = b) : SimH (m := m) (H := H) Q ψ (Pure.pure a) (Pure.pure b) := by
  intro h
  refine ⟨Pure.pure ⟨(a, h), hq⟩, ?_, ?_⟩ <;> simp [e]

theorem SimH.bind {α β γ δ : Type} {Q : α → Prop} {Q₂ : γ → Prop} {ψ : α → β} {χ : γ → δ}
    {a : StateT H m α} {b : StateT H m β} {k : α → StateT H m γ} {k' : β → StateT H m δ}
    (ha : SimH Q ψ a b) (hk : ∀ x, Q x → SimH Q₂ χ (k x) (k' (ψ x))) :
    SimH Q₂ χ (a >>= k) (b >>= k') := by
  intro h
  obtain ⟨y, hy1, hy2⟩ := ha h
  have hk' : ∀ x : {x : α × H // Q x.1}, ∃ y' : m {z : γ × H // Q₂ z.1},
      (k x.val.1).run x.val.2 = Subtype.val <$> y' ∧
        (k' (ψ x.val.1)).run x.val.2 = (fun z => (χ z.val.1, z.val.2)) <$> y' :=
    fun x => hk x.val.1 x.property x.val.2
  obtain ⟨Y, hY⟩ := Classical.skolem.mp hk'
  refine ⟨y >>= Y, ?_, ?_⟩
  · rw [StateT.run_bind, hy1, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun x => (hY x).1)
  · rw [StateT.run_bind, hy2, bind_map_left, map_bind]
    exact congrArg (y >>= ·) (funext fun x => (hY x).2)

theorem SimH.mono {α β : Type} {Q Q' : α → Prop} {ψ : α → β} {a : StateT H m α}
    {b : StateT H m β} (hq : ∀ x, Q x → Q' x) (ha : SimH Q ψ a b) : SimH Q' ψ a b := by
  intro h
  obtain ⟨y, h1, h2⟩ := ha h
  refine ⟨(fun x => ⟨x.val, hq _ x.property⟩) <$> y, ?_, ?_⟩
  · rw [h1, Functor.map_map]
  · rw [h2, Functor.map_map]

omit [LawfulMonad m] in
theorem SimH.ite {α β : Type} {Q : α → Prop} {ψ : α → β} {c c' : Prop} [Decidable c]
    [Decidable c'] (e : c ↔ c') {a₁ a₂ : StateT H m α} {b₁ b₂ : StateT H m β}
    (h₁ : c → SimH Q ψ a₁ b₁) (h₂ : ¬c → SimH Q ψ a₂ b₂) :
    SimH Q ψ (if c then a₁ else a₂) (if c' then b₁ else b₂) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte, e.mp hc]; exact h₁ hc
  · have : ¬c' := fun h => hc (e.mpr h)
    simp only [hc, ↓reduceIte, this]; exact h₂ hc

omit [LawfulMonad m] in
theorem SimH.dite {α β : Type} {Q : α → Prop} {ψ : α → β} {c c' : Prop} [Decidable c]
    [Decidable c'] (e : c ↔ c') {a₁ : c → StateT H m α} {a₂ : ¬c → StateT H m α}
    {b₁ : c' → StateT H m β} {b₂ : ¬c' → StateT H m β}
    (h₁ : ∀ hc hc', SimH Q ψ (a₁ hc) (b₁ hc')) (h₂ : ∀ hc hc', SimH Q ψ (a₂ hc) (b₂ hc')) :
    SimH Q ψ (if hc : c then a₁ hc else a₂ hc) (if hc' : c' then b₁ hc' else b₂ hc') := by
  by_cases hc : c
  · simp only [hc, dite_true, e.mp hc]; exact h₁ hc (e.mp hc)
  · have : ¬c' := fun h => hc (e.mpr h)
    simp only [hc, dite_false, this]; exact h₂ hc this

/-- An action of the consumer, the same in both lexers. -/
theorem SimH.same {α : Type} (a : StateT H m α) : SimH (fun _ => True) id a a := by
  intro h
  refine ⟨(fun x => ⟨x, trivial⟩) <$> a.run h, ?_, ?_⟩ <;> simp

omit [LawfulMonad m] in
/-- The second computation can be replaced by an equal one. -/
theorem SimH.congr_right {α β : Type} {Q : α → Prop} {ψ : α → β} {a : StateT H m α}
    {b b' : StateT H m β} (h : SimH Q ψ a b) (e : b = b') : SimH Q ψ a b' := by
  subst e
  exact h

/-- A step of the lexers run from a state that satisfies its precondition: the first gives its
values with states satisfying the postcondition, its interruptions with states satisfying the
invariant, and the second gives them mapped. -/
theorem SimH.ofSimF {ε S T α β : Type} {φ : S → T} {I P : S → Prop} {Q : α → S → Prop}
    {ψ : α → β} {f : M m H ε S α} {g : M m H ε T β} (hf : SimF I P Q φ ψ f g) (s : S)
    (hs : P s) :
    SimH (fun x => (∀ a, x.1 = .ok a → Q a x.2) ∧ (∀ e, x.1 = .error e → I x.2))
      (fun x => (x.1.map ψ, φ x.2)) (f.run.run s) (g.run.run (φ s)) := by
  intro h
  obtain ⟨y, h1, h2⟩ := hf s hs h
  refine ⟨(fun x => ⟨x.val, x.property⟩) <$> y, ?_, ?_⟩
  · show runM f s h = _
    rw [h1, Functor.map_map]
  · show runM g (φ s) h = _
    rw [h2, Functor.map_map]
    rfl

end SimH

/-- How lexing a slice from an index ends, in the second lexer for the first. -/
def exitMap {R E : Type} {floor : Option Nat} :
    Lexer.X2Contents.SliceExit R E floor → Lexer.X1BatchInCore.SliceExit R E floor
  | .done result => .done result
  | .stopped stop location after => .stopped stop location after

theorem coreMap_resumeAt (c : Core2) (location : Location) (position : Nat) :
    coreMap (c.resumeAt location position) = (coreMap c).resumeAt location position := by
  simp only [coreMap, Lexer.X2Contents.LexerCore.resumeAt, Lexer.X1BatchInCore.LexerCore.resumeAt,
    contentBytes_clear]

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  (hblind : ContentBlind H m R E)
include hblind

theorem lexSliceRun_sim {floor : Option Nat} (input : ByteSlice) (position : Nat)
    (fnResult : Except (Lexer.Failure E) (ControlFlow R)) (core : S2 floor 0)
    (hc : BFits core) :
    SimH (fun x => BFits x.2) (fun x => (exitMap x.1, boundMap x.2))
      (Lexer.X2Contents.lexSliceRun (H := H) (m := m) input position fnResult core)
      (Lexer.X1BatchInCore.lexSliceRun input position fnResult (boundMap core)) := by
  rw [Lexer.X2Contents.lexSliceRun.eq_def, Lexer.X1BatchInCore.lexSliceRun.eq_def]
  refine SimH.dite Iff.rfl (fun _ _ => ?_) fun hflush _ => ?_
  · -- the batch is handed over
    refine SimH.bind (SimH.ofSimF (flushBatch_sim hblind) core hc) fun x hx => ?_
    obtain ⟨r, c⟩ := x
    cases r with
    | ok u => exact SimH.pure (hx.1 u rfl) rfl
    | error i =>
      obtain ⟨result, location, after⟩ := i
      cases result with
      | ok stop => exact SimH.pure (hx.2 _ rfl) rfl
      | error cause => exact SimH.pure (hx.2 _ rfl) rfl
  · -- a step
    refine SimH.bind (SimH.ofSimF (lexStep_sim hblind input position _ _ _ _ _ _ _) _ hc)
      fun x hx => ?_
    obtain ⟨r, c⟩ := x
    cases r with
    | ok next =>
      obtain ⟨next, hnext⟩ := next
      exact lexSliceRun_sim input next fnResult _ (hx.1 _ rfl)
    | error i =>
      obtain ⟨result, location, after⟩ := i
      cases result with
      | ok stop => exact SimH.pure (hx.2 _ rfl) rfl
      | error cause => exact lexSliceRun_sim input position _ _ (hx.2 _ rfl)
termination_by (input.size - position, match fnResult with | .ok _ => 1 | .error _ => 0)
decreasing_by
  all_goals simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hflush
  · apply Prod.Lex.right
    cases fnResult <;> simp_all
  · apply Prod.Lex.left
    omega

theorem lexSliceFrom_sim (input : ByteSlice) (initialOffset floor : Nat) (hfloor) (position : Nat)
    (fnResult : Except (Lexer.Failure E) (ControlFlow R)) (core : S2 (some floor) 0)
    (hc : BFits core) :
    SimH (fun x => Fits x.2.tokenContent) (fun x => (x.1, coreMap x.2))
      (Lexer.X2Contents.lexSliceFrom (H := H) (m := m) input initialOffset floor hfloor position
        fnResult core)
      (Lexer.X1BatchInCore.lexSliceFrom input initialOffset floor hfloor position fnResult
        (boundMap core)) := by
  rw [Lexer.X2Contents.lexSliceFrom.eq_def, Lexer.X1BatchInCore.lexSliceFrom.eq_def]
  refine SimH.bind (lexSliceRun_sim hblind input position fnResult core hc) fun x hx => ?_
  obtain ⟨exit, c⟩ := x
  cases exit with
  | done result => exact SimH.pure hx rfl
  | stopped stop location after =>
    cases stop with
    | relex =>
      refine SimH.dite Iff.rfl (fun _ _ => ?_) fun _ _ =>
        SimH.pure (fits_clear _) (by simp only [coreMap_resumeAt]; rfl)
      refine SimH.congr_right (lexSliceFrom_sim input initialOffset location.offset _ _ _ _
        (fits_clear _)) ?_
      congr 1
      exact Subtype.ext (coreMap_resumeAt _ _ _)
    | finished r => exact SimH.pure (fits_clear _) (by simp only [coreMap_resumeAt]; rfl)
termination_by input.size + 1 - (floor + 1 - initialOffset)
decreasing_by
  have := after floor rfl
  omega

theorem lexSliceInner_sim (input : ByteSlice) (c : Core2) (hc : Fits c.tokenContent) :
    SimH (fun x => Fits x.2.tokenContent) (fun x => (x.1, coreMap x.2))
      ((Lexer.X2Contents.lexSliceInner (H := H) (m := m) (R := R) (E := E) input).run c)
      ((Lexer.X1BatchInCore.lexSliceInner input).run (coreMap c)) :=
  lexSliceFrom_sim hblind input _ _ _ 0 _ _ hc

end

end BSmtLib.Proofs.X1BatchInCoreX2Contents

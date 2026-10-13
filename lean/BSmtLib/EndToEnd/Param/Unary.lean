import BSmtLib.EndToEnd.Param.Flagged

/-!
# What the lexer does after its consumer fails

On the consumer `Flagged consumer`, a step of the library's lexer keeps three facts (`UL`):
- while nothing went wrong, the lexer's version is the version of the last cursor the consumer
  gave back, so every cursor it hands over is in that version;
- once the consumer has answered an error, the step is interrupted by that error, the error
  `none` if the consumer was handed whitespace or a comment there (`Flagged.layout`), with the
  batch empty, so that the loop over the slice hands nothing over again and fails;
- the consumer is not called after it went wrong, nor handed a cursor in another version than
  its own (`Flagged.spoiled` stays as it was).

So a call of the lexer whose consumer answered an error fails (`lexSliceStep_flag`,
`lexEofStep_flag`): a call that does not fail has a consumer that answered no error and was
handed cursors in the version it asked for. The facts are proved for each function of the lexer
from how it is built, as in step 1, by the rules below and the tactic `usim`.
-/

namespace BSmtLib.EndToEnd.Param

open BSmtLib.Lexer BSmtLib.Lexer.Internal
open BSmtLib.Proofs.Adapter

section

variable {consumer : Spec.Lexer.Consumer} {floor : Option Nat} {low : Nat} {α β : Type}

/-- The lexer's monad on the consumer `Flagged consumer`. -/
abbrev FM (consumer : Spec.Lexer.Consumer) (floor : Option Nat) (low : Nat) (α : Type) :=
  LexM (Flagged consumer) AnswerM consumer.Result (Option consumer.Error) floor low α

/-- The run of a step from the lexer's state, the consumer's and the tokens taken. -/
abbrev frun (f : FM consumer floor low α) (s : {c : LexerCore // c.Bound floor low})
    (fl : Flagged consumer) (l : List Spec.Lexer.Handed) :=
  ((f.run.run s).run fl).run l

/-- The step is interrupted by an error of the consumer: the error `none` if the call at which
the consumer went wrong was handed whitespace or a comment (`layout`). -/
def ConsumerThrow {R E : Type} {floor : Option Nat} {α : Type} (layout : Bool)
    (x : Except (Interrupted R (Option E) floor) α) : Prop :=
  ∃ i, x = .error i ∧ ∃ e, i.result = .error (.consumer e) ∧ (layout = true → e = none)

/-- From a state where nothing went wrong and the versions agree: if nothing went wrong after,
the versions agree; if the consumer answered an error, the step is interrupted by it with the
batch empty; and the consumer was neither called after that nor handed a cursor in another
version. -/
def UL (f : FM consumer floor low α) : Prop :=
  ∀ s fl l, fl.errored = false → s.val.version = fl.version →
    ((frun f s fl l).1.2.errored = false →
        (frun f s fl l).1.1.2.val.version = (frun f s fl l).1.2.version) ∧
    ((frun f s fl l).1.2.errored = true →
        ConsumerThrow (frun f s fl l).1.2.layout (frun f s fl l).1.1.1 ∧
          (frun f s fl l).1.1.2.val.batch.len = 0) ∧
    (frun f s fl l).1.2.spoiled = fl.spoiled

theorem frun_bind (x : FM consumer floor low α) (k : α → FM consumer floor low β) (s fl l) :
    frun (x >>= k) s fl l =
      match frun x s fl l with
      | (((.ok a, s'), fl'), l') => frun (k a) s' fl' l'
      | (((.error e, s'), fl'), l') => (((.error e, s'), fl'), l') := by
  simp only [frun, ExceptT.run_bind, StateT.run_bind]
  rcases ((x.run.run s).run fl).run l with ⟨⟨⟨r, s'⟩, fl'⟩, l'⟩
  cases r <;> rfl

theorem UL.pure (a : α) : UL (Pure.pure a : FM consumer floor low α) :=
  fun _ _ _ he hv => ⟨fun _ => hv, fun h => (by
    have h' : true = false := h.symm.trans he; cases h'),
    rfl⟩

theorem UL.throw (i : Interrupted consumer.Result (Option consumer.Error) floor) :
    UL (MonadExcept.throw i : FM consumer floor low α) :=
  fun _ _ _ he hv => ⟨fun _ => hv, fun h => (by
    have h' : true = false := h.symm.trans he; cases h'),
    rfl⟩

theorem UL.bind {x : FM consumer floor low α} {k : α → FM consumer floor low β} (hx : UL x)
    (hk : ∀ a, UL (k a)) : UL (x >>= k) := by
  intro s fl l he hv
  rw [frun_bind]
  obtain ⟨h₁, h₂, h₃⟩ := hx s fl l he hv
  rcases hrun : frun x s fl l with ⟨⟨⟨r, s'⟩, fl'⟩, l'⟩
  rw [hrun] at h₁ h₂ h₃
  cases r with
  | error e =>
    refine ⟨h₁, fun h => ?_, h₃⟩
    obtain ⟨⟨i, hi, hc⟩, hb⟩ := h₂ h
    cases hi
    exact ⟨⟨_, rfl, hc⟩, hb⟩
  | ok a =>
    cases he' : fl'.errored with
    | true =>
      obtain ⟨⟨i, hi, -⟩, -⟩ := h₂ he'
      cases hi
    | false =>
      obtain ⟨k₁, k₂, k₃⟩ := hk a s' fl' l' he' (h₁ he')
      exact ⟨k₁, k₂, k₃.trans h₃⟩

theorem UL.getThe : UL (getThe {c : LexerCore // c.Bound floor low} :
    FM consumer floor low {c : LexerCore // c.Bound floor low}) :=
  fun _ _ _ he hv => ⟨fun _ => hv, fun h => (by
    have h' : true = false := h.symm.trans (by assumption); cases h'), rfl⟩

theorem UL.modifyThe
    (f : {c : LexerCore // c.Bound floor low} → {c : LexerCore // c.Bound floor low})
    (hf : ∀ c, (f c).val.version = c.val.version) :
    UL (modifyThe {c : LexerCore // c.Bound floor low} f : FM consumer floor low PUnit) :=
  fun s _ _ he hv => ⟨fun _ => (hf s).trans hv, fun h => (by
    have h' : true = false := h.symm.trans (by assumption); cases h'), rfl⟩

theorem UL.modifyGetThe
    (f : {c : LexerCore // c.Bound floor low} → α × {c : LexerCore // c.Bound floor low})
    (hf : ∀ c, (f c).2.val.version = c.val.version) :
    UL (modifyGetThe {c : LexerCore // c.Bound floor low} f : FM consumer floor low α) :=
  fun s _ _ he hv => ⟨fun _ => (hf s).trans hv, fun h => (by
    have h' : true = false := h.symm.trans (by assumption); cases h'), rfl⟩

theorem UL.ite {c : Prop} [Decidable c] {a b : FM consumer floor low α} (ha : c → UL a)
    (hb : ¬c → UL b) : UL (if c then a else b) := by
  by_cases h : c
  · rw [ite_eq_left h]; exact ha h
  · rw [ite_eq_right h]; exact hb h

theorem UL.dite {c : Prop} [Decidable c] {a : c → FM consumer floor low α}
    {b : ¬c → FM consumer floor low α} (ha : ∀ h, UL (a h)) (hb : ∀ h, UL (b h)) :
    UL (if h : c then a h else b h) := by
  by_cases h : c
  · rw [dite_eq_left_of_eq_true (eq_true h)]; exact ha h
  · rw [dite_eq_right_of_eq_false (eq_false h)]; exact hb h

end

/-! ## The tactic -/

open Lean Meta Elab Tactic in
/-- The goal's computation, the last argument. -/
def usimSide (target : Expr) : Option Expr :=
  target.getAppArgs.back?

open Lean Meta Elab Tactic in
/-- The goal with its computation replaced. -/
def usimWith (target f : Expr) : Expr :=
  let args := target.getAppArgs
  mkAppN target.getAppFn (args.set! (args.size - 1) f)

/-- The lemma `f_usim` for the function `f` at the head of the goal's computation, applied. -/
syntax "usim_named" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| usim_named) => withMainContext do
    let some f := usimSide (← instantiateMVars (← getMainTarget))
      | throwError "usim_named: no computation"
    let .const name _ := f.getAppFn
      | throwError "usim_named: the computation is no function's application"
    let .str _ last := name | throwError "usim_named: unnamed function {name}"
    let lemma := (`BSmtLib.EndToEnd.Param).str (last ++ "_usim")
    unless (← getEnv).contains lemma do throwError "usim_named: no lemma {lemma}"
    let goals ← (← getMainGoal).apply (← mkConstWithFreshMVarLevels lemma)
    let mut open_ := #[]
    for goal in goals do
      unless ← goal.isAssigned do
        let rest ← Lean.Elab.Tactic.run goal (evalTactic (← `(tactic|
          first | assumption | (intros; rfl) | skip)))
        open_ := open_ ++ rest.toArray
    replaceMainGoal open_.toList

/-- A local definition: a join point with the hypothesis for all its arguments, or a local
definition of the context. -/
syntax "usim_let" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| usim_let) => withMainContext do
    let mvarId ← getMainGoal
    let target ← instantiateMVars (← mvarId.getType)
    let some (.letE name type value body _) := usimSide target
      | throwError "usim_let: no local definition"
    let joinPoint : MetaM (Option (List MVarId)) := do
      let .forallE .. := type.consumeMData | return none
      if ← isProp type then return none
      try
        withLetDecl name type value fun j => do
          let hypType ← forallTelescope type fun rs result => do
            unless ← isDefEq result (← inferType (.letE name type value body false)) do
              throwError "usim_let: not a join point"
            mkForallFVars rs (usimWith target (mkAppN j rs))
          let _ ← inferType hypType
          let proof ← mkFreshExprSyntheticOpaqueMVar hypType
          withLocalDeclD `hjp hypType fun hyp => do
            let main ← mkFreshExprSyntheticOpaqueMVar (usimWith target (body.instantiate1 j))
            let val := mkApp (← mkLambdaFVars #[hyp] main) proof
            mvarId.assign (← mkLetFVars #[j] val)
            pure (some [proof.mvarId!, main.mvarId!])
      catch _ => pure none
    if let some goals ← joinPoint then
      replaceMainGoal goals
    else
      let goal ← withLetDecl name type value fun x => do
        let goal ← mkFreshExprSyntheticOpaqueMVar (usimWith target (body.instantiate1 x))
        mvarId.assign (← mkLetFVars #[x] goal)
        pure goal
      replaceMainGoal [goal.mvarId!]

/-- The hypothesis of a join point for the goal's call of it. -/
syntax "usim_hyp" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| usim_hyp) => withMainContext do
    let mvarId ← getMainGoal
    let some f := usimSide (← instantiateMVars (← mvarId.getType))
      | throwError "usim_hyp: no computation"
    unless f.getAppFn.isFVar do throwError "usim_hyp: no call of a join point"
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ok ← withReducible do
        let saved ← saveState
        try
          let goals ← mvarId.apply decl.toExpr
          if goals.isEmpty then
            pure true
          else
            saved.restore
            pure false
        catch _ =>
          saved.restore
          pure false
      if ok then
        replaceMainGoal []
        return
    throwError "usim_hyp: no hypothesis for the call"

/-- The call of a local definition, unfolded. -/
syntax "usim_unfold" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| usim_unfold) => withMainContext do
    let mvarId ← getMainGoal
    let target ← instantiateMVars (← mvarId.getType)
    let some f := usimSide target | throwError "usim_unfold: no computation"
    let .fvar x := f.getAppFn | throwError "usim_unfold: no call of a local definition"
    let some value := (← x.getDecl).value? | throwError "usim_unfold: no local definition"
    replaceMainGoal [← mvarId.replaceTargetDefEq (usimWith target (value.betaRev f.getAppRevArgs))]

/-- One rule of the walk. -/
syntax "usim_step" : tactic
macro_rules
  | `(tactic| usim_step) => `(tactic| first
    | usim_let
    | lsim_intro
    | usim_hyp
    | usim_unfold
    | with_reducible exact UL.pure _
    | with_reducible exact UL.getThe
    | with_reducible (refine UL.modifyThe _ fun _ => rfl)
    | with_reducible (refine UL.modifyGetThe _ fun _ => rfl)
    | with_reducible (refine UL.bind ?_ fun _ => ?_)
    | with_reducible (refine UL.ite (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine UL.dite (fun _ => ?_) (fun _ => ?_))
    | with_reducible exact UL.throw _
    | usim_named
    | split
    | lsim_split)

/-- The walk: the rules, as long as one applies. -/
macro "usim" : tactic => `(tactic| repeat' usim_step)

end BSmtLib.EndToEnd.Param

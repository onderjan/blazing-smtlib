import Lean.Elab.Tactic
import BSmtLib.Facts.Proofs.Reader.Param.Basic

/-!
# Walking the lexer's code on two consumers

The library's lexer runs the same code with both consumers, so a relation between the two runs
follows the code: at a `bind`, the two first actions are related and then the two rests, for
related values; at a branch, both runs take the same branch, as its condition reads only the
lexer's state, which is the same on both sides. This module has the rules for each form the
code takes, and the tactic `lsim` that applies them; the lemmas for the lexer's functions follow
in the modules after it, each proved by `lsim` from the lemmas for the functions it calls,
which `lsim_named` finds by their names.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.Walk

open BSmtLib.Lexer
open BSmtLib.Facts.Proofs.Reader.Param.Basic

section

variable {H₁ H₂ : Type} {m₁ m₂ : Type → Type} [Monad m₁] [Monad m₂] {R₁ R₂ E₁ E₂ : Type}
  {L : Link H₁ m₁ R₁ E₁ H₂ m₂ R₂ E₂} {S ε₁ ε₂ α β γ δ : Type} {Qe : ε₁ → ε₂ → Prop}

/-! ## Rules for actions that may fail -/

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.pure_eq (a : α) : XSim (S := S) L Qe
    (· = ·) (Pure.pure a) (Pure.pure a) :=
  XSim.pure rfl

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.bind_eq {Q : γ → δ → Prop}
    {x : ExceptT ε₁ (StateT S (StateT H₁ m₁)) α}
    {y : ExceptT ε₂ (StateT S (StateT H₂ m₂)) α} {f : α → ExceptT ε₁ (StateT S (StateT H₁ m₁)) γ}
    {g : α → ExceptT ε₂ (StateT S (StateT H₂ m₂)) δ} (hx : XSim L Qe (· = ·) x y)
    (hk : ∀ a, XSim L Qe Q (f a) (g a)) : XSim L Qe Q (x >>= f) (y >>= g) :=
  XSim.bind hx fun a b h => by cases h; exact hk a

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.ite {Q : α → β → Prop}
    {c : Prop} [Decidable c]
    {a b : ExceptT ε₁ (StateT S (StateT H₁ m₁)) α} {a' b' : ExceptT ε₂ (StateT S (StateT H₂ m₂)) β}
    (ha : c → XSim L Qe Q a a') (hb : ¬c → XSim L Qe Q b b') :
    XSim L Qe Q (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]; exact ha h
  · rw [ite_eq_right h, ite_eq_right h]; exact hb h

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.dite {Q : α → β → Prop}
    {c : Prop} [Decidable c]
    {a : c → ExceptT ε₁ (StateT S (StateT H₁ m₁)) α}
    {b : ¬c → ExceptT ε₁ (StateT S (StateT H₁ m₁)) α}
    {a' : c → ExceptT ε₂ (StateT S (StateT H₂ m₂)) β}
    {b' : ¬c → ExceptT ε₂ (StateT S (StateT H₂ m₂)) β}
    (ha : ∀ h, XSim L Qe Q (a h) (a' h)) (hb : ∀ h, XSim L Qe Q (b h) (b' h)) :
    XSim L Qe Q (if h : c then a h else b h) (if h : c then a' h else b' h) := by
  by_cases h : c
  · rw [dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true (eq_true h)]; exact ha h
  · rw [dite_eq_right_of_eq_false (eq_false h), dite_eq_right_of_eq_false (eq_false h)]; exact hb h

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.getThe : XSim L Qe (· = ·)
    (getThe S : ExceptT ε₁ (StateT S (StateT H₁ m₁)) S)
    (getThe S : ExceptT ε₂ (StateT S (StateT H₂ m₂)) S) :=
  XSim.lift SSim.get

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.modifyThe (f : S → S) :
    XSim L Qe (· = ·) (modifyThe S f : ExceptT ε₁ (StateT S (StateT H₁ m₁)) PUnit)
      (modifyThe S f : ExceptT ε₂ (StateT S (StateT H₂ m₂)) PUnit) :=
  XSim.lift (SSim.modifyGet _)

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.modifyGetThe (f : S → α × S) :
    XSim L Qe (· = ·) (modifyGetThe S f : ExceptT ε₁ (StateT S (StateT H₁ m₁)) α)
      (modifyGetThe S f : ExceptT ε₂ (StateT S (StateT H₂ m₂)) α) :=
  XSim.lift (SSim.modifyGet _)

/-- The runs of two related actions that may fail, from the same state. -/
theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.XSim.run_rel {Q : α → β → Prop}
    {f : ExceptT ε₁ (StateT S (StateT H₁ m₁)) α}
    {g : ExceptT ε₂ (StateT S (StateT H₂ m₂)) β} (h : XSim L Qe Q f g) (s : S) :
    L.rc.rel (fun a b => ERel Qe Q a.1 b.1 ∧ a.2 = b.2) (f.run.run s) (g.run.run s) :=
  h s

/-! ## Rules for the consumers' computations -/

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.Relator.ite_same {Q : α → β → Prop}
    {c : Prop} [Decidable c]
    {a b : StateT H₁ m₁ α} {a' b' : StateT H₂ m₂ β}
    (ha : c → L.rc.rel Q a a') (hb : ¬c → L.rc.rel Q b b') :
    L.rc.rel Q (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]; exact ha h
  · rw [ite_eq_right h, ite_eq_right h]; exact hb h

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.Relator.dite_same {Q : α → β → Prop}
    {c : Prop} [Decidable c]
    {a : c → StateT H₁ m₁ α} {b : ¬c → StateT H₁ m₁ α}
    {a' : c → StateT H₂ m₂ β} {b' : ¬c → StateT H₂ m₂ β}
    (ha : ∀ h, L.rc.rel Q (a h) (a' h)) (hb : ∀ h, L.rc.rel Q (b h) (b' h)) :
    L.rc.rel Q (if h : c then a h else b h) (if h : c then a' h else b' h) := by
  by_cases h : c
  · rw [dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true (eq_true h)]; exact ha h
  · rw [dite_eq_right_of_eq_false (eq_false h), dite_eq_right_of_eq_false (eq_false h)]
    exact hb h

/-! ## Rules for actions on the state that do not fail -/

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.pure_eq (a : α) : SSim (S := S) L
    (· = ·) (Pure.pure a : StateT S (StateT H₁ m₁) α)
    (Pure.pure a) :=
  SSim.pure rfl

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.bind_eq {Q : γ → δ → Prop}
    {x : StateT S (StateT H₁ m₁) α}
    {y : StateT S (StateT H₂ m₂) α} {f : α → StateT S (StateT H₁ m₁) γ}
    {g : α → StateT S (StateT H₂ m₂) δ} (hx : SSim L (· = ·) x y)
    (hk : ∀ a, SSim L Q (f a) (g a)) : SSim L Q (x >>= f) (y >>= g) :=
  SSim.bind hx fun a b h => by cases h; exact hk a

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.ite {Q : α → β → Prop}
    {c : Prop} [Decidable c]
    {a b : StateT S (StateT H₁ m₁) α} {a' b' : StateT S (StateT H₂ m₂) β}
    (ha : c → SSim L Q a a') (hb : ¬c → SSim L Q b b') :
    SSim L Q (if c then a else b) (if c then a' else b') := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]; exact ha h
  · rw [ite_eq_right h, ite_eq_right h]; exact hb h

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.dite {Q : α → β → Prop}
    {c : Prop} [Decidable c]
    {a : c → StateT S (StateT H₁ m₁) α} {b : ¬c → StateT S (StateT H₁ m₁) α}
    {a' : c → StateT S (StateT H₂ m₂) β} {b' : ¬c → StateT S (StateT H₂ m₂) β}
    (ha : ∀ h, SSim L Q (a h) (a' h)) (hb : ∀ h, SSim L Q (b h) (b' h)) :
    SSim L Q (if h : c then a h else b h) (if h : c then a' h else b' h) := by
  by_cases h : c
  · rw [dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true (eq_true h)]; exact ha h
  · rw [dite_eq_right_of_eq_false (eq_false h), dite_eq_right_of_eq_false (eq_false h)]; exact hb h

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.getThe : SSim L (· = ·)
    (getThe S : StateT S (StateT H₁ m₁) S)
    (getThe S : StateT S (StateT H₂ m₂) S) :=
  SSim.get

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.modifyThe (f : S → S) :
    SSim L (· = ·) (modifyThe S f : StateT S (StateT H₁ m₁) PUnit)
      (modifyThe S f : StateT S (StateT H₂ m₂) PUnit) :=
  SSim.modifyGet _

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.liftM {Q : α → β → Prop}
    {x : StateT H₁ m₁ α} {y : StateT H₂ m₂ β}
    (h : L.rc.rel Q x y) :
    SSim (S := S) L Q (liftM x : StateT S (StateT H₁ m₁) α) (liftM y : StateT S (StateT H₂ m₂) β) :=
  SSim.lift h

theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Basic.SSim.set_eq (s : S) : SSim L (· = ·)
    (MonadStateOf.set s : StateT S (StateT H₁ m₁) PUnit)
    (MonadStateOf.set s : StateT S (StateT H₂ m₂) PUnit) :=
  SSim.set s

end

/-! ## The tactic

The goals are relations `XSim`, `LSim` or `SSim` of two computations, the last two arguments.
The rules work on their forms: `bind`, `pure`, the state's primitives, branches, the lemmas of
the functions called (`lsim_named`), and the local definitions of the code. A local definition
with the same value on both sides (a value, or a fact the code states with `have`) becomes one
local definition of the context, so that the facts are there for the proofs that recursive calls
descend. A local definition with different values on the two sides is a join point of `do`
notation, a function to the rest of the block: the two become local definitions with the
hypothesis that they are related for every argument, proved once (`lsim_let`); their calls are
then related by that hypothesis (`lsim_hyp`), and the bodies by unfolding them (`lsim_unfold`).
-/

open Lean Meta Elab Tactic in
/-- The goal's two computations, if the goal relates two computations. -/
def lsimSides (target : Expr) : Option (Expr × Expr) :=
  let args := target.getAppArgs
  if 2 ≤ args.size then some (args[args.size - 2]!, args[args.size - 1]!) else none

open Lean Meta Elab Tactic in
/-- The goal with its two computations replaced. -/
def lsimWith (target f g : Expr) : Expr :=
  let args := target.getAppArgs
  mkAppN target.getAppFn ((args.set! (args.size - 2) f).set! (args.size - 1) g)

/-- The lemma for the lexer's function that the first computation of the goal applies: for a
function `f`, the lemma `f_sim` of a module of `Param`, applied; the hypotheses it needs that are
in the context are taken from there. -/
syntax "lsim_named" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| lsim_named) => withMainContext do
    let some (f, _) := lsimSides (← instantiateMVars (← getMainTarget))
      | throwError "lsim_named: the goal relates no two computations"
    let .const name _ := f.getAppFn
      | throwError "lsim_named: the first computation is no function's application"
    let .str _ last := name | throwError "lsim_named: unnamed function {name}"
    -- the lemmas are in the modules of `Param`, each in its module's namespace
    let env ← getEnv
    let param := `BSmtLib.Facts.Proofs.Reader.Param
    let modules := (env.header.moduleNames.push env.mainModule).filter (param.isPrefixOf ·)
    let some lemma := modules.findSome? (fun m =>
        let lemma := m.str (last ++ "_sim"); if env.contains lemma then some lemma else none)
      | throwError "lsim_named: no lemma {last}_sim in a module of {param}"
    let goals ← (← getMainGoal).apply (← mkConstWithFreshMVarLevels lemma)
    let mut open_ := #[]
    for goal in goals do
      unless ← goal.isAssigned do
        unless ← (do goal.assumption; pure true) <|> pure false do
          open_ := open_.push goal
    replaceMainGoal open_.toList

/-- Local definitions on both sides: one shared, or two join points with their hypothesis. -/
syntax "lsim_let" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| lsim_let) => withMainContext do
    let mvarId ← getMainGoal
    let target ← instantiateMVars (← mvarId.getType)
    let some (.letE name type value body _, .letE name' type' value' body' _) := lsimSides target
      | throwError "lsim_let: no local definitions on both sides"
    if ← withReducible (isDefEq type type' <&&> isDefEq value value') then
      let goal ← withLetDecl name type value fun x => do
        let goal ← mkFreshExprSyntheticOpaqueMVar
          (lsimWith target (body.instantiate1 x) (body'.instantiate1 x))
        mvarId.assign (← mkLetFVars #[x] goal)
        pure goal
      replaceMainGoal [goal.mvarId!]
    else
      let goals ← withLetDecl name type value fun j₁ => withLetDecl name' type' value' fun j₂ => do
        let hypType ← forallTelescope type fun rs _ => do
          if rs.isEmpty then throwError "lsim_let: the local definitions are not join points"
          let mut other := type'
          for r in rs do
            let .forallE _ domain body _ := other.consumeMData
              | throwError "lsim_let: the join points take different arguments"
            unless ← withReducible (isDefEq domain (← inferType r)) do
              throwError "lsim_let: the join points take different arguments"
            other := body.instantiate1 r
          mkForallFVars rs (lsimWith target (mkAppN j₁ rs) (mkAppN j₂ rs))
        let proof ← mkFreshExprSyntheticOpaqueMVar hypType
        withLocalDeclD `hjp hypType fun hyp => do
          let main ← mkFreshExprSyntheticOpaqueMVar
            (lsimWith target (body.instantiate1 j₁) (body'.instantiate1 j₂))
          let val := mkApp (← mkLambdaFVars #[hyp] main) proof
          mvarId.assign (← mkLetFVars #[j₁, j₂] val)
          pure [proof.mvarId!, main.mvarId!]
      replaceMainGoal goals

/-- The hypothesis of join points for the goal's calls of them. -/
syntax "lsim_hyp" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| lsim_hyp) => withMainContext do
    let mvarId ← getMainGoal
    let some (f, _) := lsimSides (← instantiateMVars (← mvarId.getType))
      | throwError "lsim_hyp: the goal relates no two computations"
    unless f.getAppFn.isFVar do throwError "lsim_hyp: no call of a join point"
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
    throwError "lsim_hyp: no hypothesis for the call"

/-- The calls of local definitions, unfolded. -/
syntax "lsim_unfold" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| lsim_unfold) => withMainContext do
    let mvarId ← getMainGoal
    let target ← instantiateMVars (← mvarId.getType)
    let some (f, g) := lsimSides target
      | throwError "lsim_unfold: the goal relates no two computations"
    let unfold (e : Expr) : MetaM (Option Expr) := do
      let .fvar x := e.getAppFn | return none
      let some value := (← x.getDecl).value? | return none
      return some (value.betaRev e.getAppRevArgs)
    let some f' ← unfold f | throwError "lsim_unfold: no call of a local definition"
    let some g' ← unfold g | throwError "lsim_unfold: no call of a local definition"
    replaceMainGoal [← mvarId.replaceTargetDefEq (lsimWith target f' g')]

/-- The argument of a goal for every argument of the join points. -/
syntax "lsim_intro" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| lsim_intro) => withMainContext do
    let mvarId ← getMainGoal
    let .forallE .. := (← instantiateMVars (← mvarId.getType)).consumeMData
      | throwError "lsim_intro: the goal is not for every argument"
    let (_, goal) ← mvarId.intro1
    replaceMainGoal [goal]

/-- A branch on a local definition's value: the value put in for the definitions of values in
the goal, which the branch then splits on. -/
syntax "lsim_split" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| lsim_split) => withMainContext do
    let mvarId ← getMainGoal
    let target ← instantiateMVars (← mvarId.getType)
    let target' ← Meta.transform target (pre := fun e => do
      if let .fvar x := e then
        let decl ← x.getDecl
        if let some value := decl.value? then
          unless (← whnfR decl.type).isForall do
            return .visit value
      return .continue)
    if target' == target then throwError "lsim_split: no definition of a value in the goal"
    replaceMainGoal [← mvarId.replaceTargetDefEq target']
    evalTactic (← `(tactic| split))

open Lean Meta in
/-- The expression with the values of the local definitions of the context put in. -/
def lsimZetaDelta (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    if let .fvar x := e then
      if let some value := (← x.getDecl).value? then
        return .visit value
    return .continue)

open Lean Meta in
/-- The expression with the definitions of the context put in and the projections of
constructors reduced. -/
def lsimNormalize (e : Expr) : MetaM Expr := do
  Meta.transform (← lsimZetaDelta (← instantiateMVars e)) (post := fun e => do
    let .const name _ := e.getAppFn | return .continue
    let some info := (← getEnv).getProjectionFnInfo? name | return .continue
    let args := e.getAppArgs
    if args.size ≤ info.numParams then return .continue
    let struct ← whnfR args[info.numParams]!
    let .const ctor _ := struct.getAppFn | return .continue
    unless ctor == info.ctorName do return .continue
    let some field := struct.getAppArgs[info.numParams + info.i]? | return .continue
    return .visit (mkAppN field (args.extract (info.numParams + 1) args.size)))

open Lean in
/-- The applications of `g` to `n` arguments in the expression, without loose bound variables. -/
def lsimApps (g : Name) (n : Nat) : Expr → Array Expr → Array Expr
  | e@(.app f a), acc =>
    let acc := lsimApps g n a (lsimApps g n f acc)
    if e.isAppOfArity g n && !e.hasLooseBVars then acc.push e else acc
  | .lam _ t b _, acc | .forallE _ t b _, acc => lsimApps g n b (lsimApps g n t acc)
  | .letE _ t v b _, acc => lsimApps g n b (lsimApps g n v (lsimApps g n t acc))
  | .mdata _ b, acc | .proj _ _ b, acc => lsimApps g n b acc
  | _, acc => acc

open Lean Meta in
/-- The facts that the lemma states for every application of its function in the expressions: a
lemma for every `x₁ … xₙ` about `g x₁ … xₙ` is put in for every application of `g` to `n`
arguments. -/
def lsimFacts (lemma : Name) (exprs : Array Expr) : MetaM (Array (Expr × Expr)) := do
  let info ← getConstInfo lemma
  forallTelescope info.type fun xs conclusion => do
    let some app := conclusion.find? fun e => e.getAppArgs == xs && e.getAppFn.isConst
      | throwError "lsim_omega: {lemma} states nothing of an application"
    let g := app.getAppFn.constName!
    let mut facts := #[]
    for e in exprs do
      for sub in lsimApps g xs.size (← instantiateMVars e) #[] do
        let proof ← mkAppOptM lemma (sub.getAppArgs.map some)
        facts := facts.push (← inferType proof, proof)
    return facts

/-- `omega` for the descent of a recursive call: the facts of the context, with the definitions
put in and the projections of constructors reduced, which the facts of the code state and the
branches on its structures leave, and the facts the given lemmas state of the applications of
their functions there. -/
syntax "lsim_omega" (" [" ident,* "]")? : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| lsim_omega $[[$lemmas,*]]?) => withMainContext do
    let mut goal ← getMainGoal
    goal ← goal.replaceTargetDefEq (← lsimNormalize (← goal.getType))
    let mut types := #[← goal.getType]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      unless ← isProp decl.type do continue
      let type ← lsimNormalize decl.type
      types := types.push type
      goal ← goal.assert decl.userName type decl.toExpr
      (_, goal) ← goal.intro1
    for lemma in (lemmas.map (·.getElems) |>.getD #[]) do
      let name ← realizeGlobalConstNoOverloadWithInfo lemma
      for (type, proof) in ← goal.withContext (lsimFacts name types) do
        goal ← goal.assert `fact type proof
        (_, goal) ← goal.intro1
    replaceMainGoal [goal]
    evalTactic (← `(tactic| omega))

/-- One rule of the walk. -/
syntax "lsim_step" : tactic
macro_rules
  | `(tactic| lsim_step) => `(tactic| first
    | lsim_let
    | lsim_intro
    | lsim_hyp
    | lsim_unfold
    | with_reducible exact XSim.pure_eq _
    | with_reducible exact XSim.getThe
    | with_reducible exact XSim.modifyThe _
    | with_reducible exact XSim.modifyGetThe _
    | with_reducible exact SSim.pure_eq _
    | with_reducible exact SSim.getThe
    | with_reducible exact SSim.modifyThe _
    | with_reducible exact SSim.set_eq _
    | with_reducible (refine SSim.liftM ?_)
    | with_reducible (refine XSim.bind_eq ?_ fun _ => ?_)
    | with_reducible (refine SSim.bind_eq ?_ fun _ => ?_)
    | with_reducible (refine XSim.ite (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine XSim.dite (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine SSim.ite (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine SSim.dite (fun _ => ?_) (fun _ => ?_))
    | (refine XSim.throw ⟨rfl, rfl, rfl⟩)
    | (refine XSim.throw ?_; assumption)
    | lsim_named
    | split
    | lsim_split)

/-- The walk: the rules, as long as one applies. -/
macro "lsim" : tactic => `(tactic| repeat' lsim_step)

end BSmtLib.Facts.Proofs.Reader.Param.Walk

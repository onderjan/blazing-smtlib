module

public meta import Lean.Elab.Tactic
public import BSmtLib.Facts.Proofs.Parser.Blank.Simp

@[expose] public section

/-!
# Walking a step on both sides

`bsplit` takes apart the discriminants of the match that the first side of a `BSim` goal is: a
local is split into its cases, any other value that is no constructor is first named. On the
second side the same match is on the blanked discriminants, which the blanking lemmas then turn
into the same constructors, so that both matches reduce. `blank_call` closes a handler call by
`BSim.call` and the method's field of `NoFails`; `blank_sub` a step that the walk calls by its
lemma; `blank_step` walks a step.
-/

namespace BSmtLib.Facts.Proofs.Parser.Blank.Tactic

open Basic Simp

open Lean Meta in
/-- Whether a local of the type is to be split: an inductive type of the parser, not a view, an
array, a number or a slice. -/
meta def splitType (ty : Expr) : MetaM Bool := do
  if (← isClass? ty).isSome then return false
  let ty ← whnf ty
  let some n := ty.getAppFn.constName? | return false
  if (`BSmtLib.Lexicon.Value).isPrefixOf n || n == ``Array || n == ``Nat || n == ``Std.Slice ||
      n == ``String || n == ``ByteArray || n == ``BSmtLib.Version then
    return false
  match (← getEnv).find? n with
  | some (.inductInfo _) => return true
  | _ => return false

open Lean Meta in
/-- The locals to split in the discriminant. -/
meta def splittable (e : Expr) : MetaM (Array FVarId) := do
  let mut acc : Array FVarId := #[]
  for f in (Lean.collectFVars {} e).fvarIds do
    if ← splitType (← f.getType) then acc := acc.push f
  return acc

/-- The first side of a `BSim` goal. -/
meta def firstSide (target : Lean.Expr) : Option Lean.Expr :=
  if target.isAppOfArity ``BSim 7 then some target.getAppArgs[5]! else none

/-- Splits the discriminants of the match that the first side of the `BSim` goal is: the locals
in them, or a discriminant without any, named. -/
syntax "bsplit" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| bsplit) => withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some x0 := firstSide target | throwError "bsplit: the goal is no BSim"
    let mut x := x0
    while x.isAppOfArity ``Bind.bind 6 do x := x.getAppArgs[4]!
    let env ← getEnv
    let isMatch (e : Expr) : Bool := match e.getAppFn.constName? with
      | some n => (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome && !e.hasLooseBVars
      | none => false
    if x.isAppOfArity ``Pure.pure 4 then
      if let some m := x.find? isMatch then x := m
    let some name := x.getAppFn.constName? | throwError "bsplit: the first side is no match"
    let some info := Lean.Meta.Match.Extension.getMatcherInfo? env name
      | throwError "bsplit: the first side is no match"
    let discrs := x.getAppArgs.extract (info.numParams + 1) (info.numParams + 1 + info.numDiscrs)
    for d in discrs do
      if d.isAppOfArity ``ite 5 then
        let cStx ← Term.exprToSyntax d.getAppArgs[1]!
        let h := mkIdent (← mkFreshUserName `hc)
        evalTactic (← `(tactic| by_cases $h:ident : $cStx <;> (try simp only [$h:ident, ite_true,
          ite_false, ↓reduceIte, Bool.false_eq_true, not_false_eq_true])))
        return
    let mut fvars : Array FVarId := #[]
    let mut others : Array Expr := #[]
    for d in discrs do
      if (← isConstructorApp d) then
        for f in ← splittable d do
          unless fvars.contains f do fvars := fvars.push f
        continue
      let fs ← splittable d
      if fs.isEmpty then others := others.push d
      else for f in fs do
        unless fvars.contains f do fvars := fvars.push f
    if fvars.isEmpty then
      for d in others do
        let dStx ← Term.exprToSyntax d
        let n ← mkFreshUserName `discr
        evalTactic (← `(tactic| generalize $dStx = $(mkIdent n):ident))
        let some decl := (← (← getMainGoal).getDecl).lctx.findFromUserName? n
          | throwError "bsplit: the named discriminant is lost"
        fvars := fvars.push decl.fvarId
    if fvars.isEmpty then throwError "bsplit: no discriminant to split"
    -- split one local; the walk splits the others as it meets the match again
    let goals ← (← getMainGoal).cases fvars[0]!
    replaceMainGoal (goals.map (·.mvarId)).toList

/-- A call of a handler whose calls never fail against the blank handler's call: by `BSim.call`
and the field of `NoFails` named as the method. -/
syntax "blank_call" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| blank_call) => withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some x := firstSide target | throwError "blank_call: the goal is no BSim"
    unless x.isAppOfArity ``BSmtLib.Parser.Internal.call 6 do
      throwError "blank_call: no handler call"
    let action := x.getAppArgs[5]!
    let some name := action.getAppFn.constName? | throwError "blank_call: no handler method"
    let .str _ last := name | throwError "blank_call: unnamed method {name}"
    let field := ``NoFails ++ Name.mkSimple last
    unless (← getEnv).contains field do throwError "blank_call: no field {field}"
    evalTactic (← `(tactic| exact BSim.call (b := ()) ($(mkIdent field) ..) rfl (fun _ => rfl)))

open Lean Meta in
/-- The lemma of the name in a module of the blanking, if there is one. -/
meta def findBlankLemma (name : String) : MetaM (Option Name) := do
  let env ← getEnv
  let modules := (env.header.moduleNames.push env.mainModule).filter
    (`BSmtLib.Facts.Proofs.Parser.Blank).isPrefixOf
  return modules.findSome? fun m =>
    let lemma := m ++ Name.mkSimple name
    if env.contains lemma then some lemma else none

/-- Relates the two sides of a `BSim` goal that call the same step by the step's lemma. For a
function `f`, the lemma is `f_blank`, or `T_step_blank` for `T.step` and `T.Internal.step`; for
a step given as an argument, it is the hypothesis about it. The walk proves the equations
between the arguments after. -/
syntax "blank_sub" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| blank_sub) => withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    let some x := firstSide target | throwError "blank_sub: the goal is no BSim"
    let f := x.getAppFn
    if f.isFVar then
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let ty ← instantiateMVars decl.type
        let concl ← forallTelescopeReducing ty fun _ b => pure b
        if let some x' := firstSide concl then
          if x'.getAppFn == f then
            evalTactic (← `(tactic| apply $(mkIdent decl.userName)))
            return
      throwError "blank_sub: no hypothesis about the step"
    let some name := f.constName? | throwError "blank_sub: no step"
    let .str parent last := name | throwError "blank_sub: unnamed step {name}"
    -- `T.Internal.step` is named by `T`, as `T.step`
    let parent := match parent with
      | .str p "Internal" => p
      | p => p
    let base := if last == "step" then
        match parent with
        | .str _ p => p ++ "_step"
        | _ => last
      else last
    let some lemma ← findBlankLemma (base ++ "_blank")
      | throwError "blank_sub: no lemma {base}_blank"
    evalTactic (← `(tactic| apply $(mkIdent lemma)))

/-- Walks a step on both sides, by the closure lemmas of `BSim`; the lemmas given close the
steps the walk calls. -/
macro "blank_step" "[" ts:Lean.Parser.Tactic.SolveByElim.arg,* "]" : tactic => `(tactic|
  repeat' (first
    | (intro h; try subst h)
    | ((with_reducible apply BSim.pure); blank_simp; done)
    | ((with_reducible apply BSim.pure); rfl)
    | (with_reducible exact BSim.syntaxError _)
    | ((with_reducible apply BSim.throw); blank_simp; done)
    | ((with_reducible apply BSim.throw); rfl)
    | ((try blank_simp); bsplit <;> (try blank_simp) <;> (try dsimp only))
    | ((with_reducible refine BSim.bind ?_ (fun _ => ?_)); try dsimp only)
    | ((with_reducible refine BSim.ite ?_ (fun _ => ?_) (fun _ => ?_)); blank_simp)
    | ((with_reducible refine BSim.dite ?_ (fun _ _ => ?_) (fun _ _ => ?_)); blank_simp)
    | blank_call
    | (solve_by_elim only [$ts,*])
    | blank_sub
    | assumption
    | (blank_simp; done)
    ))

end BSmtLib.Facts.Proofs.Parser.Blank.Tactic

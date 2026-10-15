module

public meta import Lean.Elab.Tactic
public import BSmtLib.Facts.Proofs.Parser.Canon.Basic

@[expose] public section

/-!
# Taking a match of a step apart on both sides

`csplit` takes apart the discriminants of the match that the first side of a `CSim` goal is: a
local is split into its cases, any other value that is no constructor is first named. On the
second side the same match is on the canonicalised discriminants, which the canonicalisation
lemmas then turn into the same constructors, so that both matches reduce.
-/

namespace BSmtLib.Facts.Proofs.Parser.Canon.Tactic

open Basic

open Lean Meta in
/-- Whether a local of the type is to be split: an inductive type of the parser, not a view, an
array, a number or a slice. -/
meta def splitType (ty : Expr) : MetaM Bool := do
  let ty ← whnf ty
  let some n := ty.getAppFn.constName? | return false
  if (`BSmtLib.Plain).isPrefixOf n || n == ``Array || n == ``Nat || n == ``Std.Slice ||
      n == ``String || n == ``ByteArray || n == ``BSmtLib.Token.Version then
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

/-- Splits the discriminants of the match that the first side of the `CSim` goal is: the locals
in them, or a discriminant without any, named. -/
syntax "csplit" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| csplit) => withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    unless target.isAppOfArity ``CSim 4 do throwError "csplit: the goal is no CSim"
    let mut x := target.getAppArgs[2]!
    while x.isAppOfArity ``Bind.bind 6 do x := x.getAppArgs[4]!
    let env ← getEnv
    let isMatch (e : Expr) : Bool := match e.getAppFn.constName? with
      | some n => (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome && !e.hasLooseBVars
      | none => false
    if x.isAppOfArity ``Pure.pure 4 then
      if let some m := x.find? isMatch then x := m
    let some name := x.getAppFn.constName? | throwError "csplit: the first side is no match"
    let some info := Lean.Meta.Match.Extension.getMatcherInfo? env name
      | throwError "csplit: the first side is no match"
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
          | throwError "csplit: the named discriminant is lost"
        fvars := fvars.push decl.fvarId
    if fvars.isEmpty then throwError "csplit: no discriminant to split"
    -- split one local; the walk splits the others as it meets the match again
    let goals ← (← getMainGoal).cases fvars[0]!
    replaceMainGoal (goals.map (·.mvarId)).toList

end BSmtLib.Facts.Proofs.Parser.Canon.Tactic

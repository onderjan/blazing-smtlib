module

public meta import Lean.Elab.Tactic
public import BSmtLib.Facts.Proofs.Reader.Param.Walk

@[expose] public section

/-!
# Walking the Rust port's code on two consumers

The Rust port (`Lexer.Internal.WRustPort`) runs its code in monads of the same form as the
library's lexer, so the rules of `Param.Walk` apply to it. Only the lemmas for the functions it
calls differ: `lsimW_named` finds them in the modules of `ParamW`, where the lemma for a function
`f` is `f_sim`, and `lsimW` is the walk with it.
-/

namespace BSmtLib.Facts.Proofs.Reader.ParamW.Walk

open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.Walk

/-- The lemma for the Rust port's function that the first computation of the goal applies: for
a function `f`, the lemma `f_sim` of a module of `ParamW`, applied; the hypotheses it needs that
are in the context are taken from there. -/
syntax "lsimW_named" : tactic

open Lean Meta Elab Tactic in
elab_rules : tactic
  | `(tactic| lsimW_named) => withMainContext do
    let some (f, _) := lsimSides (← instantiateMVars (← getMainTarget))
      | throwError "lsimW_named: the goal relates no two computations"
    let .const name _ := f.getAppFn
      | throwError "lsimW_named: the first computation is no function's application"
    let .str _ last := name | throwError "lsimW_named: unnamed function {name}"
    let env ← getEnv
    let param := `BSmtLib.Facts.Proofs.Reader.ParamW
    let modules := (env.header.moduleNames.push env.mainModule).filter (param.isPrefixOf ·)
    let some lemma := modules.findSome? (fun m =>
        let lemma := m.str (last ++ "_sim"); if env.contains lemma then some lemma else none)
      | throwError "lsimW_named: no lemma {last}_sim in a module of {param}"
    let goals ← (← getMainGoal).apply (← mkConstWithFreshMVarLevels lemma)
    let mut open_ := #[]
    for goal in goals do
      unless ← goal.isAssigned do
        unless ← (do goal.assumption; pure true) <|> pure false do
          open_ := open_.push goal
    replaceMainGoal open_.toList

/-- One rule of the walk on the Rust port's code. -/
syntax "lsimW_step" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| lsimW_step) => `(tactic| first
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
    | with_reducible (refine XSim.bind ?_ fun _ _ h => XSim.throw h)
    | with_reducible (refine XSim.bind_eq ?_ fun _ => ?_)
    | with_reducible (refine SSim.bind_eq ?_ fun _ => ?_)
    | (with_reducible refine XSim.bind (XSim.throw ?_) fun _ _ h => (h : False).elim; assumption)
    | with_reducible (refine BSmtLib.Facts.Proofs.Reader.ParamW.HandOver.bind_error ?_)
    | with_reducible (refine BSmtLib.Facts.Proofs.Reader.ParamW.HandOver.bind_errorAt ?_)
    | with_reducible (refine BSmtLib.Facts.Proofs.Reader.ParamW.HandOver.bind_errorWith ?_)
    | with_reducible (refine XSim.ite (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine XSim.dite (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine SSim.ite (fun _ => ?_) (fun _ => ?_))
    | with_reducible (refine SSim.dite (fun _ => ?_) (fun _ => ?_))
    | (refine XSim.throw ⟨rfl, rfl, rfl⟩)
    | (refine XSim.throw ?_; assumption)
    | lsimW_named
    | split
    | lsim_split)

/-- The walk on the Rust port's code: the rules, as long as one applies. -/
macro "lsimW" : tactic => `(tactic| repeat' lsimW_step)

end BSmtLib.Facts.Proofs.Reader.ParamW.Walk

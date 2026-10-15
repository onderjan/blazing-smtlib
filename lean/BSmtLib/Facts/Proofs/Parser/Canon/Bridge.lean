module

public meta import Lean.Elab.Tactic
public import BSmtLib.Facts.Proofs.Parser.Canon.Simp
import all BSmtLib.Parser
import all BSmtLib.Facts.Parser.Adapters.Handler
import all BSmtLib.Facts.Parser.Adapters.Bridge
import all BSmtLib.Multiple
import all BSmtLib.Multiple.MatchCases
import all BSmtLib.Multiple.FunctionSignaturesView

@[expose] public section

/-!
# The recording handler is told contents only

The recording handler turns every view it is handed into the spec's characters, so a call with
canonicalised arguments is the same call (`canon_call`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Canon.Bridge

open Basic States Simp Tactic


open BSmtLib.Parser BSmtLib.Nodes
open BSmtLib.Facts.Parser.Adapters.Bridge.Bridge

@[canon_simps] theorem chars_canonSlice (s : ByteSlice) : chars (canonSlice s) = chars s := by
  simp only [chars, toByteArray_canonSlice]

@[canon_simps] theorem symbol_canonSymbol (s : Plain.SymbolView) :
    symbol (canonSymbol s) = symbol s := by
  simp only [symbol, canon_simps]

@[canon_simps] theorem index_canonIndex (i : Index) : index (canonIndex i) = index i := by
  cases i <;> simp only [index, canon_simps, Canon.canon]

@[canon_simps] theorem identifier_canonIdentifier (i : Identifier) :
    identifier (canonIdentifier i) = identifier i := by
  cases i
  simp only [identifier, canon_simps, Canon.canon, Array.toList_map, List.map_map,
    Function.comp_def, index_canonIndex]

@[canon_simps] theorem constant_canonConstant (c : SpecConstant) :
    constant (canonConstant c) = constant c := by
  cases c <;> simp only [constant, canon_simps, Canon.canon]

@[canon_simps] theorem symbolOrWildcard_canonSymbolOrWildcard (s : SymbolOrWildcard) :
    symbolOrWildcard (canonSymbolOrWildcard s) = symbolOrWildcard s := by
  cases s <;> simp only [symbolOrWildcard, canon_simps, Canon.canon]

@[canon_simps] theorem pattern_canonPattern (p : Pattern) :
    pattern (canonPattern p) = pattern p := by
  cases p <;> simp only [pattern, canon_simps, Canon.canon, Array.toList_map, List.map_map,
    Function.comp_def, symbolOrWildcard_canonSymbolOrWildcard]

open BSmtLib.Facts.Parser.Adapters.Handler in
@[canon_simps] theorem sExprNodeOf_canonSExprNode {values : BSmtLibSpec.Parser.Traversal.Values}
    [Canon values.sExpr] [CanonId values.sExpr] (n : SExprNode values.sExpr) :
    sExprNodeOf (canonSExprNode n) = sExprNodeOf n := by
  cases n <;> simp only [sExprNodeOf, canonSExprNode, canon_simps, Canon.canon, keyword]

open BSmtLib.Facts.Parser.Adapters.Handler in
@[canon_simps] theorem termNodeOf_canonTermNode {values : BSmtLibSpec.Parser.Traversal.Values}
    [Canon values.sort] [CanonId values.sort] [Canon values.term] [CanonId values.term]
    (n : TermNode values.sort values.term) :
    termNodeOf (canonTermNode n) = termNodeOf n := by
  cases n <;> simp only [termNodeOf, canonTermNode, canon_simps, Canon.canon]

open BSmtLib.Facts.Parser.Adapters.Handler in
@[canon_simps] theorem attributeValueOf_canonAttributeValueNode
    {values : BSmtLibSpec.Parser.Traversal.Values} [Canon values.sExpr] [CanonId values.sExpr]
    (n : AttributeValueNode values.sExpr) :
    attributeValueOf (canonAttributeValueNode n) = attributeValueOf n := by
  cases n <;> simp only [attributeValueOf, canonAttributeValueNode, canon_simps, Canon.canon]

instance : Canon BSmtLibSpec.Parser.Properties.Recorded.sExpr := inferInstanceAs (Canon Nat)
instance : Canon BSmtLibSpec.Parser.Properties.Recorded.sort := inferInstanceAs (Canon Nat)
instance : Canon BSmtLibSpec.Parser.Properties.Recorded.term := inferInstanceAs (Canon Nat)
instance : CanonId BSmtLibSpec.Parser.Properties.Recorded.sExpr := inferInstanceAs (CanonId Nat)
instance : CanonId BSmtLibSpec.Parser.Properties.Recorded.sort := inferInstanceAs (CanonId Nat)
instance : CanonId BSmtLibSpec.Parser.Properties.Recorded.term := inferInstanceAs (CanonId Nat)

@[canon_simps] theorem pairs_canon {α : Type} (items : Array (Plain.SymbolView × α)) :
    pairs (items.map fun p => (canonSymbol p.1, p.2)) = pairs items := by
  simp only [pairs, Array.toList_map, List.map_map]
  apply List.map_congr_left
  intro p _
  obtain ⟨s, a⟩ := p
  simp only [Function.comp_apply, symbol_canonSymbol]

@[canon_simps] theorem keyword_canon (k : BSmtLib.Plain.KeywordView) :
    keyword (BSmtLib.Plain.KeywordView.Internal.newUnchecked (canonSlice k.asSlice)) =
      keyword k := by
  simp only [keyword, canon_simps]

theorem symbols_canon (items : Array Plain.SymbolView) :
    (items.map canonSymbol).toList.map symbol = items.toList.map symbol := by
  simp only [Array.toList_map, List.map_map, Function.comp_def, symbol_canonSymbol]

/-! ## The recording handler's calls

Each call of the recording handler with its views canonicalised is the call itself. The walk
proves a call's two sides alike by one of these and the canonicalisation of the arguments
(`canon_call`). -/

section

open BSmtLib.Facts.Parser.Adapters.Handler BSmtLibSpec.Parser.Properties
open BSmtLib.Plain (KeywordView NumeralView StringContentView)
open Traits.Handler Traits.CommandHandler

variable {s : Plain.SymbolView} {i : Identifier} {k : KeywordView} {n : NumeralView}

theorem handleSort_canon {args : Multiple (Traits.Handler.«Sort» (List Event))} :
    handleSort (H := List Event) (canonIdentifier i) args = handleSort i args := by
  show recordingCall (.handleSort (identifier (canonIdentifier i)) _) =
    recordingCall (.handleSort (identifier i) _)
  rw [identifier_canonIdentifier]

theorem handleTerm_canon {t : TermNode (Traits.Handler.«Sort» (List Event))
    (Traits.Handler.Term (List Event))} :
    handleTerm (H := List Event) (canonTermNode t) = handleTerm t :=
  congrArg (fun x => recordingCall (.handleTerm x))
    (termNodeOf_canonTermNode (values := Recorded) t)

theorem handleSExpr_canon {x : SExprNode (Traits.Handler.SExpr (List Event))} :
    handleSExpr (H := List Event) (canonSExprNode x) = handleSExpr x :=
  congrArg (fun x => recordingCall (.handleSExpr x))
    (sExprNodeOf_canonSExprNode (values := Recorded) x)

theorem handleAttribute_canon
    {v : Option (AttributeValueNode (Traits.Handler.SExpr (List Event)))} :
    handleAttribute (H := List Event) (KeywordView.Internal.newUnchecked (canonSlice k.asSlice))
      (v.map canonAttributeValueNode) = handleAttribute k v := by
  show recordingCall (.handleAttribute (keyword _) _) =
    recordingCall (.handleAttribute (keyword _) _)
  rw [keyword_canon]
  cases v with
  | none => rfl
  | some val =>
    exact congrArg (fun x => recordingCall (.handleAttribute (keyword k) (some x)))
      (attributeValueOf_canonAttributeValueNode (values := Recorded) val)

theorem startLet_canon {bs : Multiple.BindingsView (Traits.Handler.Term (List Event))} :
    startLet (H := List Event) (canon bs) = startLet bs :=
  congrArg (fun x => recordingCall (.startLet x)) (pairs_canon bs.toArray)

theorem startQuantifier_canon {q : Quantifier}
    {vs : Multiple.SortedVarsView (Traits.Handler.«Sort» (List Event))} :
    startQuantifier (H := List Event) q (canon vs) = startQuantifier q vs :=
  congrArg (fun x => recordingCall (.startQuantifier _ x)) (pairs_canon vs.toArray)

theorem startLambda_canon {vs : Multiple.SortedVarsView (Traits.Handler.«Sort» (List Event))} :
    startLambda (H := List Event) (canon vs) = startLambda vs :=
  congrArg (fun x => recordingCall (.startLambda x)) (pairs_canon vs.toArray)

theorem startMatchCase_canon {t : Traits.Handler.Term (List Event)} {p : Pattern} :
    startMatchCase (H := List Event) t (canonPattern p) = startMatchCase t p :=
  congrArg (fun x => recordingCall (.startMatchCase t x)) (pattern_canonPattern p)

theorem endMatch_canon {t : Traits.Handler.Term (List Event)}
    {cs : Multiple.MatchCases (Traits.Handler.Term (List Event))} :
    endMatch (H := List Event) t (canon cs) = endMatch t cs := by
  show recordingCall (.endMatch t (((cs.toArray.map fun p => (canonPattern p.1, p.2))).toList.map
      fun (p, b) => (pattern p, b))) =
    recordingCall (.endMatch t (cs.toArray.toList.map fun (p, b) => (pattern p, b)))
  congr 2
  simp only [Array.toList_map, List.map_map, Function.comp_def, pattern_canonPattern]

theorem commandDeclareConst_canon {t : Traits.Handler.«Sort» (List Event)} :
    commandDeclareConst (H := List Event) (canonSymbol s) t = commandDeclareConst s t :=
  congrArg (fun x => recordingCall (.commandDeclareConst x t)) (symbol_canonSymbol s)

theorem startDeclareDatatype_canon {ps : Multiple.SymbolsView} :
    startDeclareDatatype (H := List Event) (canonSymbol s) (canon ps) =
      startDeclareDatatype s ps := by
  show recordingCall (.startDeclareDatatype (symbol (canonSymbol s))
      ((ps.toArray.map canonSymbol).toList.map symbol)) =
    recordingCall (.startDeclareDatatype (symbol s) (ps.toArray.toList.map symbol))
  rw [symbol_canonSymbol, symbols_canon]

theorem constructors_canon
    (cs : Multiple.ConstructorsView (Traits.Handler.«Sort» (List Event))) :
    (canon cs).toArray.toList.map
        (BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.constructor (H := List Event)) =
      cs.toArray.toList.map
        (BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.constructor (H := List Event)) := by
  show (cs.toArray.map canon).toList.map _ = _
  simp only [Array.toList_map, List.map_map]
  apply List.map_congr_left
  intro c _
  obtain ⟨sym, sel⟩ := c
  show BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.constructor (canonSymbol sym, canon sel) =
    BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.constructor (sym, sel)
  simp only [BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.constructor, symbol_canonSymbol]
  exact congrArg _ (pairs_canon sel.toArray)

theorem endDeclareDatatype_canon
    {cs : Multiple.ConstructorsView (Traits.Handler.«Sort» (List Event))} :
    endDeclareDatatype (H := List Event) (canon cs) = endDeclareDatatype cs :=
  congrArg (fun x => recordingCall (.endDeclareDatatype x)) (constructors_canon cs)

theorem endDatatypeDeclaration_canon
    {cs : Multiple.ConstructorsView (Traits.Handler.«Sort» (List Event))} :
    endDatatypeDeclaration (H := List Event) (canon cs) = endDatatypeDeclaration cs :=
  congrArg (fun x => recordingCall (.endDatatypeDeclaration x)) (constructors_canon cs)

theorem startDeclareDatatypes_canon {ss : Multiple.SortAritiesView} :
    startDeclareDatatypes (H := List Event) (canon ss) = startDeclareDatatypes ss := by
  show recordingCall (.startDeclareDatatypes ((ss.toArray.map fun p =>
      (canonSymbol p.1, NumeralView.Internal.newUnchecked (canonSlice p.2.asSlice))).toList.map
        fun (s, n) => (symbol s, chars n.asSlice))) =
    recordingCall (.startDeclareDatatypes
      (ss.toArray.toList.map fun (s, n) => (symbol s, chars n.asSlice)))
  congr 2
  simp only [Array.toList_map, List.map_map, Function.comp_def, symbol_canonSymbol, canon_simps]

theorem startDatatypeDeclaration_canon {ps : Multiple.SymbolsView} :
    startDatatypeDeclaration (H := List Event) (canon ps) = startDatatypeDeclaration ps :=
  congrArg (fun x => recordingCall (.startDatatypeDeclaration x)) (symbols_canon ps.toArray)

theorem commandDeclareFun_canon {ps : Multiple (Traits.Handler.«Sort» (List Event))}
    {r : Traits.Handler.«Sort» (List Event)} :
    commandDeclareFun (H := List Event) (canonSymbol s) ps r = commandDeclareFun s ps r :=
  congrArg (fun x => recordingCall (.commandDeclareFun x _ r)) (symbol_canonSymbol s)

theorem commandDeclareSort_canon :
    commandDeclareSort (H := List Event) (canonSymbol s)
        (NumeralView.Internal.newUnchecked (canonSlice n.asSlice)) = commandDeclareSort s n := by
  show recordingCall (.commandDeclareSort _ _) = recordingCall (.commandDeclareSort _ _)
  rw [symbol_canonSymbol]
  simp only [canon_simps]

theorem commandDeclareSortParameter_canon :
    commandDeclareSortParameter (H := List Event) (canonSymbol s) =
      commandDeclareSortParameter s :=
  congrArg (fun x => recordingCall (.commandDeclareSortParameter x)) (symbol_canonSymbol s)

theorem commandDefineConst_canon {t : Traits.Handler.«Sort» (List Event)}
    {b : Traits.Handler.Term (List Event)} :
    commandDefineConst (H := List Event) (canonSymbol s) t b = commandDefineConst s t b :=
  congrArg (fun x => recordingCall (.commandDefineConst x t b)) (symbol_canonSymbol s)

theorem signature_canon (sig : Signature (Traits.Handler.«Sort» (List Event))) :
    BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.signature (H := List Event) (canonSignature sig) =
      BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.signature sig := by
  obtain ⟨sym, ps, r⟩ := sig
  show BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.signature ⟨canonSymbol sym, _, _⟩ = _
  simp only [BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.signature, symbol_canonSymbol]
  simp only [Canon.canon, canon_simps]

theorem startDefineFun_canon {sig : Signature (Traits.Handler.«Sort» (List Event))} :
    startDefineFun (H := List Event) (canonSignature sig) = startDefineFun sig :=
  congrArg (fun x => recordingCall (.startDefineFun x)) (signature_canon sig)

theorem startDefineFunRec_canon {sig : Signature (Traits.Handler.«Sort» (List Event))} :
    startDefineFunRec (H := List Event) (canonSignature sig) = startDefineFunRec sig :=
  congrArg (fun x => recordingCall (.startDefineFunRec x)) (signature_canon sig)

theorem startRecursiveBody_canon {sig : Signature (Traits.Handler.«Sort» (List Event))} :
    startRecursiveBody (H := List Event) (canonSignature sig) = startRecursiveBody sig :=
  congrArg (fun x => recordingCall (.startRecursiveBody x)) (signature_canon sig)

theorem startDefineFunsRec_canon
    {sigs : Multiple.FunctionSignaturesView (Traits.Handler.«Sort» (List Event))} :
    startDefineFunsRec (H := List Event) (canon sigs) = startDefineFunsRec sigs := by
  show recordingCall (.startDefineFunsRec ((sigs.toArray.map canonSignature).toList.map _)) =
    recordingCall (.startDefineFunsRec _)
  congr 2
  rw [Array.toList_map]
  generalize sigs.toArray.toList = l
  induction l with
  | nil => rfl
  | cons sig rest ih =>
    show BSmtLib.Facts.Parser.Adapters.Bridge.Bridge.signature (canonSignature sig) :: _ = _
    rw [signature_canon]
    exact congrArg (List.cons _) ih

theorem startDefineSort_canon {ps : Multiple.SymbolsView} :
    startDefineSort (H := List Event) (canonSymbol s) (canon ps) =
      startDefineSort s ps := by
  show recordingCall (.startDefineSort (symbol (canonSymbol s))
      ((ps.toArray.map canonSymbol).toList.map symbol)) =
    recordingCall (.startDefineSort (symbol s) (ps.toArray.toList.map symbol))
  rw [symbol_canonSymbol, symbols_canon]

theorem commandEcho_canon {c : StringContentView} :
    commandEcho (H := List Event) (StringContentView.Internal.newUnchecked (canonSlice c.asSlice)) =
      commandEcho c := by
  show recordingCall (.commandEcho _) = recordingCall (.commandEcho _)
  simp only [canon_simps]

theorem commandGetInfo_canon :
    commandGetInfo (H := List Event) (KeywordView.Internal.newUnchecked (canonSlice k.asSlice)) =
      commandGetInfo k := by
  show recordingCall (.commandGetInfo _) = recordingCall (.commandGetInfo _)
  rw [keyword_canon]

theorem commandGetOption_canon :
    commandGetOption (H := List Event) (KeywordView.Internal.newUnchecked (canonSlice k.asSlice)) =
      commandGetOption k := by
  show recordingCall (.commandGetOption _) = recordingCall (.commandGetOption _)
  rw [keyword_canon]

theorem commandPop_canon :
    commandPop (H := List Event) (NumeralView.Internal.newUnchecked (canonSlice n.asSlice)) =
      commandPop n := by
  show recordingCall (.commandPop _) = recordingCall (.commandPop _)
  simp only [canon_simps]

theorem commandPush_canon :
    commandPush (H := List Event) (NumeralView.Internal.newUnchecked (canonSlice n.asSlice)) =
      commandPush n := by
  show recordingCall (.commandPush _) = recordingCall (.commandPush _)
  simp only [canon_simps]

theorem commandSetLogic_canon :
    commandSetLogic (H := List Event) (canonSymbol s) = commandSetLogic s :=
  congrArg (fun x => recordingCall (.commandSetLogic x)) (symbol_canonSymbol s)

end

open _root_.Lean _root_.Lean.Meta in
/-- The lemma of the name in a module of the canonicalisation, if there is one. -/
meta def findCanonLemma (name : String) : MetaM (Option Name) := do
  let env ← getEnv
  let canonModules := (env.header.moduleNames.push env.mainModule).filter
    (`BSmtLib.Facts.Proofs.Parser.Canon).isPrefixOf
  return canonModules.findSome? fun m =>
    let lemma := m ++ Name.mkSimple name
    if env.contains lemma then some lemma else none

/-- A call of the recording handler with its views canonicalised is the call itself: by the
lemma of its method, and the canonicalisation of its arguments. -/
syntax "canon_call" : tactic

open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic in
elab_rules : tactic
  | `(tactic| canon_call) => withMainContext do
    evalTactic (← `(tactic| refine congrArg Parser.Internal.call ?_))
    withMainContext do
      let target ← instantiateMVars (← getMainTarget)
      let some (_, lhs, _) := target.eq? | throwError "canon_call: the goal is no equation"
      let some name := lhs.getAppFn.constName? | throwError "canon_call: no handler call"
      let .str _ last := name | throwError "canon_call: unnamed method {name}"
      let some lemma ← findCanonLemma (last ++ "_canon")
        | throwError "canon_call: no lemma {last}_canon"
      evalTactic (← `(tactic| refine Eq.trans ?_ $(mkIdent lemma)))
      evalTactic (← `(tactic| canon_simp))

/-- Relates the two sides of a `CSim` goal that call the same step by the step's lemma: for a
function `f`, `f_canon`, or `T_step_canon` for `T.step`, and for a step given as an argument,
the hypothesis about it; the walk proves the equations between the arguments after. -/
syntax "canon_sub" : tactic

open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab _root_.Lean.Elab.Tactic in
elab_rules : tactic
  | `(tactic| canon_sub) => withMainContext do
    let target ← instantiateMVars (← getMainTarget)
    unless target.isAppOfArity ``CSim 4 do throwError "canon_sub: the goal is no CSim"
    let x := target.getAppArgs[2]!
    let f := x.getAppFn
    if f.isFVar then
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let ty ← instantiateMVars decl.type
        let concl ← forallTelescopeReducing ty fun _ b => pure b
        if concl.isAppOfArity ``CSim 4 && concl.getAppArgs[2]!.getAppFn == f then
          evalTactic (← `(tactic| apply $(mkIdent decl.userName)))
          return
      throwError "canon_sub: no hypothesis about the step"
    let some name := f.constName? | throwError "canon_sub: no step"
    let .str parent last := name | throwError "canon_sub: unnamed step {name}"
    let base := if last == "step" then
        match parent with
        | .str _ p => p ++ "_step"
        | _ => last
      else last
    let some lemma ← findCanonLemma (base ++ "_canon")
      | throwError "canon_sub: no lemma {base}_canon"
    evalTactic (← `(tactic| apply $(mkIdent lemma)))

/-- Walks a step on both sides, by the closure lemmas of `CSim`; the lemmas given close the
steps the walk calls. -/
macro "canon_step" "[" ts:Lean.Parser.Tactic.SolveByElim.arg,* "]" : tactic => `(tactic|
  repeat' (first
    | (intro h; try subst h)
    | ((with_reducible apply CSim.pure); canon_simp; done)
    | (with_reducible exact CSim.throw _)
    | ((try canon_simp); csplit <;> (try canon_simp) <;> (try dsimp only))
    | ((with_reducible refine CSim.bind ?_ (fun _ => ?_)); try dsimp only)
    | ((with_reducible refine CSim.ite ?_ (fun _ => ?_) (fun _ => ?_)); canon_simp)
    | (refine CSim.same ?_; canon_simp; done)
    | (refine CSim.same ?_; canon_call; done)
    | (solve_by_elim only [$ts,*])
    | canon_sub
    | assumption
    | (canon_simp; done)
    ))

end BSmtLib.Facts.Proofs.Parser.Canon.Bridge

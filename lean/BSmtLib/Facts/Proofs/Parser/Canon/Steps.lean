module

public import BSmtLib.Facts.Proofs.Parser.Canon.Bridge
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Attribute
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Category.Ident
import all BSmtLib.Parser.Category.Pattern
import all BSmtLib.Parser.Category.QualifiedIdent
import all BSmtLib.Parser.Category.SExpr
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Category.SortedVar
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Parser.Category.Token

@[expose] public section

/-!
# The steps of the categories, canonicalised

Each step of the parsers of the categories, run on a canonicalised state and token, relates to
the step run on the state and the token as they are (`CSim`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Canon.Steps

open Basic States Simp Bridge


open BSmtLib.Parser BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Parser.Category.Attribute BSmtLib.Parser.Category.Combinator
open BSmtLib.Parser.Category.Ident BSmtLib.Parser.Category.Pattern
open BSmtLib.Parser.Category.QualifiedIdent BSmtLib.Parser.Category.SExpr
open BSmtLib.Parser.Category.«Sort» BSmtLib.Parser.Category.SortedVar
open BSmtLib.Parser.Category.Term BSmtLib.Parser.Category.Token
open BSmtLibSpec.Parser.Properties (Event)
open BSmtLib.Facts.Proofs.Parser.Quiet (RPM)
open BSmtLib.Parser.Category.Attribute.Internal
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Parser.Category.Ident.Internal
open BSmtLib.Parser.Category.Pattern.Internal
open BSmtLib.Parser.Category.QualifiedIdent.Internal
open BSmtLib.Parser.Category.SExpr.Internal
open BSmtLib.Parser.Category.«Sort».Internal
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.Term.Internal
open BSmtLib.Parser.Category.Token.Internal

variable {token' : Internal.Input}

theorem expectOpen_canon {token : Internal.Input} (ht : token' = canon token) :
    CSim (expectOpen (H := List Event) token) (expectOpen token') := by
  subst ht; unfold expectOpen; canon_step []

theorem expectClose_canon {token : Internal.Input} (ht : token' = canon token) :
    CSim (expectClose (H := List Event) token) (expectClose token') := by
  subst ht; unfold expectClose; canon_step []

theorem expectSymbol_canon {token : Internal.Input} (ht : token' = canon token) :
    CSim (expectSymbol (H := List Event) token) (expectSymbol token') := by
  subst ht; unfold expectSymbol; canon_step []

theorem expectNumeral_canon {token : Internal.Input} (ht : token' = canon token) :
    CSim (expectNumeral (H := List Event) token) (expectNumeral token') := by
  subst ht; unfold expectNumeral; canon_step []

theorem expectKeyword_canon {token : Internal.Input} (ht : token' = canon token) :
    CSim (expectKeyword (H := List Event) token) (expectKeyword token') := by
  subst ht; unfold expectKeyword; canon_step []

theorem expectString_canon {token : Internal.Input} (ht : token' = canon token) :
    CSim (expectString (H := List Event) token) (expectString token') := by
  subst ht; unfold expectString; canon_step []

theorem IdentState_step_canon {version : Token.Version} {state : IdentState}
    {token : Internal.Input} {state' : IdentState} (hs : state' = canon state)
    (ht : token' = canon token) :
    CSim (IdentState.step (H := List Event) version state token)
      (IdentState.step version state' token') := by
  subst hs ht; unfold IdentState.step; canon_step []

theorem sortComplete_canon {levels : List (SortLevel RSort)} {head : Identifier}
    {arguments : Array RSort} {levels' : List (SortLevel RSort)} {head' : Identifier}
    {arguments' : Array RSort} (hl : levels' = canon levels) (hh : head' = canon head)
    (ha : arguments' = canon arguments) :
    CSim (sortComplete (H := List Event) levels head arguments)
      (sortComplete levels' head' arguments') := by
  subst hl hh ha; unfold sortComplete; canon_step []

theorem sortStep_canon {version : Token.Version} {state : SortState RSort}
    {token : Internal.Input} {state' : SortState RSort} (hs : state' = canon state)
    (ht : token' = canon token) :
    CSim (sortStep (H := List Event) version state token) (sortStep version state' token') := by
  subst hs ht; unfold sortStep; canon_step []

theorem sExprStep_canon {version : Token.Version} {state : SExprState RSExpr}
    {token : Internal.Input} {state' : SExprState RSExpr} (hs : state' = canon state)
    (ht : token' = canon token) :
    CSim (sExprStep (H := List Event) version state token) (sExprStep version state' token') := by
  subst hs ht; unfold sExprStep; canon_step []

set_option maxHeartbeats 4000000 in
theorem attributeStep_canon {single : Bool} {version : Token.Version}
    {state : AttributeState RSExpr RAttribute} {token : Internal.Input}
    {state' : AttributeState RSExpr RAttribute}
    (hs : state' = canon state) (ht : token' = canon token) :
    CSim (attributeStep (H := List Event) single version state token)
      (attributeStep single version state' token') := by
  subst hs ht; unfold attributeStep; canon_step []

set_option maxHeartbeats 4000000 in
theorem PatternState_step_canon {version : Token.Version} {state : PatternState}
    {token : Internal.Input} {state' : PatternState} (hs : state' = canon state)
    (ht : token' = canon token) :
    CSim (PatternState.step (H := List Event) version state token)
      (PatternState.step version state' token') := by
  subst hs ht; unfold PatternState.step; canon_step []

theorem qualIdentStep_canon {version : Token.Version} {state : QualIdentState RSort}
    {token : Internal.Input} {state' : QualIdentState RSort} (hs : state' = canon state)
    (ht : token' = canon token) :
    CSim (qualIdentStep (H := List Event) version state token)
      (qualIdentStep version state' token') := by
  subst hs ht; unfold qualIdentStep; canon_step []

theorem sortedVarStep_canon {version : Token.Version} {state : SortedVarState RSort}
    {token : Internal.Input} {state' : SortedVarState RSort} (hs : state' = canon state)
    (ht : token' = canon token) :
    CSim (sortedVarStep (H := List Event) version state token)
      (sortedVarStep version state' token') := by
  subst hs ht; unfold sortedVarStep; canon_step []

theorem symbolStep_canon {state : Unit} {token : Internal.Input} (ht : token' = canon token) :
    CSim (symbolStep (H := List Event) state token) (symbolStep state token') := by
  subst ht; unfold symbolStep; canon_step []

set_option maxHeartbeats 400000 in
theorem ListState_step_canon {σ ρ : Type} [Canon σ] [Canon ρ] {init init' : σ}
    {inner : σ → Internal.Input → RPM (Internal.Step σ ρ)} {maximum : Option Nat}
    {state state' : ListState σ ρ} {token : Internal.Input}
    (hinner : ∀ state token state' token', state' = canon state → token' = canon token →
      CSim (inner state token) (inner state' token'))
    (hi : init' = canon init) (hs : state' = canon state) (ht : token' = canon token) :
    CSim (ListState.step init inner maximum state token)
      (ListState.step init' inner maximum state' token') := by
  subst hi hs ht; unfold ListState.step; canon_step []

theorem termComplete_canon {levels levels' : List (TermLevel RSort RTerm RScope)} {term : RTerm}
    (hl : levels' = canon levels) :
    CSim (termComplete (H := List Event) levels term) (termComplete levels' term) := by
  subst hl; unfold termComplete; canon_step []

theorem startBinder_canon {binder : SortedBinder}
    {variables variables' : Array (Plain.SymbolView × RSort)}
    (hv : variables' = canon variables) :
    CSim (startBinder (H := List Event) binder variables) (startBinder binder variables') := by
  subst hv; unfold startBinder; canon_step []

theorem endBinder_canon {kind : BinderKind} {scope : RScope} {term : RTerm} :
    CSim (endBinder (H := List Event) kind scope term) (endBinder kind scope term) := by
  unfold endBinder; canon_step []

theorem termOpened_canon {state state' : TermStateOf (List Event)} {token : Internal.Input}
    (hs : state' = canon state) (ht : token' = canon token) :
    CSim (termOpened (H := List Event) state token) (termOpened state' token') := by
  subst hs ht; unfold termOpened; canon_step []

set_option maxHeartbeats 8000000 in
theorem termStep_canon {version : Token.Version} {state state' : TermStateOf (List Event)}
    {token : Internal.Input} (hs : state' = canon state) (ht : token' = canon token) :
    CSim (termStep (H := List Event) version state token) (termStep version state' token') := by
  subst hs ht; unfold termStep; canon_step [sortedVarStep_canon]

end BSmtLib.Facts.Proofs.Parser.Canon.Steps

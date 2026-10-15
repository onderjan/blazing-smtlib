module

public import BSmtLib.Facts.Proofs.Parser.Blank.Tactic
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
# The steps of the categories, blanked

Each step of the parsers of the categories, run with a handler whose calls never fail, relates to
the step run with the blank handler on the blanked state (`BSim`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Blank.Steps

open Basic States Simp Tactic
open BSmtLib.Parser.Internal (PM)

open BSmtLib.Parser BSmtLib.Nodes BSmtLib.Traits
open BSmtLib.Parser.Category.Attribute BSmtLib.Parser.Category.Combinator
open BSmtLib.Parser.Category.Attribute.Internal
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Parser.Category.Ident BSmtLib.Parser.Category.Pattern
open BSmtLib.Parser.Category.Ident.Internal
open BSmtLib.Parser.Category.Pattern.Internal
open BSmtLib.Parser.Category.QualifiedIdent BSmtLib.Parser.Category.SExpr
open BSmtLib.Parser.Category.QualifiedIdent.Internal
open BSmtLib.Parser.Category.SExpr.Internal
open BSmtLib.Parser.Category.«Sort» BSmtLib.Parser.Category.SortedVar
open BSmtLib.Parser.Category.«Sort».Internal
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.Term BSmtLib.Parser.Category.Token
open BSmtLib.Parser.Category.Term.Internal
open BSmtLib.Parser.Category.Token.Internal

variable {H : Type} [CommandHandler H Id]

theorem expectOpen_blank {token : Internal.Input} :
    BSim (expectOpen (H := H) token) (expectOpen (H := Shell) token) := by
  unfold expectOpen; blank_step []

theorem expectClose_blank {token : Internal.Input} :
    BSim (expectClose (H := H) token) (expectClose (H := Shell) token) := by
  unfold expectClose; blank_step []

theorem expectSymbol_blank {token : Internal.Input} :
    BSim (expectSymbol (H := H) token) (expectSymbol (H := Shell) token) := by
  unfold expectSymbol; blank_step []

theorem expectNumeral_blank {token : Internal.Input} :
    BSim (expectNumeral (H := H) token) (expectNumeral (H := Shell) token) := by
  unfold expectNumeral; blank_step []

theorem expectKeyword_blank {token : Internal.Input} :
    BSim (expectKeyword (H := H) token) (expectKeyword (H := Shell) token) := by
  unfold expectKeyword; blank_step []

theorem expectString_blank {token : Internal.Input} :
    BSim (expectString (H := H) token) (expectString (H := Shell) token) := by
  unfold expectString; blank_step []

theorem IdentState_step_blank {version : Token.Version} {state : IdentState}
    {token : Internal.Input} :
    BSim (IdentState.step (H := H) version state token)
      (IdentState.step (H := Shell) version state token) := by
  unfold IdentState.step; blank_step []

theorem sortComplete_blank [NoFails H] {levels : List (SortLevel (Handler.«Sort» H))}
    {head : Identifier}
    {arguments : Array (Handler.«Sort» H)} {levels' : List (SortLevel Unit)}
    {arguments' : Array Unit} (hl : levels' = blank levels) (ha : arguments' = blank arguments) :
    BSim (sortComplete (H := H) levels head arguments)
      (sortComplete (H := Shell) levels' head arguments') := by
  subst hl ha; unfold sortComplete; blank_step []

theorem sortStep_blank [NoFails H] {version : Token.Version} {state : SortState (Handler.«Sort» H)}
    {token : Internal.Input} {state' : SortState Unit} (hs : state' = blank state) :
    BSim (sortStep (H := H) version state token) (sortStep (H := Shell) version state' token) := by
  subst hs; unfold sortStep; blank_step []

@[blank_simps] theorem blank_sExprComplete {X X' : Type} [Blanks X X'] (levels : SExprState X)
    (x : X) :
    blankStep (σ' := SExprState X') (ρ' := X') (sExprComplete levels x) =
      sExprComplete (blank levels) (blank x) := by
  cases levels <;> simp [sExprComplete, blankStep, Blanks.blank]

theorem sExprStep_blank [NoFails H] {version : Token.Version}
    {state : SExprState (Handler.SExpr H)} {token : Internal.Input} {state' : SExprState Unit}
    (hs : state' = blank state) :
    BSim (sExprStep (H := H) version state token)
      (sExprStep (H := Shell) version state' token) := by
  subst hs; unfold sExprStep; blank_step []

set_option maxHeartbeats 4000000 in
theorem attributeStep_blank [NoFails H] {single : Bool} {version : Token.Version}
    {state : AttributeState (Handler.SExpr H) (Handler.Attribute H)} {token : Internal.Input}
    {state' : AttributeState Unit Unit} (hs : state' = blank state) :
    BSim (attributeStep (H := H) single version state token)
      (attributeStep (H := Shell) single version state' token) := by
  subst hs; unfold attributeStep; blank_step []

set_option maxHeartbeats 4000000 in
theorem PatternState_step_blank {version : Token.Version} {state : PatternState}
    {token : Internal.Input} :
    BSim (PatternState.step (H := H) version state token)
      (PatternState.step (H := Shell) version state token) := by
  unfold PatternState.step; blank_step []

theorem qualIdentStep_blank [NoFails H] {version : Token.Version}
    {state : QualIdentState (Handler.«Sort» H)} {token : Internal.Input}
    {state' : QualIdentState Unit} (hs : state' = blank state) :
    BSim (qualIdentStep (H := H) version state token)
      (qualIdentStep (H := Shell) version state' token) := by
  subst hs; unfold qualIdentStep; blank_step []

theorem sortedVarStep_blank [NoFails H] {version : Token.Version}
    {state : SortedVarState (Handler.«Sort» H)} {token : Internal.Input}
    {state' : SortedVarState Unit} (hs : state' = blank state) :
    BSim (sortedVarStep (H := H) version state token)
      (sortedVarStep (H := Shell) version state' token) := by
  subst hs; unfold sortedVarStep; blank_step []

theorem symbolStep_blank {state : Unit} {token : Internal.Input} :
    BSim (symbolStep (H := H) state token) (symbolStep (H := Shell) state token) := by
  unfold symbolStep; blank_step []

set_option maxHeartbeats 400000 in
theorem ListState_step_blank {σ σ' ρ ρ' : Type} [Blanks σ σ'] [Blanks ρ ρ'] {init : σ}
    {init' : σ'} {inner : σ → Internal.Input → PM H (Internal.Step σ ρ)}
    {inner' : σ' → Internal.Input → PM Shell (Internal.Step σ' ρ')} {maximum : Option Nat}
    {state : ListState σ ρ} {state' : ListState σ' ρ'} {token : Internal.Input}
    (hinner : ∀ state token state', state' = blank state →
      BSim (inner state token) (inner' state' token))
    (hi : init' = blank init) (hs : state' = blank state) :
    BSim (ListState.step init inner maximum state token)
      (ListState.step init' inner' maximum state' token) := by
  subst hi hs; unfold ListState.step; blank_step []

theorem termComplete_blank [NoFails H] {levels : List (TermLevelOf H)} {term : Handler.Term H}
    {levels' : List (TermLevelOf Shell)} (hl : levels' = blank levels) :
    BSim (termComplete (H := H) levels term) (termComplete (H := Shell) levels' ()) := by
  subst hl; unfold termComplete; blank_step []

theorem startBinder_blank [NoFails H] {binder : SortedBinder}
    {variables : Array (Plain.SymbolView × Handler.«Sort» H)}
    {variables' : Array (Plain.SymbolView × Unit)}
    (hv : variables' = blank variables) :
    BSim (startBinder (H := H) binder variables) (startBinder (H := Shell) binder variables') := by
  subst hv; unfold startBinder; blank_step []

theorem endBinder_blank [NoFails H] {kind : BinderKind} {scope : Handler.Scope H}
    {term : Handler.Term H} :
    BSim (endBinder (H := H) kind scope term) (endBinder (H := Shell) kind () ()) := by
  unfold endBinder; blank_step []

theorem termOpened_blank {state : TermStateOf H} {token : Internal.Input}
    {state' : TermStateOf Shell} (hs : state' = blank state) :
    BSim (termOpened (H := H) state token) (termOpened (H := Shell) state' token) := by
  subst hs; unfold termOpened; blank_step []

set_option maxHeartbeats 8000000 in
theorem termStep_blank [NoFails H] {version : Token.Version} {state : TermStateOf H}
    {token : Internal.Input} {state' : TermStateOf Shell} (hs : state' = blank state) :
    BSim (termStep (H := H) version state token) (termStep (H := Shell) version state' token) := by
  subst hs; unfold termStep; blank_step [sortedVarStep_blank]

end BSmtLib.Facts.Proofs.Parser.Blank.Steps

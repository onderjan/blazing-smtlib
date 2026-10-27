module

public import BSmtLib.Facts.Proofs.Parser.Canon.States
public import BSmtLib.Facts.Proofs.Parser.Canon.Tactic
import all BSmtLib.Lexicon.Value
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Attribute
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Category.Pattern
import all BSmtLib.Parser.Category.SExpr
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Parser.Command.Internal.Standard

@[expose] public section

/-!
# The canonicalisation lemmas and the walk over a step

The simp set `canon_simps`: `Canon.canon` taken through the constructors, the containers and the
projections, the view of a view's content read back, and what reads contents only taken out of
the canonicalisation. `canon_step` walks a step on both sides: binds, results, errors, conditions,
handler calls and matches.
-/

namespace BSmtLib.Facts.Proofs.Parser.Canon.Simp

open BSmtLib.Grammar.Multiple (FunctionSignature)
open Basic States Tactic

open BSmtLib.Parser BSmtLib.Grammar.Nodes
open BSmtLib.Lexicon.Value (Symbol Numeral Decimal HexDigits BinDigits
  StringContent Keyword)

attribute [canon_simps]
  canonIndex.eq_1 canonIndex.eq_2 canonIdentifier.eq_1 canonConstant.eq_1
  canonConstant.eq_2 canonConstant.eq_3 canonConstant.eq_4 canonConstant.eq_5
  canonSymbolOrWildcard.eq_1 canonSymbolOrWildcard.eq_2 canonPattern.eq_1 canonPattern.eq_2
  canonInput.eq_1 canonInput.eq_2 canonInput.eq_3 canonInput.eq_4 canonInput.eq_5
  canonInput.eq_6 canonInput.eq_7 canonInput.eq_8 canonStep.eq_1 canonStep.eq_2
  canonIdentState.eq_1 canonIdentState.eq_2 canonIdentState.eq_3 canonIdentState.eq_4
  canonAttributeMode.eq_1 canonAttributeMode.eq_2 canonAttributeMode.eq_3
  canonAttributeState.eq_1 canonSortMode.eq_1 canonSortMode.eq_2 canonSortMode.eq_3
  canonSortMode.eq_4 canonSortLevel.eq_1 canonSortState.eq_1 canonSortedVarState.eq_1
  canonSortedVarState.eq_2 canonSortedVarState.eq_3 canonSortedVarState.eq_4
  canonQualIdentState.eq_1 canonQualIdentState.eq_2 canonQualIdentState.eq_3
  canonQualIdentState.eq_4 canonQualIdentState.eq_5 canonQualIdentState.eq_6
  canonPatternState.eq_1 canonPatternState.eq_2 canonPatternState.eq_3 canonListState.eq_1
  canonTermLevel.eq_1 canonTermLevel.eq_2 canonTermLevel.eq_3 canonTermLevel.eq_4
  canonTermLevel.eq_5 canonTermLevel.eq_6 canonTermMode.eq_1 canonTermMode.eq_2
  canonTermMode.eq_3 canonTermMode.eq_4 canonTermMode.eq_5 canonTermMode.eq_6
  canonTermMode.eq_7 canonTermMode.eq_8 canonTermMode.eq_9 canonTermMode.eq_10
  canonTermMode.eq_11 canonTermMode.eq_12 canonTermMode.eq_13 canonTermMode.eq_14
  canonTermMode.eq_15 canonTermMode.eq_16 canonTermState.eq_1 canonSortDecState.eq_1
  canonSortDecState.eq_2 canonSortDecState.eq_3 canonSortDecState.eq_4
  canonSignature.eq_1 canonConstructorState.eq_1 canonConstructorState.eq_2
  canonConstructorState.eq_3 canonDatatypeState.eq_1 canonDatatypeState.eq_2
  canonDatatypeState.eq_3 canonDatatypeState.eq_4 canonDatatypeState.eq_5
  canonDatatypeState.eq_6 canonDefinitionEnd.eq_1 canonDefinitionEnd.eq_2
  canonDefinitionEnd.eq_3 canonSignatureState.eq_1 canonSignatureState.eq_2
  canonSignatureState.eq_3 canonFunctionDecState.eq_1 canonFunctionDecState.eq_2
  canonFunctionDecState.eq_3 canonLiteralState.eq_1 canonFinalCall.eq_1 canonFinalCall.eq_2
  canonFinalCall.eq_3 canonFinalCall.eq_4 canonFinalCall.eq_5 canonFinalCall.eq_6
  canonFinalCall.eq_7 canonFinalCall.eq_8 canonFinalCall.eq_9 canonFinalCall.eq_10
  canonFinalCall.eq_11 canonFinalCall.eq_12 canonFinalCall.eq_13 canonFinalCall.eq_14
  canonFinalCall.eq_15 canonFinalCall.eq_16 canonFinalCall.eq_17 canonFinalCall.eq_18
  canonFinalCall.eq_19 canonFinalCall.eq_20 canonFinalCall.eq_21 canonFinalCall.eq_22
  canonFinalCall.eq_23 canonFinalCall.eq_24 canonFinalCall.eq_25 canonFinalCall.eq_26
  canonFinalCall.eq_27 canonFinalCall.eq_28 canonFinalCall.eq_29 canonFinalCall.eq_30
  canonPayload.eq_1 canonPayload.eq_2 canonPayload.eq_3 canonPayload.eq_4 canonPayload.eq_5
  canonPayload.eq_6 canonPayload.eq_7 canonPayload.eq_8 canonPayload.eq_9 canonPayload.eq_10
  canonPayload.eq_11 canonPayload.eq_12 canonPayload.eq_13 canonPayload.eq_14
  canonPayload.eq_15 canonPayload.eq_16 canonPayload.eq_17 canonPayload.eq_18
  canonPayload.eq_19 canonPayload.eq_20 canonPayload.eq_21 canonPayload.eq_22
  canonPayload.eq_23 canonPayload.eq_24 canonPayload.eq_25 canonPayload.eq_26
  canonPayload.eq_27 canonCommandState.eq_1 canonCommandState.eq_2 canonCommandState.eq_3
  canonCommandState.eq_4
  canonScriptParser Script.ScriptParser.Internal.posture_mk Script.ScriptParser.Internal.command_mk
  Script.ScriptParser.Internal.declarations_mk
  Array.map_push Array.map_empty List.map_cons List.map_nil Option.map_some
  Option.map_none id_eq Array.map_id List.map_id pure_bind
  canonTermNode.eq_1 canonTermNode.eq_2 canonTermNode.eq_3 canonSExprNode.eq_1 canonSExprNode.eq_2
  canonSExprNode.eq_3 canonSExprNode.eq_4 canonSExprNode.eq_5 canonAttributeValueNode.eq_1
  canonAttributeValueNode.eq_2 canonAttributeValueNode.eq_3

section

open BSmtLib.Parser.Category.Attribute BSmtLib.Parser.Category.Combinator
open BSmtLib.Parser.Category.«Sort» BSmtLib.Parser.Category.Term
open BSmtLib.Parser.Command.Internal.Standard BSmtLib.Parser.Category.Pattern
open BSmtLib.Parser.Category.Ident BSmtLib.Parser.Category.SortedVar
open BSmtLib.Parser.Category.QualifiedIdent BSmtLib.Parser.Command
open BSmtLib.Parser.Command.Internal.Datatype
open BSmtLib.Parser.Command.Internal.Definition BSmtLib.Parser.Command.Internal.Function
open BSmtLibSpec.Parser.Properties (Event)
open BSmtLib.Parser.Category.Attribute.Internal
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Parser.Category.«Sort».Internal
open BSmtLib.Parser.Category.Term.Internal
open BSmtLib.Parser.Category.Pattern.Internal
open BSmtLib.Parser.Category.Ident.Internal
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.QualifiedIdent.Internal
open BSmtLib.Parser.Command.Internal

variable {SE A S T Sc : Type} [Canon SE] [Canon A] [Canon S] [Canon T] [Canon Sc]

@[canon_simps] theorem name_canonIdentifier (i : Ident) :
    (canonIdentifier i).name = canon i.name := by cases i; rfl
@[canon_simps] theorem indices_canonIdentifier (i : Ident) :
    (canonIdentifier i).indices = canon i.indices := by cases i; rfl
@[canon_simps] theorem mode_canonAttributeState (s : AttributeState SE A) :
    (canonAttributeState s).mode = canon s.mode := by cases s; rfl
@[canon_simps] theorem attributes_canonAttributeState (s : AttributeState SE A) :
    (canonAttributeState s).attributes = canon s.attributes := by cases s; rfl
@[canon_simps] theorem head_canonSortLevel (l : SortLevel S) :
    (canonSortLevel l).head = canon l.head := by cases l; rfl
@[canon_simps] theorem arguments_canonSortLevel (l : SortLevel S) :
    (canonSortLevel l).arguments = canon l.arguments := by cases l; rfl
@[canon_simps] theorem mode_canonSortState (s : SortState S) :
    (canonSortState s).mode = canon s.mode := by cases s; rfl
@[canon_simps] theorem levels_canonSortState (s : SortState S) :
    (canonSortState s).levels = canon s.levels := by cases s; rfl
@[canon_simps] theorem opened_canonListState {σ ρ : Type} [Canon σ] [Canon ρ]
    (s : ListState σ ρ) : (canonListState s).opened = s.opened := by cases s; rfl
@[canon_simps] theorem outside_canonListState {σ ρ : Type} [Canon σ] [Canon ρ]
    (s : ListState σ ρ) : (canonListState s).outside = s.outside := by cases s; rfl
@[canon_simps] theorem inner_canonListState {σ ρ : Type} [Canon σ] [Canon ρ]
    (s : ListState σ ρ) : (canonListState s).inner = canon s.inner := by cases s; rfl
@[canon_simps] theorem items_canonListState {σ ρ : Type} [Canon σ] [Canon ρ]
    (s : ListState σ ρ) : (canonListState s).items = canon s.items := by cases s; rfl
@[canon_simps] theorem mode_canonTermState (s : TermState SE A S T Sc) :
    (canonTermState s).mode = canon s.mode := by cases s; rfl
@[canon_simps] theorem levels_canonTermState (s : TermState SE A S T Sc) :
    (canonTermState s).levels = canon s.levels := by cases s; rfl
@[canon_simps] theorem name_canonSignature (s : FunctionSignature S) :
    (canonSignature s).name = canon s.name := by simp [canonSignature]
@[canon_simps] theorem params_canonSignature (s : FunctionSignature S) :
    (canonSignature s).params = canon s.params := by simp [canonSignature]
@[canon_simps] theorem resultSort_canonSignature (s : FunctionSignature S) :
    (canonSignature s).resultSort = canon s.resultSort := by simp [canonSignature]
@[canon_simps] theorem shape_canonLiteralState (s : LiteralState SE A S T Sc) :
    (canonLiteralState s).shape = s.shape := by cases s; rfl
@[canon_simps] theorem term_canonLiteralState (s : LiteralState SE A S T Sc) :
    (canonLiteralState s).term = canon s.term := by cases s; rfl

section

variable (w : Lexicon.Reserved.GeneralReserved)

@[canon_simps] theorem isWord_parenOpen : Internal.Input.parenOpen.isWord w = false := (rfl)
@[canon_simps] theorem isWord_parenClose : Internal.Input.parenClose.isWord w = false := (rfl)
@[canon_simps] theorem isWord_constant (c : SpecialConstant) :
    (Internal.Input.constant c).isWord w = false := (rfl)
@[canon_simps] theorem isWord_symbol (s : Symbol) :
    (Internal.Input.symbol s).isWord w = false :=
  (rfl)
@[canon_simps] theorem isWord_keyword (k : BSmtLib.Lexicon.Value.Keyword) :
    (Internal.Input.keyword k).isWord w = false := (rfl)
@[canon_simps] theorem isWord_endOfInput : Internal.Input.endOfInput.isWord w = false := (rfl)
@[canon_simps] theorem isWord_layout : Internal.Input.layout.isWord w = false := (rfl)
@[canon_simps] theorem isWord_commandName (c : Lexicon.Reserved.CommandNameReserved) :
    (Internal.Input.reserved (.commandName c)).isWord w = false := (rfl)
@[canon_simps] theorem isWord_general (w' : Lexicon.Reserved.GeneralReserved) :
    (Internal.Input.reserved (.general w')).isWord w = (w' == w) := (rfl)

end

@[canon_simps] theorem isWord_canonInput (t : Internal.Input)
    (w : Lexicon.Reserved.GeneralReserved) :
    (canonInput t).isWord w = t.isWord w := by cases t <;> rfl

@[canon_simps] theorem canonStep_id {σ ρ : Type} [Canon σ] [Canon ρ] [CanonId σ] [CanonId ρ]
    (s : Internal.Step σ ρ) : canonStep s = s := by
  cases s <;> simp only [canonStep, CanonId.canon_id]

@[canon_simps] theorem canon_sExpr (x : Handler.SExpr (List Event)) : canon x = x := (rfl)
@[canon_simps] theorem canon_attribute (x : Handler.Attribute (List Event)) :
    canon x = x := (rfl)
@[canon_simps] theorem canon_sort (x : Handler.«Sort» (List Event)) : canon x = x := (rfl)
@[canon_simps] theorem canon_term (x : Handler.Term (List Event)) : canon x = x := (rfl)
@[canon_simps] theorem canon_scope (x : Handler.Scope (List Event)) : canon x = x := (rfl)

@[canon_simps] theorem canon_attributeState_init :
    canonAttributeState (AttributeState.init : AttributeState SE A) = .init := by
  simp only [AttributeState.init, canon_simps, Canon.canon]
@[canon_simps] theorem canon_sortState_init :
    canonSortState (SortState.init : SortState S) = .init := (rfl)
@[canon_simps] theorem canon_termState_init :
    canonTermState (TermState.init : TermState SE A S T Sc) = .init := (rfl)
@[canon_simps] theorem canon_literalState_init :
    canonLiteralState (LiteralState.init : LiteralState SE A S T Sc) = .init := (rfl)
@[canon_simps] theorem canon_paren {σ ρ : Type} [Canon σ] [Canon ρ] (init : σ) :
    canonListState (ListState.paren init : ListState σ ρ) = .paren (canon init) := by
  simp only [ListState.paren, canon_simps, Canon.canon]
@[canon_simps] theorem canon_closed {σ ρ : Type} [Canon σ] [Canon ρ] (init : σ) :
    canonListState (ListState.closed init : ListState σ ρ) = .closed (canon init) := by
  simp only [ListState.closed, canon_simps, Canon.canon]
@[canon_simps] theorem canon_payload_init (name : Lexicon.Reserved.CommandNameReserved)
    (version : Version) :
    canonPayload (Payload.init name version : Payload SE A S T Sc) = .init name version := by
  cases name <;> simp only [Payload.init] <;> (try split) <;>
    simp only [canon_simps, Canon.canon, ListState.paren,
    TermState.init, AttributeState.init, LiteralState.init]


attribute [canon_simps] Array.map_id_fun List.map_id_fun PatternState.symbolOrWildcard?
  Bool.and_false Bool.and_true Bool.false_and Bool.true_and

@[canon_simps] theorem list_map_canon_id {α : Type} [Canon α] [CanonId α] (l : List α) :
    l.map canon = l := CanonId.canon_id l

@[canon_simps] theorem array_map_canon_id {α : Type} [Canon α] [CanonId α] (a : Array α) :
    a.map canon = a := CanonId.canon_id a

@[canon_simps] theorem option_map_canon_id {α : Type} [Canon α] [CanonId α] (o : Option α) :
    o.map canon = o := CanonId.canon_id o


variable {X : Type} [Canon X]

@[canon_simps] theorem fun_canonIdentState :
    (canon : IdentState → IdentState) = canonIdentState := (rfl)
@[canon_simps] theorem fun_canonAttributeMode :
    (canon : (AttributeMode SE) → (AttributeMode SE)) = canonAttributeMode := (rfl)
@[canon_simps] theorem fun_canonAttributeState :
    (canon : (AttributeState SE A) → (AttributeState SE A)) = canonAttributeState := (rfl)
@[canon_simps] theorem fun_canonSortMode :
    (canon : SortMode → SortMode) = canonSortMode := (rfl)
@[canon_simps] theorem fun_canonSortLevel :
    (canon : (SortLevel S) → (SortLevel S)) = canonSortLevel := (rfl)
@[canon_simps] theorem fun_canonSortState :
    (canon : (SortState S) → (SortState S)) = canonSortState := (rfl)
@[canon_simps] theorem fun_canonSortedVarState :
    (canon : (SortedVarState S) → (SortedVarState S)) = canonSortedVarState := (rfl)
@[canon_simps] theorem fun_canonQualIdentState :
    (canon : (QualIdentState S) → (QualIdentState S)) = canonQualIdentState := (rfl)
@[canon_simps] theorem fun_canonPatternState :
    (canon : PatternState → PatternState) = canonPatternState := (rfl)
@[canon_simps] theorem fun_canonListState {σ ρ : Type} [Canon σ] [Canon ρ] :
    (canon : (ListState σ ρ) → (ListState σ ρ)) = canonListState := (rfl)
@[canon_simps] theorem fun_canonTermLevel :
    (canon : (TermLevel S T Sc) → (TermLevel S T Sc)) = canonTermLevel := (rfl)
@[canon_simps] theorem fun_canonTermMode :
    (canon : (TermMode SE A S T Sc) → (TermMode SE A S T Sc)) = canonTermMode := (rfl)
@[canon_simps] theorem fun_canonTermState :
    (canon : (TermState SE A S T Sc) → (TermState SE A S T Sc)) = canonTermState := (rfl)
@[canon_simps] theorem fun_canonSortDecState :
    (canon : SortDecState → SortDecState) = canonSortDecState := (rfl)
@[canon_simps] theorem fun_canonSignature :
    (canon : (FunctionSignature S) → (FunctionSignature S)) = canonSignature := (rfl)
@[canon_simps] theorem fun_canonConstructorState :
    (canon : (ConstructorState S) → (ConstructorState S)) = canonConstructorState := (rfl)
@[canon_simps] theorem fun_canonDatatypeState :
    (canon : (DatatypeState S) → (DatatypeState S)) = canonDatatypeState := (rfl)
@[canon_simps] theorem fun_canonDefinitionEnd :
    (canon : (DefinitionEnd S) → (DefinitionEnd S)) = canonDefinitionEnd := (rfl)
@[canon_simps] theorem fun_canonSignatureState :
    (canon : (SignatureState S) → (SignatureState S)) = canonSignatureState := (rfl)
@[canon_simps] theorem fun_canonFunctionDecState :
    (canon : (FunctionDecState S) → (FunctionDecState S)) = canonFunctionDecState := (rfl)
@[canon_simps] theorem fun_canonLiteralState :
    (canon : (LiteralState SE A S T Sc) → (LiteralState SE A S T Sc)) = canonLiteralState := (rfl)
omit [Canon A] in
@[canon_simps] theorem fun_canonFinalCall :
    (canon : (FinalCall A S T) → (FinalCall A S T)) = canonFinalCall := (rfl)
@[canon_simps] theorem fun_canonPayload :
    (canon : (Payload SE A S T Sc) → (Payload SE A S T Sc)) = canonPayload := (rfl)
@[canon_simps] theorem fun_canonCommandState {N : Type} :
    (canon : (CommandState SE A S T Sc N) → (CommandState SE A S T Sc N)) =
      canonCommandState := (rfl)
@[canon_simps] theorem fun_canonSymbol :
    (canon : Symbol → Symbol) = canonSymbol := (rfl)
@[canon_simps] theorem fun_canonIndex :
    (canon : Index → Index) = canonIndex := (rfl)
@[canon_simps] theorem fun_canonIdentifier :
    (canon : Ident → Ident) = canonIdentifier := (rfl)
@[canon_simps] theorem fun_canonConstant :
    (canon : SpecialConstant → SpecialConstant) = canonConstant := (rfl)
@[canon_simps] theorem fun_canonSymbolOrWildcard :
    (canon : SimplePattern → SimplePattern) = canonSymbolOrWildcard := (rfl)
@[canon_simps] theorem fun_canonPattern :
    (canon : Pattern → Pattern) = canonPattern := (rfl)
@[canon_simps] theorem fun_canonTermNode {S T : Type} [Canon S] [Canon T] :
    (canon : (Grammar.Nodes.Term S T) → (Grammar.Nodes.Term S T)) = canonTermNode := (rfl)
@[canon_simps] theorem fun_canonSExprNode {X : Type} [Canon X] :
    (canon : (Grammar.Nodes.SExpr X) → (Grammar.Nodes.SExpr X)) = canonSExprNode := (rfl)
@[canon_simps] theorem fun_canonAttributeValueNode {X : Type} [Canon X] :
    (canon : (AttributeValue X) → (AttributeValue X)) = canonAttributeValueNode := (rfl)
@[canon_simps] theorem fun_canonInput :
    (canon : Internal.Input → Internal.Input) = canonInput := (rfl)
@[canon_simps] theorem fun_canonStep {σ ρ : Type} [Canon σ] [Canon ρ] :
    (canon : (Internal.Step σ ρ) → (Internal.Step σ ρ)) = canonStep := (rfl)

@[canon_simps] theorem fun_prod {α β : Type} [Canon α] [Canon β] :
    (canon : α × β → α × β) = fun p => (canon p.1, canon p.2) := (rfl)

@[canon_simps] theorem isEmpty_map {α β : Type} (f : α → β) (a : Array α) :
    (a.map f).isEmpty = a.isEmpty := by simp [Array.isEmpty]

@[canon_simps] theorem size_map {α β : Type} (f : α → β) (a : Array α) :
    (a.map f).size = a.size := Array.size_map ..

end

@[canon_simps] theorem asSlice_newUnchecked_symbol (q : Bool) (s : ByteSlice) :
    (Symbol.Internal.newUnchecked q s).asSlice = s := (rfl)
@[canon_simps] theorem isQuoted_newUnchecked_symbol (q : Bool) (s : ByteSlice) :
    (Symbol.Internal.newUnchecked q s).isQuoted = q := (rfl)
@[canon_simps] theorem asSlice_newUnchecked_numeral (s : ByteSlice) :
    (Numeral.Internal.newUnchecked s).asSlice = s := (rfl)
@[canon_simps] theorem asSlice_newUnchecked_decimal (s : ByteSlice) :
    (Decimal.Internal.newUnchecked s).asSlice = s := (rfl)
@[canon_simps] theorem asSlice_newUnchecked_hexDigits (s : ByteSlice) :
    (HexDigits.Internal.newUnchecked s).asSlice = s := (rfl)
@[canon_simps] theorem asSlice_newUnchecked_binDigits (s : ByteSlice) :
    (BinDigits.Internal.newUnchecked s).asSlice = s := (rfl)
@[canon_simps] theorem asSlice_newUnchecked_stringContent (s : ByteSlice) :
    (StringContent.Internal.newUnchecked s).asSlice = s := (rfl)
@[canon_simps] theorem asSlice_newUnchecked_keyword (s : ByteSlice) :
    (Keyword.Internal.newUnchecked s).asSlice = s := (rfl)

attribute [canon_simps] toByteArray_canonSlice

/-- The simp set of canonicalisation, with the instances unfolded. -/
macro "canon_simp" : tactic => `(tactic| simp only [Canon.canon, canon_simps])


end BSmtLib.Facts.Proofs.Parser.Canon.Simp

module

public import BSmtLib.Facts.Proofs.Parser.Blank.States
import all BSmtLib.Parser
import all BSmtLib.Parser.Category.Attribute
import all BSmtLib.Parser.Category.Combinator
import all BSmtLib.Parser.Category.Sort
import all BSmtLib.Parser.Category.Term
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# The blanking lemmas

The simp set `blank_simps`: `Blanks.blank` taken through the constructors, the containers and the
projections of the parser's values and states, and the initial states.
-/

namespace BSmtLib.Facts.Proofs.Parser.Blank.Simp

open Basic States

open BSmtLib.Grammar (Multiple)
open BSmtLib.Parser BSmtLib.Grammar.Nodes
open BSmtLib.Parser.Category.Attribute BSmtLib.Parser.Category.Combinator
open BSmtLib.Parser.Category.Attribute.Internal
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Parser.Category.«Sort» BSmtLib.Parser.Category.Term
open BSmtLib.Parser.Category.«Sort».Internal
open BSmtLib.Parser.Category.Term.Internal
open BSmtLib.Parser.Command.Internal.Standard BSmtLib.Parser.Category.SortedVar
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.QualifiedIdent BSmtLib.Parser.Command
open BSmtLib.Parser.Command.Internal.Datatype
open BSmtLib.Parser.Category.QualifiedIdent.Internal
open BSmtLib.Parser.Command.Internal
open BSmtLib.Parser.Command.Internal.Definition BSmtLib.Parser.Command.Internal.Function
open BSmtLib.Parser.Script

attribute [blank_simps]
  blankQualifiedIdent.eq_1 blankTermNode.eq_1 blankTermNode.eq_2 blankTermNode.eq_3
  blankSExprNode.eq_1 blankSExprNode.eq_2 blankSExprNode.eq_3 blankSExprNode.eq_4
  blankSExprNode.eq_5 blankAttributeValueNode.eq_1 blankAttributeValueNode.eq_2
  blankAttributeValueNode.eq_3 blankSignature.eq_1 blankStep.eq_1
  blankStep.eq_2 blankCause.eq_1 blankCause.eq_2 blankResult.eq_1 blankResult.eq_2
  blankAttributeMode.eq_1 blankAttributeMode.eq_2 blankAttributeMode.eq_3
  blankAttributeState.eq_1 blankSortLevel.eq_1 blankSortState.eq_1 blankSortedVarState.eq_1
  blankSortedVarState.eq_2 blankSortedVarState.eq_3 blankSortedVarState.eq_4
  blankQualIdentState.eq_1 blankQualIdentState.eq_2 blankQualIdentState.eq_3
  blankQualIdentState.eq_4 blankQualIdentState.eq_5 blankQualIdentState.eq_6 blankListState.eq_1
  blankTermLevel.eq_1 blankTermLevel.eq_2 blankTermLevel.eq_3 blankTermLevel.eq_4
  blankTermLevel.eq_5 blankTermLevel.eq_6 blankTermMode.eq_1 blankTermMode.eq_2
  blankTermMode.eq_3 blankTermMode.eq_4 blankTermMode.eq_5 blankTermMode.eq_6 blankTermMode.eq_7
  blankTermMode.eq_8 blankTermMode.eq_9 blankTermMode.eq_10 blankTermMode.eq_11
  blankTermMode.eq_12 blankTermMode.eq_13 blankTermMode.eq_14 blankTermMode.eq_15
  blankTermMode.eq_16 blankTermState.eq_1 blankConstructorState.eq_1 blankConstructorState.eq_2
  blankConstructorState.eq_3 blankDatatypeState.eq_1 blankDatatypeState.eq_2
  blankDatatypeState.eq_3 blankDatatypeState.eq_4 blankDatatypeState.eq_5 blankDatatypeState.eq_6
  blankDefinitionEnd.eq_1 blankDefinitionEnd.eq_2 blankDefinitionEnd.eq_3
  blankSignatureState.eq_1 blankSignatureState.eq_2 blankSignatureState.eq_3
  blankFunctionDecState.eq_1 blankFunctionDecState.eq_2 blankFunctionDecState.eq_3
  blankLiteralState.eq_1 blankFinalCall.eq_1 blankFinalCall.eq_2 blankFinalCall.eq_3
  blankFinalCall.eq_4 blankFinalCall.eq_5 blankFinalCall.eq_6 blankFinalCall.eq_7
  blankFinalCall.eq_8 blankFinalCall.eq_9 blankFinalCall.eq_10 blankFinalCall.eq_11
  blankFinalCall.eq_12 blankFinalCall.eq_13 blankFinalCall.eq_14 blankFinalCall.eq_15
  blankFinalCall.eq_16 blankFinalCall.eq_17 blankFinalCall.eq_18 blankFinalCall.eq_19
  blankFinalCall.eq_20 blankFinalCall.eq_21 blankFinalCall.eq_22 blankFinalCall.eq_23
  blankFinalCall.eq_24 blankFinalCall.eq_25 blankFinalCall.eq_26 blankFinalCall.eq_27
  blankFinalCall.eq_28 blankFinalCall.eq_29 blankFinalCall.eq_30 blankPayload.eq_1
  blankPayload.eq_2 blankPayload.eq_3 blankPayload.eq_4 blankPayload.eq_5 blankPayload.eq_6
  blankPayload.eq_7 blankPayload.eq_8 blankPayload.eq_9 blankPayload.eq_10 blankPayload.eq_11
  blankPayload.eq_12 blankPayload.eq_13 blankPayload.eq_14 blankPayload.eq_15 blankPayload.eq_16
  blankPayload.eq_17 blankPayload.eq_18 blankPayload.eq_19 blankPayload.eq_20 blankPayload.eq_21
  blankPayload.eq_22 blankPayload.eq_23 blankPayload.eq_24 blankPayload.eq_25 blankPayload.eq_26
  blankPayload.eq_27 blankCommandState.eq_1 blankCommandState.eq_2 blankCommandState.eq_3
  blankCommandState.eq_4 Grammar.Multiple.asSlice_new Grammar.Multiple.NamedValues.Internal.toArray_new
  Grammar.Multiple.Constructors.Internal.toArray_new Grammar.Multiple.MatchCases.Internal.toArray_new
  Grammar.Multiple.FunctionSignatures.Internal.toArray_new Grammar.Multiple.FunctionSignature.Internal.name_new
  Grammar.Multiple.FunctionSignature.Internal.params_new Grammar.Multiple.FunctionSignature.Internal.resultSort_new
  blankScriptParser Script.ScriptParser.Internal.posture_mk Script.ScriptParser.Internal.command_mk
  Script.ScriptParser.Internal.declarations_mk
  Array.map_push Array.map_empty List.map_cons List.map_nil Option.map_some Option.map_none
  id_eq Array.map_id List.map_id Option.map_id pure_bind Array.map_id_fun List.map_id_fun
  Option.map_id_fun Bool.and_false Bool.and_true Bool.false_and Bool.true_and

section

variable {SE SE' A A' S S' T T' Sc Sc' : Type} [Blanks SE SE'] [Blanks A A'] [Blanks S S']
  [Blanks T T'] [Blanks Sc Sc']

/-! ## Projections -/

@[blank_simps] theorem ident_blankQualifiedIdent (q : QualifiedIdent S) :
    (blankQualifiedIdent (S' := S') q).ident = q.ident := by cases q; rfl
@[blank_simps] theorem sort_blankQualifiedIdent (q : QualifiedIdent S) :
    (blankQualifiedIdent (S' := S') q).sort = blank q.sort := by cases q; rfl
@[blank_simps] theorem mode_blankAttributeState (s : AttributeState SE A) :
    (blankAttributeState (SE' := SE') (A' := A') s).mode = blank s.mode := by cases s; rfl
@[blank_simps] theorem attributes_blankAttributeState (s : AttributeState SE A) :
    (blankAttributeState (SE' := SE') (A' := A') s).attributes = blank s.attributes := by
  cases s; rfl
@[blank_simps] theorem head_blankSortLevel (l : SortLevel S) :
    (blankSortLevel (S' := S') l).head = l.head := by cases l; rfl
@[blank_simps] theorem arguments_blankSortLevel (l : SortLevel S) :
    (blankSortLevel (S' := S') l).arguments = blank l.arguments := by cases l; rfl
@[blank_simps] theorem mode_blankSortState (s : SortState S) :
    (blankSortState (S' := S') s).mode = s.mode := by cases s; rfl
@[blank_simps] theorem levels_blankSortState (s : SortState S) :
    (blankSortState (S' := S') s).levels = blank s.levels := by cases s; rfl
@[blank_simps] theorem opened_blankListState {σ σ' ρ ρ' : Type} [Blanks σ σ'] [Blanks ρ ρ']
    (s : ListState σ ρ) : (blankListState (σ' := σ') (ρ' := ρ') s).opened = s.opened := by
  cases s; rfl
@[blank_simps] theorem outside_blankListState {σ σ' ρ ρ' : Type} [Blanks σ σ'] [Blanks ρ ρ']
    (s : ListState σ ρ) : (blankListState (σ' := σ') (ρ' := ρ') s).outside = s.outside := by
  cases s; rfl
@[blank_simps] theorem inner_blankListState {σ σ' ρ ρ' : Type} [Blanks σ σ'] [Blanks ρ ρ']
    (s : ListState σ ρ) : (blankListState (σ' := σ') (ρ' := ρ') s).inner = blank s.inner := by
  cases s; rfl
@[blank_simps] theorem items_blankListState {σ σ' ρ ρ' : Type} [Blanks σ σ'] [Blanks ρ ρ']
    (s : ListState σ ρ) : (blankListState (σ' := σ') (ρ' := ρ') s).items = blank s.items := by
  cases s; rfl
@[blank_simps] theorem mode_blankTermState (s : TermState SE A S T Sc) :
    (blankTermState (SE' := SE') (A' := A') (S' := S') (T' := T') (Sc' := Sc') s).mode =
      blank s.mode := by cases s; rfl
@[blank_simps] theorem levels_blankTermState (s : TermState SE A S T Sc) :
    (blankTermState (SE' := SE') (A' := A') (S' := S') (T' := T') (Sc' := Sc') s).levels =
      blank s.levels := by cases s; rfl
@[blank_simps] theorem name_blankSignature (s : Grammar.Multiple.FunctionSignature S) :
    (blankSignature (S' := S') s).name = s.name := by simp [blankSignature]
@[blank_simps] theorem params_blankSignature (s : Grammar.Multiple.FunctionSignature S) :
    (blankSignature (S' := S') s).params = blank s.params := by simp [blankSignature]
@[blank_simps] theorem resultSort_blankSignature (s : Grammar.Multiple.FunctionSignature S) :
    (blankSignature (S' := S') s).resultSort = blank s.resultSort := by simp [blankSignature]
@[blank_simps] theorem shape_blankLiteralState (s : LiteralState SE A S T Sc) :
    (blankLiteralState (SE' := SE') (A' := A') (S' := S') (T' := T') (Sc' := Sc') s).shape =
      s.shape := by cases s; rfl
@[blank_simps] theorem term_blankLiteralState (s : LiteralState SE A S T Sc) :
    (blankLiteralState (SE' := SE') (A' := A') (S' := S') (T' := T') (Sc' := Sc') s).term =
      blank s.term := by cases s; rfl

/-! ## The initial states -/

@[blank_simps] theorem blank_attributeState_init :
    blankAttributeState (SE' := SE') (A' := A') (AttributeState.init : AttributeState SE A) =
      .init := by
  simp only [AttributeState.init, blankAttributeState, blankAttributeMode, Blanks.blank,
    Array.map_empty]
@[blank_simps] theorem blank_sortState_init :
    blankSortState (S' := S') (SortState.init : SortState S) = .init := (rfl)
@[blank_simps] theorem blank_termState_init :
    blankTermState (SE' := SE') (A' := A') (S' := S') (T' := T') (Sc' := Sc')
      (TermState.init : TermState SE A S T Sc) = .init := (rfl)
@[blank_simps] theorem blank_literalState_init :
    blankLiteralState (SE' := SE') (A' := A') (S' := S') (T' := T') (Sc' := Sc')
      (LiteralState.init : LiteralState SE A S T Sc) = .init := (rfl)
@[blank_simps] theorem blank_paren {σ σ' ρ ρ' : Type} [Blanks σ σ'] [Blanks ρ ρ'] (init : σ) :
    blankListState (σ' := σ') (ρ' := ρ') (ListState.paren init : ListState σ ρ) =
      .paren (blank init) := by
  simp only [ListState.paren, blankListState, Blanks.blank, Array.map_empty]
@[blank_simps] theorem blank_closed {σ σ' ρ ρ' : Type} [Blanks σ σ'] [Blanks ρ ρ'] (init : σ) :
    blankListState (σ' := σ') (ρ' := ρ') (ListState.closed init : ListState σ ρ) =
      .closed (blank init) := by
  simp only [ListState.closed, blankListState, Blanks.blank, Array.map_empty]
@[blank_simps] theorem blank_payload_init (name : Token.Reserved.CommandNameReserved)
    (version : Version) :
    blankPayload (SE' := SE') (A' := A') (S' := S') (T' := T') (Sc' := Sc')
      (Payload.init name version : Payload SE A S T Sc) = .init name version := by
  cases name <;> simp only [Payload.init] <;> (try split) <;>
    simp only [blankPayload, blankFinalCall, Blanks.blank, blankListState, ListState.paren,
      blankTermState, TermState.init, blankAttributeState, AttributeState.init,
      blankLiteralState, LiteralState.init, Array.map_empty, List.map_nil, blankTermMode,
      blankAttributeMode] <;> rfl

/-! ## The maps as functions -/

@[blank_simps] theorem fun_blankAttributeMode :
    (blank : AttributeMode SE → AttributeMode SE') = blankAttributeMode := (rfl)
@[blank_simps] theorem fun_blankAttributeState :
    (blank : AttributeState SE A → AttributeState SE' A') = blankAttributeState := (rfl)
@[blank_simps] theorem fun_blankSortLevel :
    (blank : SortLevel S → SortLevel S') = blankSortLevel := (rfl)
@[blank_simps] theorem fun_blankSortState :
    (blank : SortState S → SortState S') = blankSortState := (rfl)
@[blank_simps] theorem fun_blankSortedVarState :
    (blank : SortedVarState S → SortedVarState S') = blankSortedVarState := (rfl)
@[blank_simps] theorem fun_blankQualIdentState :
    (blank : QualIdentState S → QualIdentState S') = blankQualIdentState := (rfl)
@[blank_simps] theorem fun_blankListState {σ σ' ρ ρ' : Type} [Blanks σ σ'] [Blanks ρ ρ'] :
    (blank : ListState σ ρ → ListState σ' ρ') = blankListState := (rfl)
@[blank_simps] theorem fun_blankTermLevel :
    (blank : TermLevel S T Sc → TermLevel S' T' Sc') = blankTermLevel := (rfl)
@[blank_simps] theorem fun_blankTermMode :
    (blank : TermMode SE A S T Sc → TermMode SE' A' S' T' Sc') = blankTermMode := (rfl)
@[blank_simps] theorem fun_blankTermState :
    (blank : TermState SE A S T Sc → TermState SE' A' S' T' Sc') = blankTermState := (rfl)
@[blank_simps] theorem fun_blankConstructorState :
    (blank : ConstructorState S → ConstructorState S') = blankConstructorState := (rfl)
@[blank_simps] theorem fun_blankDatatypeState :
    (blank : DatatypeState S → DatatypeState S') = blankDatatypeState := (rfl)
@[blank_simps] theorem fun_blankDefinitionEnd :
    (blank : DefinitionEnd S → DefinitionEnd S') = blankDefinitionEnd := (rfl)
@[blank_simps] theorem fun_blankSignatureState :
    (blank : SignatureState S → SignatureState S') = blankSignatureState := (rfl)
@[blank_simps] theorem fun_blankFunctionDecState :
    (blank : FunctionDecState S → FunctionDecState S') = blankFunctionDecState := (rfl)
@[blank_simps] theorem fun_blankLiteralState :
    (blank : LiteralState SE A S T Sc → LiteralState SE' A' S' T' Sc') = blankLiteralState :=
  (rfl)
@[blank_simps] theorem fun_blankFinalCall :
    (blank : FinalCall A S T → FinalCall A' S' T') = blankFinalCall := (rfl)
@[blank_simps] theorem fun_blankPayload :
    (blank : Payload SE A S T Sc → Payload SE' A' S' T' Sc') = blankPayload := (rfl)
@[blank_simps] theorem fun_blankCommandState {N : Type} :
    (blank : CommandState SE A S T Sc N → CommandState SE' A' S' T' Sc' Empty) =
      blankCommandState := (rfl)
@[blank_simps] theorem fun_blankQualifiedIdent :
    (blank : QualifiedIdent S → QualifiedIdent S') = blankQualifiedIdent := (rfl)
@[blank_simps] theorem fun_blankTermNode :
    (blank : Grammar.Nodes.Term S T → Grammar.Nodes.Term S' T') = blankTermNode := (rfl)
@[blank_simps] theorem fun_blankSExprNode :
    (blank : Grammar.Nodes.SExpr SE → Grammar.Nodes.SExpr SE') = blankSExprNode := (rfl)
@[blank_simps] theorem fun_blankAttributeValueNode :
    (blank : AttributeValue SE → AttributeValue SE') = blankAttributeValueNode := (rfl)
@[blank_simps] theorem fun_blankSignature :
    (blank : Grammar.Multiple.FunctionSignature S → Grammar.Multiple.FunctionSignature S') = blankSignature := (rfl)
@[blank_simps] theorem fun_blank_multiple {α β : Type} [Blanks α β] :
    (blank : Multiple α → Multiple β) = fun m => Grammar.Multiple.new (blank m.asSlice) := (rfl)
@[blank_simps] theorem fun_blank_namedView {V V' : Type} [Blanks V V'] :
    (blank : Grammar.Multiple.NamedValues V → Grammar.Multiple.NamedValues V') =
      fun v => Grammar.Multiple.NamedValues.Internal.new (blank v.toArray) := (rfl)
@[blank_simps] theorem fun_blank_matchCases {T T' : Type} [Blanks T T'] :
    (blank : Grammar.Multiple.MatchCases T → Grammar.Multiple.MatchCases T') =
      fun v => Grammar.Multiple.MatchCases.Internal.new (blank v.toArray) := (rfl)
@[blank_simps] theorem fun_blank_constructorsView {S S' : Type} [Blanks S S'] :
    (blank : Grammar.Multiple.Constructors S → Grammar.Multiple.Constructors S') =
      fun v => Grammar.Multiple.Constructors.Internal.new (blank v.toArray) := (rfl)
@[blank_simps] theorem fun_blank_functionSignaturesView {S S' : Type} [Blanks S S'] :
    (blank : Grammar.Multiple.FunctionSignatures S → Grammar.Multiple.FunctionSignatures S') =
      fun v => Grammar.Multiple.FunctionSignatures.Internal.new (blank v.toArray) := (rfl)
@[blank_simps] theorem fun_blankStep {σ σ' ρ ρ' : Type} [Blanks σ σ'] [Blanks ρ ρ'] :
    (blank : Internal.Step σ ρ → Internal.Step σ' ρ') = blankStep := (rfl)
@[blank_simps] theorem fun_blank_prod {α α' β β' : Type} [Blanks α α'] [Blanks β β'] :
    (blank : α × β → α' × β') = fun p => (blank p.1, blank p.2) := (rfl)
@[blank_simps] theorem fun_blank_array {α β : Type} [Blanks α β] :
    (blank : Array α → Array β) = Array.map blank := (rfl)
@[blank_simps] theorem fun_blank_list {α β : Type} [Blanks α β] :
    (blank : List α → List β) = List.map blank := (rfl)
@[blank_simps] theorem fun_blank_option {α β : Type} [Blanks α β] :
    (blank : Option α → Option β) = Option.map blank := (rfl)
@[blank_simps] theorem fun_blank_id {α : Type} :
    (@blank α α blanksId) = id := (rfl)

@[blank_simps] theorem blankListState_id {σ ρ : Type} (s : ListState σ ρ) :
    @blankListState σ σ ρ ρ blanksId blanksId s = s := by
  cases s; simp [blankListState, Blanks.blank]; try rfl

@[blank_simps] theorem blankListState_id_prod {σ α β : Type} (s : ListState σ (α × β)) :
    @blankListState σ σ (α × β) (α × β) blanksId (@instBlanksProd α α β β blanksId blanksId) s =
      s := by
  cases s; simp [blankListState, Blanks.blank]; try rfl

@[blank_simps] theorem isEmpty_map {α β : Type} (f : α → β) (a : Array α) :
    (a.map f).isEmpty = a.isEmpty := by simp [Array.isEmpty]

@[blank_simps] theorem isEmpty_push {α : Type} (a : Array α) (x : α) :
    (a.push x).isEmpty = false := by simp [Array.isEmpty]

@[blank_simps] theorem size_map {α β : Type} (f : α → β) (a : Array α) :
    (a.map f).size = a.size := Array.size_map ..

@[blank_simps] theorem getElem?_map {α β : Type} (f : α → β) (a : Array α) (i : Nat) :
    (a.map f)[i]? = a[i]?.map f := Array.getElem?_map ..

end

section

variable {H : Type} [Handler.CommandHandler H Id]

@[blank_simps] theorem posture_blankScriptParser (p : ScriptParser H) :
    ScriptParser.Internal.posture (blankScriptParser p) = ScriptParser.Internal.posture p :=
  ScriptParser.Internal.posture_mk ..
@[blank_simps] theorem command_blankScriptParser (p : ScriptParser H) :
    ScriptParser.Internal.command (blankScriptParser p) =
      blank (ScriptParser.Internal.command p) :=
  ScriptParser.Internal.command_mk ..
@[blank_simps] theorem declarations_blankScriptParser (p : ScriptParser H) :
    ScriptParser.Internal.declarations (blankScriptParser p) =
      ScriptParser.Internal.declarations p :=
  ScriptParser.Internal.declarations_mk ..
@[blank_simps] theorem fun_blankScriptParser :
    (blank : ScriptParser H → ScriptParser Shell) = blankScriptParser := (rfl)

@[blank_simps] theorem blank_sExpr (x : Handler.SExpr H) : blank x = () := (rfl)
@[blank_simps] theorem blank_attribute (x : Handler.Attribute H) : blank x = () := (rfl)
@[blank_simps] theorem blank_sort (x : Handler.«Sort» H) : blank x = () := (rfl)
@[blank_simps] theorem blank_term (x : Handler.Term H) : blank x = () := (rfl)
@[blank_simps] theorem blank_scope (x : Handler.Scope H) : blank x = () := (rfl)
@[blank_simps] theorem blank_sExpr' (x : Handler.SExpr H) :
    (blank x : Handler.SExpr Shell) = () := (rfl)
@[blank_simps] theorem blank_attribute' (x : Handler.Attribute H) :
    (blank x : Handler.Attribute Shell) = () := (rfl)
@[blank_simps] theorem blank_sort' (x : Handler.«Sort» H) :
    (blank x : Handler.«Sort» Shell) = () := (rfl)
@[blank_simps] theorem blank_term' (x : Handler.Term H) :
    (blank x : Handler.Term Shell) = () := (rfl)
@[blank_simps] theorem blank_scope' (x : Handler.Scope H) :
    (blank x : Handler.Scope Shell) = () := (rfl)

end

/-- The simp set of blanking, with the instances unfolded. -/
macro "blank_simp" : tactic => `(tactic| simp only [Blanks.blank, blank_simps])

end BSmtLib.Facts.Proofs.Parser.Blank.Simp

module

public import BSmtLib.Facts.Proofs.Parser.Blank.Basic
public import BSmtLib.Parser.Script
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
import all BSmtLib.Parser.Command
import all BSmtLib.Parser.Command.Internal.Datatype
import all BSmtLib.Parser.Command.Internal.Definition
import all BSmtLib.Parser.Command.Internal.Function
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# The parser's states with the handler's values blanked

`Blanks.blank` on the states of every parser the script parser is built from: each value of the
handler in a state is replaced by `()`, everything else is kept. A state that holds no value of
the handler is kept as it is (`blanksId`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Blank.States

open Basic

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
open BSmtLib.Parser.Category.Term BSmtLib.Parser.Command BSmtLib.Parser.Command.Internal.Datatype
open BSmtLib.Parser.Category.Term.Internal
open BSmtLib.Parser.Command.Internal
open BSmtLib.Parser.Command.Internal.Definition BSmtLib.Parser.Command.Internal.Function
open BSmtLib.Parser.Command.Internal.Standard BSmtLib.Parser.Script

variable {SE SE' A A' S S' T T' Sc Sc' : Type} [Blanks SE SE'] [Blanks A A'] [Blanks S S']
  [Blanks T T'] [Blanks Sc Sc']

/-! ## The categories -/

def blankAttributeMode : AttributeMode SE → AttributeMode SE'
  | .start => .start
  | .afterName keyword => .afterName keyword
  | .inside keyword items sExpr outside => .inside keyword (blank items) (blank sExpr) outside

instance : Blanks (AttributeMode SE) (AttributeMode SE') := ⟨blankAttributeMode⟩

def blankAttributeState : AttributeState SE A → AttributeState SE' A'
  | ⟨mode, attributes⟩ => ⟨blank mode, blank attributes⟩

instance : Blanks (AttributeState SE A) (AttributeState SE' A') := ⟨blankAttributeState⟩

def blankSortLevel : SortLevel S → SortLevel S'
  | ⟨head, arguments⟩ => ⟨head, blank arguments⟩

instance : Blanks (SortLevel S) (SortLevel S') := ⟨blankSortLevel⟩

def blankSortState : SortState S → SortState S'
  | ⟨mode, levels⟩ => ⟨mode, blank levels⟩

instance : Blanks (SortState S) (SortState S') := ⟨blankSortState⟩

def blankSortedVarState : SortedVarState S → SortedVarState S'
  | .start => .start
  | .opened => .opened
  | .sort symbol sort => .sort symbol (blank sort)
  | .close symbol sort => .close symbol (blank sort)

instance : Blanks (SortedVarState S) (SortedVarState S') := ⟨blankSortedVarState⟩

def blankQualIdentState : QualIdentState S → QualIdentState S'
  | .start => .start
  | .opened => .opened
  | .indexed ident => .indexed ident
  | .qualifiedIdent ident => .qualifiedIdent ident
  | .sort identifier sort => .sort identifier (blank sort)
  | .close identifier sort => .close identifier (blank sort)

instance : Blanks (QualIdentState S) (QualIdentState S') := ⟨blankQualIdentState⟩

def blankListState {σ σ' ρ ρ' : Type} [Blanks σ σ'] [Blanks ρ ρ'] :
    ListState σ ρ → ListState σ' ρ'
  | ⟨opened, outside, inner, items⟩ => ⟨opened, outside, blank inner, blank items⟩

instance {σ σ' ρ ρ' : Type} [Blanks σ σ'] [Blanks ρ ρ'] :
    Blanks (ListState σ ρ) (ListState σ' ρ') := ⟨blankListState⟩

def blankTermLevel : TermLevel S T Sc → TermLevel S' T' Sc'
  | .application function sort arguments => .application function (blank sort) (blank arguments)
  | .letBinding bindings symbol => .letBinding (blank bindings) symbol
  | .binder kind scope => .binder kind (blank scope)
  | .annotation => .annotation
  | .matchScrutinee => .matchScrutinee
  | .matchCase scrutinee cases pattern scope =>
    .matchCase (blank scrutinee) (blank cases) pattern (blank scope)

instance : Blanks (TermLevel S T Sc) (TermLevel S' T' Sc') := ⟨blankTermLevel⟩

def blankTermMode : TermMode SE A S T Sc → TermMode SE' A' S' T' Sc'
  | .start => .start
  | .opened => .opened
  | .qualIdent state => .qualIdent (blank state)
  | .applicationHead state => .applicationHead (blank state)
  | .letBindingsOpen => .letBindingsOpen
  | .letBindingOpen bindings => .letBindingOpen (blank bindings)
  | .letBindingSymbol bindings => .letBindingSymbol (blank bindings)
  | .letBindingClose bindings => .letBindingClose (blank bindings)
  | .sortedVars binder state => .sortedVars binder (blank state)
  | .binderClose kind scope body => .binderClose kind (blank scope) (blank body)
  | .matchCasesOpen scrutinee => .matchCasesOpen (blank scrutinee)
  | .matchCaseOpen scrutinee cases => .matchCaseOpen (blank scrutinee) (blank cases)
  | .matchPattern scrutinee cases state => .matchPattern (blank scrutinee) (blank cases) state
  | .matchCaseClose scrutinee cases pattern scope body =>
    .matchCaseClose (blank scrutinee) (blank cases) pattern (blank scope) (blank body)
  | .matchClose scrutinee cases => .matchClose (blank scrutinee) (blank cases)
  | .annotating term state => .annotating (blank term) (blank state)

instance : Blanks (TermMode SE A S T Sc) (TermMode SE' A' S' T' Sc') := ⟨blankTermMode⟩

def blankTermState : TermState SE A S T Sc → TermState SE' A' S' T' Sc'
  | ⟨mode, levels⟩ => ⟨blank mode, blank levels⟩

instance : Blanks (TermState SE A S T Sc) (TermState SE' A' S' T' Sc') := ⟨blankTermState⟩

/-! ## The commands -/

def blankConstructorState : ConstructorState S → ConstructorState S'
  | .start => .start
  | .opened => .opened
  | .selectors symbol state => .selectors symbol (blank state)

instance : Blanks (ConstructorState S) (ConstructorState S') := ⟨blankConstructorState⟩

def blankDatatypeState : DatatypeState S → DatatypeState S'
  | .start => .start
  | .kind => .kind
  | .parameters state => .parameters state
  | .constructorsOpen => .constructorsOpen
  | .constructors parametric state => .constructors parametric (blank state)
  | .close constructors => .close (blank constructors)

instance : Blanks (DatatypeState S) (DatatypeState S') := ⟨blankDatatypeState⟩

def blankDefinitionEnd : DefinitionEnd S → DefinitionEnd S'
  | .defineConst symbol sort => .defineConst symbol (blank sort)
  | .defineFun => .defineFun
  | .defineFunRec => .defineFunRec

instance : Blanks (DefinitionEnd S) (DefinitionEnd S') := ⟨blankDefinitionEnd⟩

def blankSignatureState : SignatureState S → SignatureState S'
  | .start => .start
  | .parameters symbol state => .parameters symbol (blank state)
  | .result symbol parameters state => .result symbol (blank parameters) (blank state)

instance : Blanks (SignatureState S) (SignatureState S') := ⟨blankSignatureState⟩

def blankFunctionDecState : FunctionDecState S → FunctionDecState S'
  | .start => .start
  | .signature state => .signature (blank state)
  | .close signature => .close (blank signature)

instance : Blanks (FunctionDecState S) (FunctionDecState S') := ⟨blankFunctionDecState⟩

def blankLiteralState : LiteralState SE A S T Sc → LiteralState SE' A' S' T' Sc'
  | ⟨shape, term⟩ => ⟨shape, blank term⟩

instance : Blanks (LiteralState SE A S T Sc) (LiteralState SE' A' S' T' Sc') :=
  ⟨blankLiteralState⟩

def blankFinalCall : FinalCall A S T → FinalCall A' S' T'
  | .assert term => .assert (blank term)
  | .checkSat => .checkSat
  | .checkSatAssuming terms => .checkSatAssuming (blank terms)
  | .declareConst symbol sort => .declareConst symbol (blank sort)
  | .declareFun symbol parameters result => .declareFun symbol (blank parameters) (blank result)
  | .declareSort symbol arity => .declareSort symbol arity
  | .declareSortParameter symbol => .declareSortParameter symbol
  | .endDeclareDatatype constructors => .endDeclareDatatype (blank constructors)
  | .endDeclareDatatypes => .endDeclareDatatypes
  | .defineConst symbol sort body => .defineConst symbol (blank sort) (blank body)
  | .endDefineFun body => .endDefineFun (blank body)
  | .endDefineFunRec body => .endDefineFunRec (blank body)
  | .endDefineFunsRec => .endDefineFunsRec
  | .endDefineSort sort => .endDefineSort (blank sort)
  | .echo content => .echo content
  | .exit => .exit
  | .getAssertions => .getAssertions
  | .getAssignment => .getAssignment
  | .getInfo flag => .getInfo flag
  | .getModel => .getModel
  | .getOption keyword => .getOption keyword
  | .getProof => .getProof
  | .getUnsatAssumptions => .getUnsatAssumptions
  | .getUnsatCore => .getUnsatCore
  | .getValue terms => .getValue (blank terms)
  | .pop count => .pop count
  | .push count => .push count
  | .reset => .reset
  | .resetAssertions => .resetAssertions
  | .setLogic symbol => .setLogic symbol

instance [Blanks A A'] : Blanks (FinalCall A S T) (FinalCall A' S' T') := ⟨blankFinalCall⟩

def blankPayload : Payload SE A S T Sc → Payload SE' A' S' T' Sc'
  | .closing final => .closing (blank final)
  | .named command => .named command
  | .assert state => .assert (blank state)
  | .checkSatAssuming state => .checkSatAssuming (blank state)
  | .checkSatAssumingLiterals state => .checkSatAssumingLiterals (blank state)
  | .declareConst symbol state => .declareConst symbol (blank state)
  | .declareFunParameters symbol state => .declareFunParameters symbol (blank state)
  | .declareFunResult symbol parameters state =>
    .declareFunResult symbol (blank parameters) (blank state)
  | .declareSort symbol => .declareSort symbol
  | .declareDatatype symbol state => .declareDatatype symbol (blank state)
  | .declareDatatypesSorts state => .declareDatatypesSorts state
  | .declareDatatypesDatatypes count state => .declareDatatypesDatatypes count (blank state)
  | .defineSortParameters symbol state => .defineSortParameters symbol state
  | .defineSortBody state => .defineSortBody (blank state)
  | .defineConstSort symbol state => .defineConstSort symbol (blank state)
  | .defineSignature definition state => .defineSignature (blank definition) (blank state)
  | .defineBody definition state => .defineBody (blank definition) (blank state)
  | .defineFunsRecDeclarations state => .defineFunsRecDeclarations (blank state)
  | .defineFunsRecBodies signatures state => .defineFunsRecBodies (blank signatures) (blank state)
  | .echo => .echo
  | .getInfo => .getInfo
  | .getOption => .getOption
  | .getValue state => .getValue (blank state)
  | .pop => .pop
  | .push => .push
  | .setInfo declaration state => .setInfo declaration (blank state)
  | .setOption state => .setOption (blank state)

instance : Blanks (Payload SE A S T Sc) (Payload SE' A' S' T' Sc') := ⟨blankPayload⟩

/-- The command parser's state blanked. The handler names no parser of non-standard commands
when its calls never fail (`NoFails`), so the state in such a payload never arises; it is blanked
to `awaiting`, the blank handler's parser of non-standard commands being of the empty type. -/
def blankCommandState {N : Type} : CommandState SE A S T Sc N → CommandState SE' A' S' T' Sc' Empty
  | .awaiting => .awaiting
  | .opened => .opened
  | .payload state => .payload (blank state)
  | .nonstandard _ => .awaiting

instance {N : Type} : Blanks (CommandState SE A S T Sc N) (CommandState SE' A' S' T' Sc' Empty) :=
  ⟨blankCommandState⟩

/-! ## The script parser -/

section

variable {H : Type} [CommandHandler H Id]

/-- The script parser with the handler's values in its state blanked, over the blank
handler. -/
def blankScriptParser (parser : ScriptParser H) : ScriptParser Shell :=
  ScriptParser.Internal.mk (ScriptParser.Internal.posture parser)
    (blank (ScriptParser.Internal.command parser)) (ScriptParser.Internal.declarations parser)

instance : Blanks (ScriptParser H) (ScriptParser Shell) := ⟨blankScriptParser⟩

end

end BSmtLib.Facts.Proofs.Parser.Blank.States

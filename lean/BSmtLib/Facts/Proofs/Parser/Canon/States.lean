module

public import BSmtLib.Facts.Proofs.Parser.Canon.Basic
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
# The parser's states with their views replaced by their contents

`Canon.canon` on the states of every parser the script parser is built from: each view in a state
is replaced by the view of its content (`canonSlice`), everything else is kept.
-/

namespace BSmtLib.Facts.Proofs.Parser.Canon.States

open Basic

open BSmtLib.Parser BSmtLib.Grammar.Nodes BSmtLib.Handler
open BSmtLib.Lexicon.Value (Numeral StringContent Keyword)
open BSmtLib.Parser.Category.Attribute BSmtLib.Parser.Category.Combinator
open BSmtLib.Parser.Category.Ident BSmtLib.Parser.Category.Pattern
open BSmtLib.Parser.Category.QualifiedIdent BSmtLib.Parser.Category.SExpr
open BSmtLib.Parser.Category.«Sort» BSmtLib.Parser.Category.SortedVar
open BSmtLib.Parser.Category.Term BSmtLib.Parser.Command
open BSmtLib.Parser.Command.Internal.Datatype BSmtLib.Parser.Command.Internal.Definition
open BSmtLib.Parser.Command.Internal.Function BSmtLib.Parser.Command.Internal.Standard
open BSmtLib.Parser.Script
open BSmtLib.Parser.Category.Attribute.Internal
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Parser.Category.Ident.Internal
open BSmtLib.Parser.Category.Pattern.Internal
open BSmtLib.Parser.Category.QualifiedIdent.Internal
open BSmtLib.Parser.Category.SExpr.Internal
open BSmtLib.Parser.Category.«Sort».Internal
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.Term.Internal
open BSmtLib.Parser.Command.Internal
open BSmtLibSpec.Parser.Properties (Event)

variable {SE A S T Sc : Type} [Canon SE] [Canon A] [Canon S] [Canon T] [Canon Sc]

/-! ## The values of the recording handler -/

instance : Canon (Handler.SExpr (List Event)) := inferInstanceAs (Canon Nat)
instance : Canon (Handler.Attribute (List Event)) := inferInstanceAs (Canon Nat)
instance : Canon (Handler.«Sort» (List Event)) := inferInstanceAs (Canon Nat)
instance : Canon (Handler.Term (List Event)) := inferInstanceAs (Canon Nat)
instance : Canon (Handler.Scope (List Event)) := inferInstanceAs (Canon Nat)
instance : CanonId (Handler.SExpr (List Event)) := inferInstanceAs (CanonId Nat)
instance : CanonId (Handler.Attribute (List Event)) := inferInstanceAs (CanonId Nat)
instance : CanonId (Handler.«Sort» (List Event)) := inferInstanceAs (CanonId Nat)
instance : CanonId (Handler.Term (List Event)) := inferInstanceAs (CanonId Nat)
instance : CanonId (Handler.Scope (List Event)) := inferInstanceAs (CanonId Nat)

/-- The recording handler's s-expressions. -/
abbrev RSExpr := Handler.SExpr (List Event)
/-- The recording handler's attributes. -/
abbrev RAttribute := Handler.Attribute (List Event)
/-- The recording handler's sorts. -/
abbrev RSort := Handler.«Sort» (List Event)
/-- The recording handler's terms. -/
abbrev RTerm := Handler.Term (List Event)
/-- The recording handler's scopes. -/
abbrev RScope := Handler.Scope (List Event)

/-! ## The categories -/

def canonIdentState : IdentState → IdentState
  | .indices symbol indices => .indices (canon symbol) (canon indices)
  | .start => .start
  | .opened => .opened
  | .afterUnderscore => .afterUnderscore

instance : Canon IdentState := ⟨canonIdentState⟩

def canonAttributeMode : AttributeMode SE → AttributeMode SE
  | .start => .start
  | .afterName keyword => .afterName (canon keyword)
  | .inside keyword items sExpr outside =>
    .inside (canon keyword) (canon items) (canon sExpr) outside

instance : Canon (AttributeMode SE) := ⟨canonAttributeMode⟩

def canonAttributeState : AttributeState SE A → AttributeState SE A
  | ⟨mode, attributes⟩ => ⟨canon mode, canon attributes⟩

instance : Canon (AttributeState SE A) := ⟨canonAttributeState⟩

def canonSortMode : SortMode → SortMode
  | .identOnly ident => .identOnly (canon ident)
  | .startingIdent ident => .startingIdent (canon ident)
  | .start => .start
  | .opened => .opened

instance : Canon SortMode := ⟨canonSortMode⟩

def canonSortLevel : SortLevel S → SortLevel S
  | ⟨head, arguments⟩ => ⟨canon head, canon arguments⟩

instance : Canon (SortLevel S) := ⟨canonSortLevel⟩

def canonSortState : SortState S → SortState S
  | ⟨mode, levels⟩ => ⟨canon mode, canon levels⟩

instance : Canon (SortState S) := ⟨canonSortState⟩

def canonSortedVarState : SortedVarState S → SortedVarState S
  | .start => .start
  | .opened => .opened
  | .sort symbol sort => .sort (canon symbol) (canon sort)
  | .close symbol sort => .close (canon symbol) (canon sort)

instance : Canon (SortedVarState S) := ⟨canonSortedVarState⟩

def canonQualIdentState : QualIdentState S → QualIdentState S
  | .start => .start
  | .opened => .opened
  | .indexed ident => .indexed (canon ident)
  | .qualifiedIdent ident => .qualifiedIdent (canon ident)
  | .sort identifier sort => .sort (canon identifier) (canon sort)
  | .close identifier sort => .close (canon identifier) (canon sort)

instance : Canon (QualIdentState S) := ⟨canonQualIdentState⟩

def canonPatternState : PatternState → PatternState
  | .arguments constructor arguments => .arguments (canon constructor) (canon arguments)
  | .start => .start
  | .opened => .opened

instance : Canon PatternState := ⟨canonPatternState⟩

def canonListState {σ ρ : Type} [Canon σ] [Canon ρ] : ListState σ ρ → ListState σ ρ
  | ⟨opened, outside, inner, items⟩ => ⟨opened, outside, canon inner, canon items⟩

instance {σ ρ : Type} [Canon σ] [Canon ρ] : Canon (ListState σ ρ) := ⟨canonListState⟩

instance : Canon SortedBinder := ⟨id⟩
instance : Canon BinderKind := ⟨id⟩

def canonTermLevel : TermLevel S T Sc → TermLevel S T Sc
  | .application function sort arguments =>
    .application (canon function) (canon sort) (canon arguments)
  | .letBinding bindings symbol => .letBinding (canon bindings) (canon symbol)
  | .binder kind scope => .binder kind (canon scope)
  | .annotation => .annotation
  | .matchScrutinee => .matchScrutinee
  | .matchCase scrutinee cases pattern scope =>
    .matchCase (canon scrutinee) (canon cases) (canon pattern) (canon scope)

instance : Canon (TermLevel S T Sc) := ⟨canonTermLevel⟩

def canonTermMode : TermMode SE A S T Sc → TermMode SE A S T Sc
  | .start => .start
  | .opened => .opened
  | .qualIdent state => .qualIdent (canon state)
  | .applicationHead state => .applicationHead (canon state)
  | .letBindingsOpen => .letBindingsOpen
  | .letBindingOpen bindings => .letBindingOpen (canon bindings)
  | .letBindingSymbol bindings => .letBindingSymbol (canon bindings)
  | .letBindingClose bindings => .letBindingClose (canon bindings)
  | .sortedVars binder state => .sortedVars binder (canon state)
  | .binderClose kind scope body => .binderClose kind (canon scope) (canon body)
  | .matchCasesOpen scrutinee => .matchCasesOpen (canon scrutinee)
  | .matchCaseOpen scrutinee cases => .matchCaseOpen (canon scrutinee) (canon cases)
  | .matchPattern scrutinee cases state =>
    .matchPattern (canon scrutinee) (canon cases) (canon state)
  | .matchCaseClose scrutinee cases pattern scope body =>
    .matchCaseClose (canon scrutinee) (canon cases) (canon pattern) (canon scope) (canon body)
  | .matchClose scrutinee cases => .matchClose (canon scrutinee) (canon cases)
  | .annotating term state => .annotating (canon term) (canon state)

instance : Canon (TermMode SE A S T Sc) := ⟨canonTermMode⟩

def canonTermState : TermState SE A S T Sc → TermState SE A S T Sc
  | ⟨mode, levels⟩ => ⟨canon mode, canon levels⟩

instance : Canon (TermState SE A S T Sc) := ⟨canonTermState⟩

/-! ## The commands -/

def canonSortDecState : SortDecState → SortDecState
  | .arity symbol => .arity (canon symbol)
  | .close symbol arity => .close (canon symbol) (canon arity)
  | .start => .start
  | .opened => .opened

instance : Canon SortDecState := ⟨canonSortDecState⟩

def canonSignature (s : Grammar.Multiple.FunctionSignature S) : Grammar.Multiple.FunctionSignature S :=
  Grammar.Multiple.FunctionSignature.Internal.new (canon s.name) (canon s.params) (canon s.resultSort)

instance : Canon (Grammar.Multiple.FunctionSignature S) := ⟨canonSignature⟩

instance : Canon (Grammar.Multiple.FunctionSignatures S) :=
  ⟨fun v => Grammar.Multiple.FunctionSignatures.Internal.new (canon v.toArray)⟩

def canonConstructorState : ConstructorState S → ConstructorState S
  | .start => .start
  | .opened => .opened
  | .selectors symbol state => .selectors (canon symbol) (canon state)

instance : Canon (ConstructorState S) := ⟨canonConstructorState⟩

def canonDatatypeState : DatatypeState S → DatatypeState S
  | .start => .start
  | .kind => .kind
  | .parameters state => .parameters (canon state)
  | .constructorsOpen => .constructorsOpen
  | .constructors parametric state => .constructors parametric (canon state)
  | .close constructors => .close (canon constructors)

instance : Canon (DatatypeState S) := ⟨canonDatatypeState⟩

def canonDefinitionEnd : DefinitionEnd S → DefinitionEnd S
  | .defineConst symbol sort => .defineConst (canon symbol) (canon sort)
  | .defineFun => .defineFun
  | .defineFunRec => .defineFunRec

instance : Canon (DefinitionEnd S) := ⟨canonDefinitionEnd⟩

def canonSignatureState : SignatureState S → SignatureState S
  | .start => .start
  | .parameters symbol state => .parameters (canon symbol) (canon state)
  | .result symbol parameters state => .result (canon symbol) (canon parameters) (canon state)

instance : Canon (SignatureState S) := ⟨canonSignatureState⟩

def canonFunctionDecState : FunctionDecState S → FunctionDecState S
  | .start => .start
  | .signature state => .signature (canon state)
  | .close signature => .close (canon signature)

instance : Canon (FunctionDecState S) := ⟨canonFunctionDecState⟩

instance : Canon LiteralShape := ⟨id⟩

def canonLiteralState : LiteralState SE A S T Sc → LiteralState SE A S T Sc
  | ⟨shape, term⟩ => ⟨shape, canon term⟩

instance : Canon (LiteralState SE A S T Sc) := ⟨canonLiteralState⟩

def canonFinalCall : FinalCall A S T → FinalCall A S T
  | .assert term => .assert (canon term)
  | .checkSat => .checkSat
  | .checkSatAssuming terms => .checkSatAssuming (canon terms)
  | .declareConst symbol sort => .declareConst (canon symbol) (canon sort)
  | .declareFun symbol parameters result =>
    .declareFun (canon symbol) (canon parameters) (canon result)
  | .declareSort symbol arity => .declareSort (canon symbol) (canon arity)
  | .declareSortParameter symbol => .declareSortParameter (canon symbol)
  | .endDeclareDatatype constructors => .endDeclareDatatype (canon constructors)
  | .endDeclareDatatypes => .endDeclareDatatypes
  | .defineConst symbol sort body => .defineConst (canon symbol) (canon sort) (canon body)
  | .endDefineFun body => .endDefineFun (canon body)
  | .endDefineFunRec body => .endDefineFunRec (canon body)
  | .endDefineFunsRec => .endDefineFunsRec
  | .endDefineSort sort => .endDefineSort (canon sort)
  | .echo content => .echo (canon content)
  | .exit => .exit
  | .getAssertions => .getAssertions
  | .getAssignment => .getAssignment
  | .getInfo flag => .getInfo (canon flag)
  | .getModel => .getModel
  | .getOption keyword => .getOption (canon keyword)
  | .getProof => .getProof
  | .getUnsatAssumptions => .getUnsatAssumptions
  | .getUnsatCore => .getUnsatCore
  | .getValue terms => .getValue (canon terms)
  | .pop count => .pop (canon count)
  | .push count => .push (canon count)
  | .reset => .reset
  | .resetAssertions => .resetAssertions
  | .setLogic symbol => .setLogic (canon symbol)

instance : Canon (FinalCall A S T) := ⟨canonFinalCall⟩

instance : Canon NamedCommand := ⟨id⟩
instance : Canon Declaration := ⟨id⟩

def canonPayload : Payload SE A S T Sc → Payload SE A S T Sc
  | .closing final => .closing (canon final)
  | .named command => .named command
  | .assert state => .assert (canon state)
  | .checkSatAssuming state => .checkSatAssuming (canon state)
  | .checkSatAssumingLiterals state => .checkSatAssumingLiterals (canon state)
  | .declareConst symbol state => .declareConst (canon symbol) (canon state)
  | .declareFunParameters symbol state => .declareFunParameters (canon symbol) (canon state)
  | .declareFunResult symbol parameters state =>
    .declareFunResult (canon symbol) (canon parameters) (canon state)
  | .declareSort symbol => .declareSort (canon symbol)
  | .declareDatatype symbol state => .declareDatatype (canon symbol) (canon state)
  | .declareDatatypesSorts state => .declareDatatypesSorts (canon state)
  | .declareDatatypesDatatypes count state => .declareDatatypesDatatypes count (canon state)
  | .defineSortParameters symbol state => .defineSortParameters (canon symbol) (canon state)
  | .defineSortBody state => .defineSortBody (canon state)
  | .defineConstSort symbol state => .defineConstSort (canon symbol) (canon state)
  | .defineSignature definition state => .defineSignature (canon definition) (canon state)
  | .defineBody definition state => .defineBody (canon definition) (canon state)
  | .defineFunsRecDeclarations state => .defineFunsRecDeclarations (canon state)
  | .defineFunsRecBodies signatures state => .defineFunsRecBodies (canon signatures) (canon state)
  | .echo => .echo
  | .getInfo => .getInfo
  | .getOption => .getOption
  | .getValue state => .getValue (canon state)
  | .pop => .pop
  | .push => .push
  | .setInfo declaration state => .setInfo declaration (canon state)
  | .setOption state => .setOption (canon state)

instance : Canon (Payload SE A S T Sc) := ⟨canonPayload⟩

def canonCommandState {N : Type} : CommandState SE A S T Sc N → CommandState SE A S T Sc N
  | .awaiting => .awaiting
  | .opened => .opened
  | .payload state => .payload (canon state)
  | .nonstandard parser => .nonstandard parser

instance {N : Type} : Canon (CommandState SE A S T Sc N) := ⟨canonCommandState⟩

instance : Canon CommandOutcome := ⟨id⟩

instance : Canon (CommandStateOf (List Event)) :=
  inferInstanceAs (Canon (CommandState Nat Nat Nat Nat Nat Empty))

/-- The script parser over the recording handler, with the views in its state replaced. -/
def canonScriptParser (parser : ScriptParser (List Event)) : ScriptParser (List Event) :=
  ScriptParser.Internal.mk (ScriptParser.Internal.posture parser)
    (canon (ScriptParser.Internal.command parser)) (ScriptParser.Internal.declarations parser)

instance : Canon (ScriptParser (List Event)) := ⟨canonScriptParser⟩

end BSmtLib.Facts.Proofs.Parser.Canon.States

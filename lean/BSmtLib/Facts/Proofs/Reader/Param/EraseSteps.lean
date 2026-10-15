module

public import BSmtLib.Facts.Proofs.Reader.Param.Erase
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
import all BSmtLib.Parser.Command
import all BSmtLib.Parser.Command.Datatype
import all BSmtLib.Parser.Command.Function
import all BSmtLib.Parser.Command.Standard
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# Each step of the parser reads the log only by its calls

The closure of `Erasing` under the operations the steps are built from, applied to each step
function by the tactic `erasing_step`: unfold the step, then take its binds, matches, conditions,
handler calls and results apart.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.EraseSteps

open BSmtLibSpec.Parser.Properties
open BSmtLib.Parser
open BSmtLib.Facts.Proofs.Parser.Quiet
open BSmtLib.Facts.Proofs.Reader.Param.Erase BSmtLib.Nodes BSmtLib.Parser.Category.Attribute
open BSmtLib.Parser.Category.Combinator BSmtLib.Parser.Category.Ident
open BSmtLib.Parser.Category.Pattern BSmtLib.Parser.Category.QualifiedIdent
open BSmtLib.Parser.Category.SExpr BSmtLib.Parser.Category.«Sort» BSmtLib.Parser.Category.SortedVar
open BSmtLib.Parser.Category.Term BSmtLib.Parser.Category.Token BSmtLib.Parser.Command
open BSmtLib.Parser.Command.Datatype BSmtLib.Parser.Command.Function BSmtLib.Parser.Command.Standard
open BSmtLib.Parser.Script BSmtLib.Traits

theorem expectOpen_erases (token : Parser.Internal.Input) : Erases (expectOpen
    (H := List Event) token) := by
  unfold expectOpen
  split <;> first | exact Erasing.pure trivial | exact Erasing.throw _

theorem expectClose_erases (token : Parser.Internal.Input) : Erases (expectClose
    (H := List Event) token) := by
  unfold expectClose
  split <;> first | exact Erasing.pure trivial | exact Erasing.throw _

theorem expectSymbol_erases (token : Parser.Internal.Input) : Erases (expectSymbol
    (H := List Event) token) := by
  unfold expectSymbol
  split <;> first | exact Erasing.pure trivial | exact Erasing.throw _

theorem expectNumeral_erases (token : Parser.Internal.Input) :
    Erases (expectNumeral (H := List Event) token) := by
  unfold expectNumeral
  split <;> first | exact Erasing.pure trivial | exact Erasing.throw _

theorem expectKeyword_erases (token : Parser.Internal.Input) :
    Erases (expectKeyword (H := List Event) token) := by
  unfold expectKeyword
  split <;> first | exact Erasing.pure trivial | exact Erasing.throw _

theorem expectString_erases (token : Parser.Internal.Input) : Erases (expectString
    (H := List Event) token) := by
  unfold expectString
  split <;> first | exact Erasing.pure trivial | exact Erasing.throw _

/-- Takes an action apart into the closure lemmas of `Erasing`. -/
macro "erasing_step" "[" ts:Lean.Parser.Tactic.SolveByElim.arg,* "]" : tactic => `(tactic|
  repeat' (first
    | (intro)
    | (exact Erasing.pure trivial)
    | (exact Erasing.throw _)
    | (apply Erasing.bind_erases)
    | (apply erases_call)
    | (solve_by_elim only [$ts,*])
    | (solve_by_elim only [expectOpen_erases, expectClose_erases, expectSymbol_erases,
        expectNumeral_erases, expectKeyword_erases, expectString_erases])
    | split))

theorem identStep_erases (version : Token.Version) (state : IdentState)
    (token : Parser.Internal.Input) :
    Erases (IdentState.step (H := List Event) version state token) := by
  unfold IdentState.step
  erasing_step []

theorem sortComplete_erases (levels : List (SortLevel Nat)) (head : Identifier)
    (arguments : Array Nat) :
    Erases (sortComplete (H := List Event) levels head arguments) := by
  unfold sortComplete
  erasing_step []

theorem sortStep_erases (version : Token.Version) (state : SortState Nat)
    (token : Parser.Internal.Input) :
    Erases (sortStep (H := List Event) version state token) := by
  unfold sortStep
  erasing_step [identStep_erases]
theorem sExprStep_erases (version : Token.Version) (state : SExprState Nat)
    (token : Parser.Internal.Input) :
    Erases (sExprStep (H := List Event) version state token) := by
  unfold sExprStep
  try dsimp only
  erasing_step []

theorem attributeStep_erases (single : Bool) (version : Token.Version)
    (state : AttributeState Nat Nat) (token : Parser.Internal.Input) :
    Erases (attributeStep (H := List Event) single version state token) := by
  unfold attributeStep
  try dsimp only
  erasing_step [sExprStep_erases, expectClose_erases]

theorem patternStep_erases (version : Token.Version) (state : PatternState)
    (token : Parser.Internal.Input) :
    Erases (PatternState.step (H := List Event) version state token) := by
  unfold PatternState.step
  try dsimp only
  erasing_step []

theorem qualIdentStep_erases (version : Token.Version) (state : QualIdentState Nat)
    (token : Parser.Internal.Input) :
    Erases (qualIdentStep (H := List Event) version state token) := by
  unfold qualIdentStep
  try dsimp only
  erasing_step [identStep_erases, sortStep_erases]

theorem sortedVarStep_erases (version : Token.Version) (state : SortedVarState Nat)
    (token : Parser.Internal.Input) :
    Erases (sortedVarStep (H := List Event) version state token) := by
  unfold sortedVarStep expectOpen expectSymbol expectClose
  try dsimp only
  erasing_step [sortStep_erases]

theorem listStep_erases {σ ρ : Type} (init : σ) {inner : σ → Parser.Internal.Input → RPM
    (Parser.Internal.Step σ ρ)}
    (hinner : ∀ state token, Erases (inner state token)) (maximum : Option Nat)
    (state : ListState σ ρ) (token : Parser.Internal.Input) :
    Erases (ListState.step init inner maximum state token) := by
  unfold ListState.step expectOpen
  try dsimp only
  erasing_step [hinner]

theorem termComplete_erases (levels : List (TermLevel Nat Nat Nat)) (term : Nat) :
    Erases (termComplete (H := List Event) levels term) := by
  unfold termComplete
  try dsimp only
  erasing_step []

theorem startBinder_erases (binder : SortedBinder) (variables : Array (Nodes.Symbol × Nat)) :
    Erases (startBinder (H := List Event) binder variables) := by
  unfold startBinder
  try dsimp only
  erasing_step []

theorem endBinder_erases (kind : BinderKind) (scope term : Nat) :
    Erases (endBinder (H := List Event) kind scope term) := by
  unfold endBinder
  try dsimp only
  erasing_step []

theorem termOpened_erases (state : TermState Nat Nat Nat Nat Nat) (token : Parser.Internal.Input) :
    Erases (termOpened (H := List Event) state token) := by
  unfold termOpened
  try dsimp only
  erasing_step []

theorem termStep_erases (version : Token.Version) (state : TermState Nat Nat Nat Nat Nat)
    (token : Parser.Internal.Input) : Erases (termStep (H := List Event) version state token) := by
  have hvars := listStep_erases (SortedVarState.start (HandledSort := Nat))
    (sortedVarStep_erases version) none
  unfold termStep expectOpen expectSymbol expectClose
  try dsimp only
  erasing_step [qualIdentStep_erases, hvars, patternStep_erases, attributeStep_erases,
    termComplete_erases, startBinder_erases, endBinder_erases, termOpened_erases]
theorem symbolStep_erases (state : Unit) (token : Parser.Internal.Input) :
    Erases (symbolStep (H := List Event) state token) := by
  unfold symbolStep
  try dsimp only
  erasing_step []

theorem sortDecStep_erases (state : SortDecState) (token : Parser.Internal.Input) :
    Erases (SortDecState.step (H := List Event) state token) := by
  unfold SortDecState.step
  try dsimp only
  erasing_step []

set_option maxHeartbeats 4000000 in
theorem literalStep_erases (version : Token.Version) (state : LiteralState Nat Nat Nat Nat Nat)
    (token : Parser.Internal.Input) : Erases (literalStep
        (H := List Event) version state token) := by
  unfold literalStep
  try dsimp only
  erasing_step [termStep_erases]

theorem signatureStep_erases (version : Token.Version) (state : SignatureState Nat)
    (token : Parser.Internal.Input) :
    Erases (signatureStep (H := List Event) version state token) := by
  have hvars := listStep_erases (SortedVarState.start (HandledSort := Nat))
    (sortedVarStep_erases version) none
  unfold signatureStep
  try dsimp only
  erasing_step [hvars, sortStep_erases]

theorem functionDecStep_erases (version : Token.Version) (state : FunctionDecState Nat)
    (token : Parser.Internal.Input) :
    Erases (functionDecStep (H := List Event) version state token) := by
  unfold functionDecStep
  try dsimp only
  erasing_step [signatureStep_erases]

theorem constructorStep_erases (version : Token.Version) (state : ConstructorState Nat)
    (token : Parser.Internal.Input) : Erases (constructorStep
        (H := List Event) version state token) := by
  have hvars := listStep_erases (SortedVarState.start (HandledSort := Nat))
    (sortedVarStep_erases version) none
  unfold constructorStep
  try dsimp only
  erasing_step [hvars]

theorem datatypeStep_erases {start : Array Nodes.Symbol → RPM Unit}
    (hstart : ∀ parameters, Erases (start parameters)) (version : Token.Version)
    (state : DatatypeState Nat) (token : Parser.Internal.Input) :
    Erases (datatypeStep (H := List Event) start version state token) := by
  have hsymbols := listStep_erases () symbolStep_erases none
  have hconstructors := listStep_erases (ConstructorState.start (HandledSort := Nat))
    (constructorStep_erases version) none
  unfold datatypeStep
  try dsimp only
  erasing_step [hstart, hsymbols, hconstructors]

theorem bodyStep_erases (version : Token.Version) (state : TermState Nat Nat Nat Nat Nat)
    (token : Parser.Internal.Input) : Erases (bodyStep (H := List Event) version state token) := by
  unfold bodyStep
  try dsimp only
  erasing_step [termStep_erases]

theorem bodiesStep_erases (count : Nat) (version : Token.Version)
    (state : ListState (TermState Nat Nat Nat Nat Nat) Unit) (token : Parser.Internal.Input) :
    Erases (bodiesStep (H := List Event) count version state token) := by
  have hbodies := listStep_erases (TermState.init (HandledSExpr := Nat) (HandledAttribute := Nat)
    (HandledSort := Nat) (HandledTerm := Nat) (Scope := Nat)) (bodyStep_erases version) (some count)
  unfold bodiesStep
  try dsimp only
  erasing_step [hbodies]

theorem finalCall_erases (final : FinalCall Nat Nat Nat) :
    Erases (finalCall (H := List Event) final) := by
  unfold finalCall
  try dsimp only
  erasing_step []

set_option maxHeartbeats 4000000 in
theorem payloadStep_erases (version : Token.Version) (state : Payload Nat Nat Nat Nat Nat)
    (token : Parser.Internal.Input) : Erases (payloadStep
        (H := List Event) version state token) := by
  have hterms := listStep_erases (TermState.init (HandledSExpr := Nat) (HandledAttribute := Nat)
    (HandledSort := Nat) (HandledTerm := Nat) (Scope := Nat)) (termStep_erases version) none
  have hliterals := listStep_erases (LiteralState.init (HandledSExpr := Nat)
    (HandledAttribute := Nat) (HandledSort := Nat) (HandledTerm := Nat) (Scope := Nat))
    (literalStep_erases version) none
  have hsorts := listStep_erases (SortState.init (HandledSort := Nat)) (sortStep_erases version)
    none
  have hsortDecs := listStep_erases SortDecState.start sortDecStep_erases none
  have hsymbols := listStep_erases () symbolStep_erases none
  have hfunctions := listStep_erases (FunctionDecState.start (HandledSort := Nat))
    (functionDecStep_erases version) none
  have hdatatypes : ∀ count (start : Array Nodes.Symbol → RPM Unit),
      (∀ parameters, Erases (start parameters)) →
      ∀ state token, Erases (ListState.step (DatatypeState.start (HandledSort := Nat))
        (fun state token => do
          match ← datatypeStep (H := List Event) start version state token with
          | .more state => return Parser.Internal.Step.more state
          | .done constructors =>
            Parser.call (CommandHandler.endDatatypeDeclaration constructors)
            return .done ()) (some count) state token) := by
    intro count start hstart state token
    apply listStep_erases
    intro state token
    erasing_step [datatypeStep_erases hstart]
  have hdeclare : ∀ symbol state token, Erases (datatypeStep (H := List Event)
      (fun parameters => Parser.call (CommandHandler.startDeclareDatatype symbol parameters))
      version state token) := fun symbol =>
    datatypeStep_erases (fun _ => by apply erases_call) version
  have hdeclarations := fun count => hdatatypes count
    (fun parameters => Parser.call (CommandHandler.startDatatypeDeclaration parameters))
    (fun _ => by apply erases_call)
  have hdeclareEach : ∀ state token, Erases (datatypeStep (H := List Event)
      (fun parameters => Parser.call (CommandHandler.startDatatypeDeclaration parameters))
      version state token) :=
    datatypeStep_erases (fun _ => by apply erases_call) version
  have hbodies := fun count => listStep_erases (TermState.init (HandledSExpr := Nat)
    (HandledAttribute := Nat) (HandledSort := Nat) (HandledTerm := Nat) (Scope := Nat))
    (bodyStep_erases version) (some count)
  unfold payloadStep
  try dsimp only
  erasing_step [hterms, hliterals, hsorts, hsortDecs, hsymbols, hfunctions, hdeclare,
    hdeclarations, hbodies,
    termStep_erases, sortStep_erases, signatureStep_erases, bodiesStep_erases,
    attributeStep_erases, finalCall_erases, datatypeStep_erases]
  all_goals
    apply listStep_erases
    intro state token
    erasing_step [hdeclareEach]

theorem commandStep_erases (version : Token.Version) (state : CommandState Nat Nat Nat Nat Nat)
    (token : Parser.Internal.Input) : Erases (commandStep
        (H := List Event) version state token) := by
  unfold commandStep
  try dsimp only
  erasing_step [payloadStep_erases]

/-- What a step of a parser asks of its driver, with the continuations `Erases`. -/
def FlowErases {σ ρ : Type} : Parser.Internal.Flow RPM σ ρ → Prop
  | .switchVersion _ resume => Erases resume
  | .discardRest resume => Erases resume
  | _ => True

theorem scriptArrive_erases (parser : ScriptParser (List Event)) (token : Parser.Internal.Input) :
    Erases (Parser.Internal.ParseByToken.arrive (H := List Event) parser token) := by
  show Erases (ScriptParser.arrive parser token)
  unfold ScriptParser.arrive commandArrive payloadArrive bodiesArrive
  erasing_step []

theorem scriptStep_erasing (version : Token.Version) (parser : ScriptParser (List Event))
    (token : Parser.Internal.Input) :
    Erasing FlowErases (Parser.Internal.ParseByToken.step
        (H := List Event) version parser token) := by
  show Erasing FlowErases (ScriptParser.step version parser token)
  unfold ScriptParser.step
  apply Erasing.bind_erases (commandStep_erases _ _ _)
  intro outcome
  split
  · exact Erasing.pure trivial
  · exact Erasing.pure trivial
  · split
    · exact Erasing.throw _
    · apply Erasing.pure
      show Erases _
      exact Erasing.bind_erases (erases_setVersion _) fun _ => Erasing.pure trivial
  · apply Erasing.pure
    show Erases _
    exact Erasing.pure trivial
  · exact Erasing.pure trivial

end BSmtLib.Facts.Proofs.Reader.Param.EraseSteps

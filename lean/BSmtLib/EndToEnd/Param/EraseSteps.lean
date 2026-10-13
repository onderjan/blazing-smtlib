import BSmtLib.EndToEnd.Param.Erase

/-!
# Each step of the parser reads the log only by its calls

The closure of `Erasing` under the operations the steps are built from, applied to each step
function by the tactic `erasing_step`: unfold the step, then take its binds, matches, conditions,
handler calls and results apart.
-/

namespace BSmtLib.EndToEnd.Param

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Parser
open BSmtLib.ParserProofs

theorem expectOpen_erases (token : Input) : Erases (expectOpen (H := List Event) token) := by
  unfold expectOpen
  split <;> first | exact Erasing.pure trivial | exact Erasing.throw _

theorem expectClose_erases (token : Input) : Erases (expectClose (H := List Event) token) := by
  unfold expectClose
  split <;> first | exact Erasing.pure trivial | exact Erasing.throw _

theorem expectSymbol_erases (token : Input) : Erases (expectSymbol (H := List Event) token) := by
  unfold expectSymbol
  split <;> first | exact Erasing.pure trivial | exact Erasing.throw _

theorem expectNumeral_erases (token : Input) :
    Erases (expectNumeral (H := List Event) token) := by
  unfold expectNumeral
  split <;> first | exact Erasing.pure trivial | exact Erasing.throw _

theorem expectKeyword_erases (token : Input) :
    Erases (expectKeyword (H := List Event) token) := by
  unfold expectKeyword
  split <;> first | exact Erasing.pure trivial | exact Erasing.throw _

theorem expectString_erases (token : Input) : Erases (expectString (H := List Event) token) := by
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

theorem identStep_erases (version : Version) (state : IdentState) (token : Input) :
    Erases (IdentState.step (H := List Event) version state token) := by
  unfold IdentState.step
  erasing_step []

theorem sortComplete_erases (levels : List (SortLevel Nat)) (head : Identifier)
    (arguments : Array Nat) :
    Erases (sortComplete (H := List Event) levels head arguments) := by
  unfold sortComplete
  erasing_step []

theorem sortStep_erases (version : Version) (state : SortState Nat) (token : Input) :
    Erases (sortStep (H := List Event) version state token) := by
  unfold sortStep
  erasing_step [identStep_erases]
theorem sExprStep_erases (version : Version) (state : SExprState Nat) (token : Input) :
    Erases (sExprStep (H := List Event) version state token) := by
  unfold sExprStep
  try dsimp only
  erasing_step []

theorem attributeStep_erases (single : Bool) (version : Version)
    (state : AttributeState Nat Nat) (token : Input) :
    Erases (attributeStep (H := List Event) single version state token) := by
  unfold attributeStep
  try dsimp only
  erasing_step [sExprStep_erases, expectClose_erases]

theorem patternStep_erases (version : Version) (state : PatternState) (token : Input) :
    Erases (PatternState.step (H := List Event) version state token) := by
  unfold PatternState.step
  try dsimp only
  erasing_step []

theorem qualIdentStep_erases (version : Version) (state : QualIdentState Nat) (token : Input) :
    Erases (qualIdentStep (H := List Event) version state token) := by
  unfold qualIdentStep
  try dsimp only
  erasing_step [identStep_erases, sortStep_erases]

theorem sortedVarStep_erases (version : Version) (state : SortedVarState Nat) (token : Input) :
    Erases (sortedVarStep (H := List Event) version state token) := by
  unfold sortedVarStep expectOpen expectSymbol expectClose
  try dsimp only
  erasing_step [sortStep_erases]

theorem listStep_erases {σ ρ : Type} (init : σ) {inner : σ → Input → RPM (Step σ ρ)}
    (hinner : ∀ state token, Erases (inner state token)) (maximum : Option Nat)
    (state : ListState σ ρ) (token : Input) :
    Erases (ListState.step init inner maximum state token) := by
  unfold ListState.step expectOpen
  try dsimp only
  erasing_step [hinner]

theorem termComplete_erases (levels : List (TermLevel Nat Nat Nat)) (term : Nat) :
    Erases (termComplete (H := List Event) levels term) := by
  unfold termComplete
  try dsimp only
  erasing_step []

theorem startBinder_erases (binder : SortedBinder) (variables : Array (Parser.Symbol × Nat)) :
    Erases (startBinder (H := List Event) binder variables) := by
  unfold startBinder
  try dsimp only
  erasing_step []

theorem endBinder_erases (kind : BinderKind) (scope term : Nat) :
    Erases (endBinder (H := List Event) kind scope term) := by
  unfold endBinder
  try dsimp only
  erasing_step []

theorem termOpened_erases (state : TermState Nat Nat Nat Nat Nat) (token : Input) :
    Erases (termOpened (H := List Event) state token) := by
  unfold termOpened
  try dsimp only
  erasing_step []

theorem termStep_erases (version : Version) (state : TermState Nat Nat Nat Nat Nat)
    (token : Input) : Erases (termStep (H := List Event) version state token) := by
  have hvars := listStep_erases (SortedVarState.start (HandledSort := Nat))
    (sortedVarStep_erases version) none
  unfold termStep expectOpen expectSymbol expectClose
  try dsimp only
  erasing_step [qualIdentStep_erases, hvars, patternStep_erases, attributeStep_erases,
    termComplete_erases, startBinder_erases, endBinder_erases, termOpened_erases]
theorem symbolStep_erases (state : Unit) (token : Input) :
    Erases (symbolStep (H := List Event) state token) := by
  unfold symbolStep
  try dsimp only
  erasing_step []

theorem sortDecStep_erases (state : SortDecState) (token : Input) :
    Erases (SortDecState.step (H := List Event) state token) := by
  unfold SortDecState.step
  try dsimp only
  erasing_step []

set_option maxHeartbeats 4000000 in
theorem literalStep_erases (version : Version) (state : LiteralState Nat Nat Nat Nat Nat)
    (token : Input) : Erases (literalStep (H := List Event) version state token) := by
  unfold literalStep
  try dsimp only
  erasing_step [termStep_erases]

theorem signatureStep_erases (version : Version) (state : SignatureState Nat) (token : Input) :
    Erases (signatureStep (H := List Event) version state token) := by
  have hvars := listStep_erases (SortedVarState.start (HandledSort := Nat))
    (sortedVarStep_erases version) none
  unfold signatureStep
  try dsimp only
  erasing_step [hvars, sortStep_erases]

theorem functionDecStep_erases (version : Version) (state : FunctionDecState Nat) (token : Input) :
    Erases (functionDecStep (H := List Event) version state token) := by
  unfold functionDecStep
  try dsimp only
  erasing_step [signatureStep_erases]

theorem constructorStep_erases (version : Version) (state : ConstructorState Nat)
    (token : Input) : Erases (constructorStep (H := List Event) version state token) := by
  have hvars := listStep_erases (SortedVarState.start (HandledSort := Nat))
    (sortedVarStep_erases version) none
  unfold constructorStep
  try dsimp only
  erasing_step [hvars]

theorem datatypeStep_erases {start : Array Parser.Symbol → RPM Unit}
    (hstart : ∀ parameters, Erases (start parameters)) (version : Version)
    (state : DatatypeState Nat) (token : Input) :
    Erases (datatypeStep (H := List Event) start version state token) := by
  have hsymbols := listStep_erases () symbolStep_erases none
  have hconstructors := listStep_erases (ConstructorState.start (HandledSort := Nat))
    (constructorStep_erases version) none
  unfold datatypeStep
  try dsimp only
  erasing_step [hstart, hsymbols, hconstructors]

theorem bodyStep_erases (version : Version) (state : TermState Nat Nat Nat Nat Nat)
    (token : Input) : Erases (bodyStep (H := List Event) version state token) := by
  unfold bodyStep
  try dsimp only
  erasing_step [termStep_erases]

theorem bodiesStep_erases (count : Nat) (version : Version)
    (state : ListState (TermState Nat Nat Nat Nat Nat) Unit) (token : Input) :
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
theorem payloadStep_erases (version : Version) (state : Payload Nat Nat Nat Nat Nat)
    (token : Input) : Erases (payloadStep (H := List Event) version state token) := by
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
  have hdatatypes : ∀ count (start : Array Parser.Symbol → RPM Unit),
      (∀ parameters, Erases (start parameters)) →
      ∀ state token, Erases (ListState.step (DatatypeState.start (HandledSort := Nat))
        (fun state token => do
          match ← datatypeStep (H := List Event) start version state token with
          | .more state => return Step.more state
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

theorem commandStep_erases (version : Version) (state : CommandState Nat Nat Nat Nat Nat)
    (token : Input) : Erases (commandStep (H := List Event) version state token) := by
  unfold commandStep
  try dsimp only
  erasing_step [payloadStep_erases]

/-- What a step of a parser asks of its driver, with the continuations `Erases`. -/
def FlowErases {σ ρ : Type} : Flow RPM σ ρ → Prop
  | .switchVersion _ resume => Erases resume
  | .discardRest resume => Erases resume
  | _ => True

theorem scriptArrive_erases (parser : ScriptParser (List Event)) (token : Input) :
    Erases (Parse.arrive (H := List Event) parser token) := by
  show Erases (ScriptParser.arrive parser token)
  unfold ScriptParser.arrive commandArrive payloadArrive bodiesArrive
  erasing_step []

theorem scriptStep_erasing (version : Version) (parser : ScriptParser (List Event))
    (token : Input) :
    Erasing FlowErases (Parse.step (H := List Event) version parser token) := by
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

end BSmtLib.EndToEnd.Param

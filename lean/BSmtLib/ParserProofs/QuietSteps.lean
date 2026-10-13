import BSmtLib.ParserProofs.Quiet

/-!
# Each step of the parser is silent in a recording run

The closure of `Quiet` under the operations the steps are built from, applied to each step
function by the tactic `silent_step`: unfold the step, then take its binds, matches, conditions,
handler calls and results apart.
-/

namespace BSmtLib.ParserProofs

open BSmtLib.Spec.Parser
open BSmtLib.Spec.Parser.Traversal
open BSmtLib.Parser

theorem expectOpen_silent (token : Input) : Silent (expectOpen (H := List Event) token) := by
  unfold expectOpen
  split <;> first | exact Quiet.pure trivial | exact Quiet.throw _

theorem expectClose_silent (token : Input) : Silent (expectClose (H := List Event) token) := by
  unfold expectClose
  split <;> first | exact Quiet.pure trivial | exact Quiet.throw _

theorem expectSymbol_silent (token : Input) : Silent (expectSymbol (H := List Event) token) := by
  unfold expectSymbol
  split <;> first | exact Quiet.pure trivial | exact Quiet.throw _

theorem expectNumeral_silent (token : Input) :
    Silent (expectNumeral (H := List Event) token) := by
  unfold expectNumeral
  split <;> first | exact Quiet.pure trivial | exact Quiet.throw _

theorem expectKeyword_silent (token : Input) :
    Silent (expectKeyword (H := List Event) token) := by
  unfold expectKeyword
  split <;> first | exact Quiet.pure trivial | exact Quiet.throw _

theorem expectString_silent (token : Input) : Silent (expectString (H := List Event) token) := by
  unfold expectString
  split <;> first | exact Quiet.pure trivial | exact Quiet.throw _

/-- Takes a silent action apart into the closure lemmas. -/
macro "silent_step" "[" ts:Lean.Parser.Tactic.SolveByElim.arg,* "]" : tactic => `(tactic|
  repeat' (first
    | (intro)
    | (exact Quiet.pure trivial)
    | (exact Quiet.throw _)
    | (apply Quiet.bind_silent)
    | (apply silent_call)
    | (solve_by_elim only [$ts,*])
    | (solve_by_elim only [expectOpen_silent, expectClose_silent, expectSymbol_silent,
        expectNumeral_silent, expectKeyword_silent, expectString_silent])
    | split))

theorem identStep_silent (version : Version) (state : IdentState) (token : Input) :
    Silent (IdentState.step (H := List Event) version state token) := by
  unfold IdentState.step
  silent_step []

theorem sortComplete_silent (levels : List (SortLevel Nat)) (head : Identifier)
    (arguments : Array Nat) :
    Silent (sortComplete (H := List Event) levels head arguments) := by
  unfold sortComplete
  silent_step []

theorem sortStep_silent (version : Version) (state : SortState Nat) (token : Input) :
    Silent (sortStep (H := List Event) version state token) := by
  unfold sortStep
  silent_step [identStep_silent]
theorem sExprStep_silent (version : Version) (state : SExprState Nat) (token : Input) :
    Silent (sExprStep (H := List Event) version state token) := by
  unfold sExprStep
  try dsimp only
  silent_step []

theorem attributeStep_silent (single : Bool) (version : Version)
    (state : AttributeState Nat Nat) (token : Input) :
    Silent (attributeStep (H := List Event) single version state token) := by
  unfold attributeStep
  try dsimp only
  silent_step [sExprStep_silent, expectClose_silent]

theorem patternStep_silent (version : Version) (state : PatternState) (token : Input) :
    Silent (PatternState.step (H := List Event) version state token) := by
  unfold PatternState.step
  try dsimp only
  silent_step []

theorem qualIdentStep_silent (version : Version) (state : QualIdentState Nat) (token : Input) :
    Silent (qualIdentStep (H := List Event) version state token) := by
  unfold qualIdentStep
  try dsimp only
  silent_step [identStep_silent, sortStep_silent]

theorem sortedVarStep_silent (version : Version) (state : SortedVarState Nat) (token : Input) :
    Silent (sortedVarStep (H := List Event) version state token) := by
  unfold sortedVarStep expectOpen expectSymbol expectClose
  try dsimp only
  silent_step [sortStep_silent]

theorem listStep_silent {σ ρ : Type} (init : σ) {inner : σ → Input → RPM (Step σ ρ)}
    (hinner : ∀ state token, Silent (inner state token)) (maximum : Option Nat)
    (state : ListState σ ρ) (token : Input) :
    Silent (ListState.step init inner maximum state token) := by
  unfold ListState.step expectOpen
  try dsimp only
  silent_step [hinner]

theorem termComplete_silent (levels : List (TermLevel Nat Nat Nat)) (term : Nat) :
    Silent (termComplete (H := List Event) levels term) := by
  unfold termComplete
  try dsimp only
  silent_step []

theorem startBinder_silent (binder : SortedBinder) (variables : Array (Parser.Symbol × Nat)) :
    Silent (startBinder (H := List Event) binder variables) := by
  unfold startBinder
  try dsimp only
  silent_step []

theorem endBinder_silent (kind : BinderKind) (scope term : Nat) :
    Silent (endBinder (H := List Event) kind scope term) := by
  unfold endBinder
  try dsimp only
  silent_step []

theorem termOpened_silent (state : TermState Nat Nat Nat Nat Nat) (token : Input) :
    Silent (termOpened (H := List Event) state token) := by
  unfold termOpened
  try dsimp only
  silent_step []

theorem termStep_silent (version : Version) (state : TermState Nat Nat Nat Nat Nat)
    (token : Input) : Silent (termStep (H := List Event) version state token) := by
  have hvars := listStep_silent (SortedVarState.start (HandledSort := Nat))
    (sortedVarStep_silent version) none
  unfold termStep expectOpen expectSymbol expectClose
  try dsimp only
  silent_step [qualIdentStep_silent, hvars, patternStep_silent, attributeStep_silent,
    termComplete_silent, startBinder_silent, endBinder_silent, termOpened_silent]
theorem symbolStep_silent (state : Unit) (token : Input) :
    Silent (symbolStep (H := List Event) state token) := by
  unfold symbolStep
  try dsimp only
  silent_step []

theorem sortDecStep_silent (state : SortDecState) (token : Input) :
    Silent (SortDecState.step (H := List Event) state token) := by
  unfold SortDecState.step
  try dsimp only
  silent_step []

set_option maxHeartbeats 4000000 in
theorem literalStep_silent (version : Version) (state : LiteralState Nat Nat Nat Nat Nat)
    (token : Input) : Silent (literalStep (H := List Event) version state token) := by
  unfold literalStep
  try dsimp only
  silent_step [termStep_silent]

theorem signatureStep_silent (version : Version) (state : SignatureState Nat) (token : Input) :
    Silent (signatureStep (H := List Event) version state token) := by
  have hvars := listStep_silent (SortedVarState.start (HandledSort := Nat))
    (sortedVarStep_silent version) none
  unfold signatureStep
  try dsimp only
  silent_step [hvars, sortStep_silent]

theorem functionDecStep_silent (version : Version) (state : FunctionDecState Nat) (token : Input) :
    Silent (functionDecStep (H := List Event) version state token) := by
  unfold functionDecStep
  try dsimp only
  silent_step [signatureStep_silent]

theorem constructorStep_silent (version : Version) (state : ConstructorState Nat)
    (token : Input) : Silent (constructorStep (H := List Event) version state token) := by
  have hvars := listStep_silent (SortedVarState.start (HandledSort := Nat))
    (sortedVarStep_silent version) none
  unfold constructorStep
  try dsimp only
  silent_step [hvars]

theorem datatypeStep_silent {start : Array Parser.Symbol → RPM Unit}
    (hstart : ∀ parameters, Silent (start parameters)) (version : Version)
    (state : DatatypeState Nat) (token : Input) :
    Silent (datatypeStep (H := List Event) start version state token) := by
  have hsymbols := listStep_silent () symbolStep_silent none
  have hconstructors := listStep_silent (ConstructorState.start (HandledSort := Nat))
    (constructorStep_silent version) none
  unfold datatypeStep
  try dsimp only
  silent_step [hstart, hsymbols, hconstructors]

theorem bodyStep_silent (version : Version) (state : TermState Nat Nat Nat Nat Nat)
    (token : Input) : Silent (bodyStep (H := List Event) version state token) := by
  unfold bodyStep
  try dsimp only
  silent_step [termStep_silent]

theorem bodiesStep_silent (count : Nat) (version : Version)
    (state : ListState (TermState Nat Nat Nat Nat Nat) Unit) (token : Input) :
    Silent (bodiesStep (H := List Event) count version state token) := by
  have hbodies := listStep_silent (TermState.init (HandledSExpr := Nat) (HandledAttribute := Nat)
    (HandledSort := Nat) (HandledTerm := Nat) (Scope := Nat)) (bodyStep_silent version) (some count)
  unfold bodiesStep
  try dsimp only
  silent_step [hbodies]

theorem finalCall_silent (final : FinalCall Nat Nat Nat) :
    Silent (finalCall (H := List Event) final) := by
  unfold finalCall
  try dsimp only
  silent_step []

set_option maxHeartbeats 4000000 in
theorem payloadStep_silent (version : Version) (state : Payload Nat Nat Nat Nat Nat)
    (token : Input) : Silent (payloadStep (H := List Event) version state token) := by
  have hterms := listStep_silent (TermState.init (HandledSExpr := Nat) (HandledAttribute := Nat)
    (HandledSort := Nat) (HandledTerm := Nat) (Scope := Nat)) (termStep_silent version) none
  have hliterals := listStep_silent (LiteralState.init (HandledSExpr := Nat)
    (HandledAttribute := Nat) (HandledSort := Nat) (HandledTerm := Nat) (Scope := Nat))
    (literalStep_silent version) none
  have hsorts := listStep_silent (SortState.init (HandledSort := Nat)) (sortStep_silent version)
    none
  have hsortDecs := listStep_silent SortDecState.start sortDecStep_silent none
  have hsymbols := listStep_silent () symbolStep_silent none
  have hfunctions := listStep_silent (FunctionDecState.start (HandledSort := Nat))
    (functionDecStep_silent version) none
  have hdatatypes : ∀ count (start : Array Parser.Symbol → RPM Unit),
      (∀ parameters, Silent (start parameters)) →
      ∀ state token, Silent (ListState.step (DatatypeState.start (HandledSort := Nat))
        (fun state token => do
          match ← datatypeStep (H := List Event) start version state token with
          | .more state => return Step.more state
          | .done constructors =>
            Parser.call (CommandHandler.endDatatypeDeclaration constructors)
            return .done ()) (some count) state token) := by
    intro count start hstart state token
    apply listStep_silent
    intro state token
    silent_step [datatypeStep_silent hstart]
  have hdeclare : ∀ symbol state token, Silent (datatypeStep (H := List Event)
      (fun parameters => Parser.call (CommandHandler.startDeclareDatatype symbol parameters))
      version state token) := fun symbol =>
    datatypeStep_silent (fun _ => by apply silent_call) version
  have hdeclarations := fun count => hdatatypes count
    (fun parameters => Parser.call (CommandHandler.startDatatypeDeclaration parameters))
    (fun _ => by apply silent_call)
  have hdeclareEach : ∀ state token, Silent (datatypeStep (H := List Event)
      (fun parameters => Parser.call (CommandHandler.startDatatypeDeclaration parameters))
      version state token) :=
    datatypeStep_silent (fun _ => by apply silent_call) version
  have hbodies := fun count => listStep_silent (TermState.init (HandledSExpr := Nat)
    (HandledAttribute := Nat) (HandledSort := Nat) (HandledTerm := Nat) (Scope := Nat))
    (bodyStep_silent version) (some count)
  unfold payloadStep
  try dsimp only
  silent_step [hterms, hliterals, hsorts, hsortDecs, hsymbols, hfunctions, hdeclare,
    hdeclarations, hbodies,
    termStep_silent, sortStep_silent, signatureStep_silent, bodiesStep_silent,
    attributeStep_silent, finalCall_silent, datatypeStep_silent]
  all_goals
    apply listStep_silent
    intro state token
    silent_step [hdeclareEach]

theorem commandStep_silent (version : Version) (state : CommandState Nat Nat Nat Nat Nat)
    (token : Input) : Silent (commandStep (H := List Event) version state token) := by
  unfold commandStep
  try dsimp only
  silent_step [payloadStep_silent]
/-- What a step of a parser asks of its driver, with the continuations silent. -/
def FlowSilent {σ ρ : Type} : Flow RPM σ ρ → Prop
  | .switchVersion _ resume => Silent resume
  | .discardRest resume => Silent resume
  | _ => True

theorem bodiesArrive_silent (signatures : Array (Parser.Signature Nat))
    (state : ListState (TermState Nat Nat Nat Nat Nat) Unit) (token : Input) :
    Silent (bodiesArrive (H := List Event) signatures state token) := by
  unfold bodiesArrive
  silent_step []

theorem payloadArrive_silent (state : Payload Nat Nat Nat Nat Nat) (token : Input) :
    Silent (payloadArrive (H := List Event) state token) := by
  unfold payloadArrive
  split
  · exact bodiesArrive_silent _ _ _
  · exact Quiet.pure trivial

theorem commandArrive_silent (state : CommandState Nat Nat Nat Nat Nat) (token : Input) :
    Silent (commandArrive (H := List Event) state token) := by
  unfold commandArrive
  split
  · exact payloadArrive_silent _ _
  · exact Quiet.pure trivial
theorem scriptArrive_silent (parser : ScriptParser (List Event)) (token : Input) :
    Silent (Parse.arrive (H := List Event) parser token) := by
  show Silent (ScriptParser.arrive parser token)
  unfold ScriptParser.arrive
  exact commandArrive_silent _ _

theorem scriptStep_quiet (version : Version) (parser : ScriptParser (List Event))
    (token : Input) :
    Quiet FlowSilent (Parse.step (H := List Event) version parser token) := by
  show Quiet FlowSilent (ScriptParser.step version parser token)
  unfold ScriptParser.step
  apply Quiet.bind_silent (commandStep_silent _ _ _)
  intro outcome
  split
  · exact Quiet.pure trivial
  · exact Quiet.pure trivial
  · split
    · exact Quiet.throw _
    · apply Quiet.pure
      show Silent _
      exact Quiet.bind_silent (silent_handlerSetVersion _) fun _ => Quiet.pure trivial
  · apply Quiet.pure
    show Silent _
    exact Quiet.pure trivial
  · exact Quiet.pure trivial

end BSmtLib.ParserProofs

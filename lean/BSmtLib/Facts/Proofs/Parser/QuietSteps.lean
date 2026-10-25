module

public import BSmtLib.Facts.Proofs.Parser.Quiet
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
import all BSmtLib.Parser.Command.Internal.Datatype
import all BSmtLib.Parser.Command.Internal.Function
import all BSmtLib.Parser.Command.Internal.Standard
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# Each step of the parser is silent in a recording run

The closure of `Quiet.Without` under the operations the steps are built from, applied to each step
function by the tactic `silent_step`: unfold the step, then take its binds, matches, conditions,
handler calls and results apart.

Up to the command parser's step, the steps tell the handler only calls, so they hold for every
`bad` that picks out no call (`Quiet.CallsPass`): they write no token point (`Quiet.Silent`), and
they tell the handler no version (`Quiet.isSwitch`). The script parser's step also switches the
handler's version, and is silent (`scriptStep_quiet`).
-/

namespace BSmtLib.Facts.Proofs.Parser.QuietSteps

open BSmtLibSpec.Parser.Properties
open BSmtLib.Parser
open BSmtLib.Grammar.Nodes BSmtLib.Parser.Category.Attribute BSmtLib.Parser.Category.Combinator
open BSmtLib.Parser.Category.Attribute.Internal
open BSmtLib.Parser.Category.Combinator.Internal
open BSmtLib.Parser.Category.Ident BSmtLib.Parser.Category.Pattern
open BSmtLib.Parser.Category.Ident.Internal
open BSmtLib.Parser.Category.Pattern.Internal
open BSmtLib.Parser.Category.QualifiedIdent BSmtLib.Parser.Category.SExpr
open BSmtLib.Parser.Category.QualifiedIdent.Internal
open BSmtLib.Parser.Category.SExpr.Internal
open BSmtLib.Parser.Category.«Sort» BSmtLib.Parser.Category.SortedVar BSmtLib.Parser.Category.Term
open BSmtLib.Parser.Category.«Sort».Internal
open BSmtLib.Parser.Category.SortedVar.Internal
open BSmtLib.Parser.Category.Term.Internal
open BSmtLib.Parser.Category.Token BSmtLib.Parser.Command BSmtLib.Parser.Command.Internal.Datatype
open BSmtLib.Parser.Category.Token.Internal
open BSmtLib.Parser.Command.Internal
open BSmtLib.Parser.Command.Internal.Function BSmtLib.Parser.Command.Internal.Standard BSmtLib.Parser.Script
open BSmtLib.Handler

section

variable {bad : Event → Bool} [Quiet.CallsPass bad]

omit [Quiet.CallsPass bad] in
theorem expectOpen_silent (token : Parser.Internal.Input) :
    Quiet.Avoids bad (expectOpen (H := List Event) token) := by
  unfold expectOpen
  split <;> first | exact Quiet.pure trivial | exact Quiet.throw _

omit [Quiet.CallsPass bad] in
theorem expectClose_silent (token : Parser.Internal.Input) : Quiet.Avoids bad
    (expectClose (H := List Event) token) := by
  unfold expectClose
  split <;> first | exact Quiet.pure trivial | exact Quiet.throw _

omit [Quiet.CallsPass bad] in
theorem expectSymbol_silent (token : Parser.Internal.Input) : Quiet.Avoids bad
    (expectSymbol (H := List Event) token) := by
  unfold expectSymbol
  split <;> first | exact Quiet.pure trivial | exact Quiet.throw _

omit [Quiet.CallsPass bad] in
theorem expectNumeral_silent (token : Parser.Internal.Input) :
    Quiet.Avoids bad (expectNumeral (H := List Event) token) := by
  unfold expectNumeral
  split <;> first | exact Quiet.pure trivial | exact Quiet.throw _

omit [Quiet.CallsPass bad] in
theorem expectKeyword_silent (token : Parser.Internal.Input) :
    Quiet.Avoids bad (expectKeyword (H := List Event) token) := by
  unfold expectKeyword
  split <;> first | exact Quiet.pure trivial | exact Quiet.throw _

omit [Quiet.CallsPass bad] in
theorem expectString_silent (token : Parser.Internal.Input) : Quiet.Avoids bad
    (expectString (H := List Event) token) := by
  unfold expectString
  split <;> first | exact Quiet.pure trivial | exact Quiet.throw _

/-- Takes a silent action apart into the closure lemmas. -/
macro "silent_step" "[" ts:Lean.Parser.Tactic.SolveByElim.arg,* "]" : tactic => `(tactic|
  repeat' (first
    | (intro)
    | (exact Quiet.pure trivial)
    | (exact Quiet.throw _)
    | (apply Quiet.bind_silent)
    | (apply Quiet.silent_call)
    | (solve_by_elim only [$ts,*])
    | (solve_by_elim only [expectOpen_silent, expectClose_silent, expectSymbol_silent,
        expectNumeral_silent, expectKeyword_silent, expectString_silent])
    | split))

omit [Quiet.CallsPass bad] in
theorem identStep_silent (version : Version) (state : IdentState)
    (token : Parser.Internal.Input) :
    Quiet.Avoids bad (IdentState.step (H := List Event) version state token) := by
  unfold IdentState.step
  silent_step []

theorem sortComplete_silent (levels : List (SortLevel Nat)) (head : Ident)
    (arguments : Array Nat) :
    Quiet.Avoids bad (sortComplete (H := List Event) levels head arguments) := by
  unfold sortComplete
  silent_step []

theorem sortStep_silent (version : Version) (state : SortState Nat)
    (token : Parser.Internal.Input) :
    Quiet.Avoids bad (sortStep (H := List Event) version state token) := by
  unfold sortStep
  silent_step [identStep_silent]
theorem sExprStep_silent (version : Version) (state : SExprState Nat)
    (token : Parser.Internal.Input) :
    Quiet.Avoids bad (sExprStep (H := List Event) version state token) := by
  unfold sExprStep
  try dsimp only
  silent_step []

theorem attributeStep_silent (single : Bool) (version : Version)
    (state : AttributeState Nat Nat) (token : Parser.Internal.Input) :
    Quiet.Avoids bad (attributeStep (H := List Event) single version state token) := by
  unfold attributeStep
  try dsimp only
  silent_step [sExprStep_silent, expectClose_silent]

omit [Quiet.CallsPass bad] in
theorem patternStep_silent (version : Version) (state : PatternState)
    (token : Parser.Internal.Input) :
    Quiet.Avoids bad (PatternState.step (H := List Event) version state token) := by
  unfold PatternState.step
  try dsimp only
  silent_step []

theorem qualIdentStep_silent (version : Version) (state : QualIdentState Nat)
    (token : Parser.Internal.Input) :
    Quiet.Avoids bad (qualIdentStep (H := List Event) version state token) := by
  unfold qualIdentStep
  try dsimp only
  silent_step [identStep_silent, sortStep_silent]

theorem sortedVarStep_silent (version : Version) (state : SortedVarState Nat)
    (token : Parser.Internal.Input) :
    Quiet.Avoids bad (sortedVarStep (H := List Event) version state token) := by
  unfold sortedVarStep expectOpen expectSymbol expectClose
  try dsimp only
  silent_step [sortStep_silent]

omit [Quiet.CallsPass bad] in
theorem listStep_silent {σ ρ : Type} (init : σ) {inner : σ → Parser.Internal.Input → Quiet.RPM
    (Parser.Internal.Step σ ρ)}
    (hinner : ∀ state token, Quiet.Avoids bad (inner state token)) (maximum : Option Nat)
    (state : ListState σ ρ) (token : Parser.Internal.Input) :
    Quiet.Avoids bad (ListState.step init inner maximum state token) := by
  unfold ListState.step expectOpen
  try dsimp only
  silent_step [hinner]

theorem termComplete_silent (levels : List (TermLevel Nat Nat Nat)) (term : Nat) :
    Quiet.Avoids bad (termComplete (H := List Event) levels term) := by
  unfold termComplete
  try dsimp only
  silent_step []

theorem startBinder_silent (binder : SortedBinder) (variables : Array (Lexicon.Value.Symbol × Nat)) :
    Quiet.Avoids bad (startBinder (H := List Event) binder variables) := by
  unfold startBinder
  try dsimp only
  silent_step []

theorem endBinder_silent (kind : BinderKind) (scope term : Nat) :
    Quiet.Avoids bad (endBinder (H := List Event) kind scope term) := by
  unfold endBinder
  try dsimp only
  silent_step []

omit [Quiet.CallsPass bad] in
theorem termOpened_silent (state : TermState Nat Nat Nat Nat Nat) (token : Parser.Internal.Input) :
    Quiet.Avoids bad (termOpened (H := List Event) state token) := by
  unfold termOpened
  try dsimp only
  silent_step []

theorem termStep_silent (version : Version) (state : TermState Nat Nat Nat Nat Nat)
    (token : Parser.Internal.Input) : Quiet.Avoids bad (termStep
        (H := List Event) version state token) := by
  have hvars := listStep_silent (bad := bad) (SortedVarState.start (HandledSort := Nat))
    (sortedVarStep_silent version) none
  unfold termStep expectOpen expectSymbol expectClose
  try dsimp only
  silent_step [qualIdentStep_silent, hvars, patternStep_silent, attributeStep_silent,
    termComplete_silent, startBinder_silent, endBinder_silent, termOpened_silent]
omit [Quiet.CallsPass bad] in
theorem symbolStep_silent (state : Unit) (token : Parser.Internal.Input) :
    Quiet.Avoids bad (symbolStep (H := List Event) state token) := by
  unfold symbolStep
  try dsimp only
  silent_step []

omit [Quiet.CallsPass bad] in
theorem sortDecStep_silent (state : SortDecState) (token : Parser.Internal.Input) :
    Quiet.Avoids bad (SortDecState.step (H := List Event) state token) := by
  unfold SortDecState.step
  try dsimp only
  silent_step []

set_option maxHeartbeats 4000000 in
theorem literalStep_silent (version : Version) (state : LiteralState Nat Nat Nat Nat Nat)
    (token : Parser.Internal.Input) : Quiet.Avoids bad (literalStep
        (H := List Event) version state token) := by
  unfold literalStep
  try dsimp only
  silent_step [termStep_silent]

theorem signatureStep_silent (version : Version) (state : SignatureState Nat)
    (token : Parser.Internal.Input) :
    Quiet.Avoids bad (signatureStep (H := List Event) version state token) := by
  have hvars := listStep_silent (bad := bad) (SortedVarState.start (HandledSort := Nat))
    (sortedVarStep_silent version) none
  unfold signatureStep
  try dsimp only
  silent_step [hvars, sortStep_silent]

theorem functionDecStep_silent (version : Version) (state : FunctionDecState Nat)
    (token : Parser.Internal.Input) :
    Quiet.Avoids bad (functionDecStep (H := List Event) version state token) := by
  unfold functionDecStep
  try dsimp only
  silent_step [signatureStep_silent]

theorem constructorStep_silent (version : Version) (state : ConstructorState Nat)
    (token : Parser.Internal.Input) : Quiet.Avoids bad (constructorStep
        (H := List Event) version state token) := by
  have hvars := listStep_silent (bad := bad) (SortedVarState.start (HandledSort := Nat))
    (sortedVarStep_silent version) none
  unfold constructorStep
  try dsimp only
  silent_step [hvars]

theorem datatypeStep_silent {start : Array Lexicon.Value.Symbol → Quiet.RPM Unit}
    (hstart : ∀ parameters, Quiet.Avoids bad (start parameters)) (version : Version)
    (state : DatatypeState Nat) (token : Parser.Internal.Input) :
    Quiet.Avoids bad (datatypeStep (H := List Event) start version state token) := by
  have hsymbols := listStep_silent (bad := bad) () symbolStep_silent none
  have hconstructors := listStep_silent (bad := bad) (ConstructorState.start (HandledSort := Nat))
    (constructorStep_silent version) none
  unfold datatypeStep
  try dsimp only
  silent_step [hstart, hsymbols, hconstructors]

theorem bodyStep_silent (version : Version) (state : TermState Nat Nat Nat Nat Nat)
    (token : Parser.Internal.Input) : Quiet.Avoids bad (bodyStep
        (H := List Event) version state token) := by
  unfold bodyStep
  try dsimp only
  silent_step [termStep_silent]

theorem bodiesStep_silent (count : Nat) (version : Version)
    (state : ListState (TermState Nat Nat Nat Nat Nat) Unit) (token : Parser.Internal.Input) :
    Quiet.Avoids bad (bodiesStep (H := List Event) count version state token) := by
  have hbodies := listStep_silent (bad := bad)
    (TermState.init (HandledSExpr := Nat) (HandledAttribute := Nat)
    (HandledSort := Nat) (HandledTerm := Nat) (Scope := Nat)) (bodyStep_silent version) (some count)
  unfold bodiesStep
  try dsimp only
  silent_step [hbodies]

theorem finalCall_silent (final : FinalCall Nat Nat Nat) :
    Quiet.Avoids bad (finalCall (H := List Event) final) := by
  unfold finalCall
  try dsimp only
  silent_step []

set_option maxHeartbeats 4000000 in
theorem payloadStep_silent (version : Version) (state : Payload Nat Nat Nat Nat Nat)
    (token : Parser.Internal.Input) : Quiet.Avoids bad (payloadStep
        (H := List Event) version state token) := by
  have hterms := listStep_silent (bad := bad)
    (TermState.init (HandledSExpr := Nat) (HandledAttribute := Nat)
    (HandledSort := Nat) (HandledTerm := Nat) (Scope := Nat)) (termStep_silent version) none
  have hliterals := listStep_silent (bad := bad) (LiteralState.init (HandledSExpr := Nat)
    (HandledAttribute := Nat) (HandledSort := Nat) (HandledTerm := Nat) (Scope := Nat))
    (literalStep_silent version) none
  have hsorts := listStep_silent (bad := bad) (SortState.init (HandledSort := Nat))
    (sortStep_silent version)
    none
  have hsortDecs := listStep_silent (bad := bad) SortDecState.start sortDecStep_silent none
  have hsymbols := listStep_silent (bad := bad) () symbolStep_silent none
  have hfunctions := listStep_silent (bad := bad) (FunctionDecState.start (HandledSort := Nat))
    (functionDecStep_silent version) none
  have hdatatypes : ∀ count (start : Array Lexicon.Value.Symbol → Quiet.RPM Unit),
      (∀ parameters, Quiet.Avoids bad (start parameters)) →
      ∀ state token, Quiet.Avoids bad (ListState.step (DatatypeState.start (HandledSort := Nat))
        (fun state token => do
          match ← datatypeStep (H := List Event) start version state token with
          | .more state => return Parser.Internal.Step.more state
          | .done constructors =>
            Parser.Internal.call (CommandHandler.endDatatypeDeclaration
              (Grammar.Multiple.Constructors.Internal.new constructors))
            return .done ()) (some count) state token) := by
    intro count start hstart state token
    apply listStep_silent
    intro state token
    silent_step [datatypeStep_silent hstart]
  have hdeclare : ∀ symbol state token, Quiet.Avoids bad (datatypeStep (H := List Event)
      (fun parameters =>
        Parser.Internal.call (CommandHandler.startDeclareDatatype symbol
          (Grammar.Multiple.Symbols.Internal.new parameters)))
      version state token) := fun symbol =>
    datatypeStep_silent (fun _ => by apply Quiet.silent_call) version
  have hdeclarations := fun count => hdatatypes count
    (fun parameters =>
      Parser.Internal.call (CommandHandler.startDatatypeDeclaration
        (Grammar.Multiple.Symbols.Internal.new parameters)))
    (fun _ => by apply Quiet.silent_call)
  have hdeclareEach : ∀ state token, Quiet.Avoids bad (datatypeStep (H := List Event)
      (fun parameters =>
        Parser.Internal.call (CommandHandler.startDatatypeDeclaration
          (Grammar.Multiple.Symbols.Internal.new parameters)))
      version state token) :=
    datatypeStep_silent (fun _ => by apply Quiet.silent_call) version
  have hbodies := fun count => listStep_silent (bad := bad) (TermState.init (HandledSExpr := Nat)
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

theorem commandStep_silent (version : Version)
    (state : CommandState Nat Nat Nat Nat Nat Empty)
    (token : Parser.Internal.Input) : Quiet.Avoids bad (commandStep
        (H := List Event) version state token) := by
  unfold commandStep
  try dsimp only
  silent_step [payloadStep_silent]
  -- the recording handler has no non-standard parser
  all_goals exact Empty.elim ‹CommandHandler.NonstandardParser (List Event)›

theorem bodiesArrive_silent (signatures : Array (Grammar.Multiple.FunctionSignature Nat))
    (state : ListState (TermState Nat Nat Nat Nat Nat) Unit) (token : Parser.Internal.Input) :
    Quiet.Avoids bad (bodiesArrive (H := List Event) signatures state token) := by
  unfold bodiesArrive
  silent_step []

theorem payloadArrive_silent (state : Payload Nat Nat Nat Nat Nat) (token : Parser.Internal.Input) :
    Quiet.Avoids bad (payloadArrive (H := List Event) state token) := by
  unfold payloadArrive
  split
  · exact bodiesArrive_silent _ _ _
  · exact Quiet.pure trivial

theorem commandArrive_silent (state : CommandState Nat Nat Nat Nat Nat Empty)
    (token : Parser.Internal.Input) :
    Quiet.Avoids bad (commandArrive (H := List Event) state token) := by
  unfold commandArrive
  split
  · exact payloadArrive_silent _ _
  · exact Quiet.pure trivial
theorem scriptArrive_silent (parser : ScriptParser (List Event)) (token : Parser.Internal.Input) :
    Quiet.Avoids bad (Parser.Internal.ParseByToken.arrive (H := List Event) parser token) := by
  show Quiet.Avoids bad (ScriptParser.Internal.arrive parser token)
  unfold ScriptParser.Internal.arrive
  exact commandArrive_silent _ _

end

/-- What a step of a parser asks of its driver, with the continuations silent. -/
def FlowSilent {σ ρ : Type} : Parser.Internal.Flow Quiet.RPM σ ρ → Prop
  | .switchVersion _ resume => Quiet.Silent resume
  | .discardRest resume => Quiet.Silent resume
  | _ => True

theorem scriptStep_quiet (version : Version) (parser : ScriptParser (List Event))
    (token : Parser.Internal.Input) :
    Quiet FlowSilent (Parser.Internal.ParseByToken.step
        (H := List Event) version parser token) := by
  show Quiet FlowSilent (ScriptParser.Internal.step version parser token)
  unfold ScriptParser.Internal.step
  apply Quiet.bind_silent (commandStep_silent _ _ _)
  intro outcome
  split
  · exact Quiet.pure trivial
  · exact Quiet.pure trivial
  · split
    · exact Quiet.throw _
    · apply Quiet.pure
      show Quiet.Silent _
      exact Quiet.bind_silent (Quiet.silent_handlerSetVersion _) fun _ => Quiet.pure trivial
  · apply Quiet.pure
    show Quiet.Silent _
    exact Quiet.pure trivial
  · exact Quiet.pure trivial

end BSmtLib.Facts.Proofs.Parser.QuietSteps

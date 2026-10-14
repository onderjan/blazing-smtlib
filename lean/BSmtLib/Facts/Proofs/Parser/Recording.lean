import BSmtLibSpec.Facts
import BSmtLib.Facts.Proofs.Parser.Lemmas

/-!
# The recording run as a run of the library's parser

The spec states the placement of the calls on a recording run
(`BSmtLibSpec.Parser.Properties.record`), whose handler writes down every call in the log that is
the state of the monad `Recording`. A library handler whose state is that log (`List Event`) runs
the parser in the same monad. Its error type is `Unit`, since a library handler must be able to fail
on a non-standard command; it agrees with the recording handler with its errors (of which it has
none) mapped into `Unit` (`recordingHandlerU`), and runs of the two make the same records
(`run_adaptHandler`).
-/

namespace BSmtLib.Facts.Proofs.Parser.Recording

open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Handler
open BSmtLib.Facts.Proofs.Parser.Lemmas

/-- The recording handler, with its errors (of which it has none) in `Unit`. -/
def recordingHandlerU : Traversal.Handler Recording Unit Recorded where
  call request := recordingCall request
  setVersion := recordingHandler.setVersion

section

/-- The recording library handler agrees with the recording handler. -/
theorem agrees_recording :
    Agrees (H := List Event) (m := Id)
      (recordingHandlerU : Traversal.Handler (StateT (List Event) Id) Unit
        (valuesOf (List Event))) where
  handleSort _ _ := rfl
  handleTerm node := by cases node <;> rfl
  handleSExpr node := by cases node <;> rfl
  handleAttribute _ v := by rcases v with _ | v <;> (try cases v) <;> rfl
  annotateTerm _ _ := rfl
  startLet _ := rfl
  endLet _ _ := rfl
  startQuantifier _ _ := rfl
  endQuantifier _ _ _ := rfl
  startLambda _ := rfl
  endLambda _ _ := rfl
  startMatch _ := rfl
  startMatchCase _ _ := rfl
  endMatchCase _ _ _ := rfl
  endMatch _ _ := rfl
  setVersion _ := rfl
  commandAssert _ := rfl
  commandCheckSat := rfl
  commandCheckSatAssuming _ := rfl
  commandDeclareConst _ _ := rfl
  startDeclareDatatype _ _ := rfl
  endDeclareDatatype _ := rfl
  startDeclareDatatypes _ := rfl
  startDatatypeDeclaration _ := rfl
  endDatatypeDeclaration _ := rfl
  endDeclareDatatypes := rfl
  commandDeclareFun _ _ _ := rfl
  commandDeclareSort _ _ := rfl
  commandDeclareSortParameter _ := rfl
  commandDefineConst _ _ _ := rfl
  startDefineFun _ := rfl
  endDefineFun _ := rfl
  startDefineFunRec _ := rfl
  endDefineFunRec _ := rfl
  startDefineFunsRec _ := rfl
  startRecursiveBody _ := rfl
  endRecursiveBody _ := rfl
  endDefineFunsRec := rfl
  startDefineSort _ _ := rfl
  endDefineSort _ := rfl
  commandEcho _ := rfl
  commandExit := rfl
  commandGetAssertions := rfl
  commandGetAssignment := rfl
  commandGetInfo _ := rfl
  commandGetModel := rfl
  commandGetOption _ := rfl
  commandGetProof := rfl
  commandGetUnsatAssumptions := rfl
  commandGetUnsatCore := rfl
  commandGetValue _ := rfl
  commandPop _ := rfl
  commandPush _ := rfl
  commandReset := rfl
  commandResetAssertions := rfl
  commandSetInfo _ := rfl
  commandSetLogic _ := rfl
  commandSetOption _ := rfl

end
/-! ## The records of the two recording handlers -/

open BSmtLibSpec.Facts.Proofs.Parser (Program)

@[simp] theorem recordingHandlerU_setVersion :
    recordingHandlerU.setVersion = recordingHandler.setVersion := rfl

@[simp] theorem recordingHandlerU_call {returns : Returns} (request : Call Recorded returns) :
    recordingHandlerU.call request = recordingCall request := rfl

/-- A failure of a recording run, in `Unit`. -/
def mapCause : Cause Empty → Cause Unit
  | .syntax error => .syntax error
  | .handler error => nomatch error

theorem adapt_call_U {returns : Returns} (request : Call Recorded returns) :
    ExceptT.adapt mapCause (Traversal.call recordingHandler request) =
      Traversal.call recordingHandlerU request := by
  apply ExceptT.ext
  simp only [Traversal.call, recordingHandlerU_call, recordingCall, ExceptT.run_adapt,
    Functor.map_map]
  congr 1
  funext result
  cases result with
  | error e => exact nomatch e
  | ok => rfl

theorem adapt_callUnit_U (request : Call Recorded .nothing) :
    ExceptT.adapt mapCause (Program.callUnit recordingHandler request) =
      Program.callUnit recordingHandlerU request :=
  adapt_call_U request

theorem adapt_switch_U (policy : VersionPolicy) (declarations : Nat)
    (version : BSmtLibSpec.Lexicon.Version) :
    ExceptT.adapt mapCause
        (switchVersion recordingHandler recordingProducer policy declarations version) =
      switchVersion recordingHandlerU recordingProducer policy declarations version := by
  rw [BSmtLibSpec.Facts.Proofs.Parser.Equations.switchVersion_eq,
      BSmtLibSpec.Facts.Proofs.Parser.Equations.switchVersion_eq]
  split <;> simp [mapCause, Function.comp_def]

theorem run_adaptHandler {policy : VersionPolicy} {α : Type} (p : Program Recorded α) :
    ∀ items : List Received,
    Program.run recordingPoints recordingHandlerU recordingProducer policy p items =
      ExceptT.adapt mapCause
        (Program.run recordingPoints recordingHandler recordingProducer policy p items) := by
  induction p with
  | done => intro; simp
  | receive start next ih =>
    intro items
    cases items with
    | nil => simp [Program.run, Program.stuckFailure, mapCause]
    | cons item items =>
      cases start with
      | none => simp [Program.run, ih, Traversal.receive]
      | some request =>
        simp only [Program.run, Traversal.receive, Program.arrival_some, adapt_bind, adapt_lift,
          ih, ← adapt_call_U, bind_assoc]
        erw [adapt_bind, adapt_lift]
        rfl
  | call request next ih =>
    intro items
    simp only [Program.run, adapt_bind, ih, adapt_call_U]
  | setVersion version next ih => intro; simp [Program.run, ih]
  | discard next ih => intro; simp [Program.run, ih]
  | switch declarations version next ih =>
    intro items
    simp only [Program.run, adapt_bind, ih, adapt_switch_U]
  | stuck => intro; simp [Program.run, Program.stuckFailure, mapCause]

theorem state_bind_pure {ε σ α β : Type} (x : ExceptT ε (StateM σ) α) (b : β) (s : σ) :
    ((x >>= fun _ => pure b).run.run s).2 = (x.run.run s).2 := by
  simp only [ExceptT.run_bind, StateT.run_bind]
  rcases h : x.run.run s with ⟨e, s'⟩
  cases e <;> rfl

theorem state_adapt {ε ε' σ α : Type} (f : ε → ε') (x : ExceptT ε (StateM σ) α) (s : σ) :
    ((ExceptT.adapt f x).run.run s).2 = (x.run.run s).2 := by
  simp only [ExceptT.run_adapt, StateT.run_map]
  rfl

/-- The records of a run of the traversal with `recordingHandlerU` are those of `record`. -/
theorem record_eq_U {version : BSmtLibSpec.Lexicon.Version}
    {commands : List BSmtLibSpec.Grammar.Tree.Command}
    (hscript : BSmtLibSpec.Grammar.Script version commands) :
    ((Traversal.script recordingPoints recordingHandlerU recordingProducer
      VersionPolicy.unrestricted version commands).run.run []).2.reverse =
      record version commands := by
  have hU := BSmtLibSpec.Facts.Parser.script_eq_parse recordingPoints recordingHandlerU
    recordingProducer VersionPolicy.unrestricted hscript [] (Nat.lt_succ_self _)
  have hE := BSmtLibSpec.Facts.Parser.script_eq_parse recordingPoints recordingHandler
    recordingProducer VersionPolicy.unrestricted hscript [] (Nat.lt_succ_self _)
  rw [run_adaptHandler, hE] at hU
  have hstate := congrArg (fun x => ((ExceptT.run x).run []).2) hU
  simp only [state_adapt, state_bind_pure] at hstate
  simp only [record, Id.run]
  rw [hstate]

end BSmtLib.Facts.Proofs.Parser.Recording

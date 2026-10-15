module

public import BSmtLib.Facts.Proofs.Parser.Refused
public import BSmtLib.Facts.Proofs.Parser.Cut
import all BSmtLib.Parser.Script

@[expose] public section

/-!
# The recording run on what a parser takes

On what a parser takes for commands (`Takes`), the parser's recording run writes what `record`
writes for them, as on a script; where a declaration that names no supported version ends the
commands, both fail after it. The recording run with the library's handler, whose errors are in
`Unit`, makes the records of the recording run of the spec, whose handler cannot fail: command
by command, each run is the other with its errors mapped (`command_U`), as the runs of
`BSmtLibSpec.Facts.Proofs.Parser.Simulation`'s reader of a command are.
-/

namespace BSmtLib.Facts.Proofs.Parser.RefusedRecord

open BSmtLibSpec.Grammar
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Parser.Traversal
open BSmtLibSpec.Facts.Proofs.Parser.Simulation (commandFirst run_command)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Run
open BSmtLib.Facts.Proofs.Parser.Cut BSmtLib.Facts.Proofs.Parser.Lemmas
open BSmtLib.Facts.Proofs.Parser.Recording BSmtLib.Facts.Proofs.Parser.Refused
open BSmtLib.Facts.Proofs.Parser.Script

theorem bind_unit_cancel {ε σ β : Type} {x y : ExceptT ε (StateM σ) Unit} (b : β)
    (h : (x >>= fun _ => pure b) = (y >>= fun _ => pure b)) : x = y := by
  have := congrArg (fun z => z >>= fun _ => (pure () : ExceptT ε (StateM σ) Unit)) h
  simp only [bind_assoc, pure_bind] at this
  simpa only [bind_pure_unit] using this

/-- A valid command's recording run with the library's handler is the spec's, its errors
mapped. -/
theorem command_U {version : BSmtLibSpec.Lexicon.Version} {command : Tree.Command}
    (hvalid : command.Valid version) :
    Traversal.command recordingPoints recordingHandlerU command =
      ExceptT.adapt mapCause (Traversal.command recordingPoints recordingHandler command) := by
  have hU := run_command (points := recordingPoints) (handler := recordingHandlerU)
    (producer := recordingProducer) (policy := VersionPolicy.unrestricted) version command
    [] (n := 10 * sizeOf command + 1) hvalid (by omega)
  have hE := run_command (points := recordingPoints) (handler := recordingHandler)
    (producer := recordingProducer) (policy := VersionPolicy.unrestricted) version command
    [] (n := 10 * sizeOf command + 1) hvalid (by omega)
  have hA := run_adaptHandler (policy := VersionPolicy.unrestricted)
    (commandFirst (10 * sizeOf command + 1))
    (BSmtLibSpec.Facts.Proofs.Parser.Simulation.items command.tokens ++ [])
  rw [hU, hE, adapt_bind] at hA
  simp only [adapt_pure] at hA
  exact bind_unit_cancel _ hA

/-- The recording run with the library's handler of what a parser takes is the spec's, its errors
mapped. -/
theorem commands_U {start : BSmtLibSpec.Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes start commands taken ending) :
    ∀ (declarations : Nat),
    Traversal.commands recordingPoints recordingHandlerU recordingProducer
        VersionPolicy.unrestricted declarations commands =
      ExceptT.adapt mapCause (Traversal.commands recordingPoints recordingHandler
        recordingProducer VersionPolicy.unrestricted declarations commands) := by
  induction htakes with
  | done =>
    intro declarations
    simp [Traversal.commands, receive]
  | stop hvalid hmode =>
    intro declarations
    obtain rfl := modeAfter_unparsed hmode
    simp only [Traversal.commands, adapt_bind, command_U hvalid, adapt_lift]
    simp [receive]
  | @command _ next _ _ _ command hvalid hmode _ ih =>
    intro declarations
    obtain ⟨hexit, -⟩ := modeAfter_read hmode
    rw [commands_cons _ _ _ hexit (namesNoVersion_of_read hmode),
      commands_cons _ _ _ hexit (namesNoVersion_of_read hmode), command_U hvalid, adapt_bind]
    congr 1
    funext _
    cases command.declaredVersion with
    | none => exact ih declarations
    | some declared =>
      simp only [adapt_bind, ← adapt_switch_U]
      congr 1
      funext _
      exact ih (declarations + 1)
  | refused hvalid hmode =>
    intro declarations
    rw [commands_refused _ _ _ hmode, commands_refused _ _ _ hmode, command_U hvalid,
      adapt_bind]
    simp [mapCause]

/-- The recording run with the library's handler of a script read from the version is the spec's,
its errors mapped. -/
theorem script_U {start : BSmtLibSpec.Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes start commands taken ending)
    (version : BSmtLibSpec.Lexicon.Version) :
    Traversal.script recordingPoints recordingHandlerU recordingProducer
        VersionPolicy.unrestricted version commands =
      ExceptT.adapt mapCause (Traversal.script recordingPoints recordingHandler recordingProducer
        VersionPolicy.unrestricted version commands) := by
  simp only [Traversal.script, adapt_bind, adapt_lift, recordingHandlerU_setVersion,
    commands_U htakes 0]

/-- The records of the recording run with the library's handler on what a parser takes are those
of `record`. -/
theorem record_eq_U_takes {start : BSmtLibSpec.Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes start commands taken ending)
    (version : BSmtLibSpec.Lexicon.Version) :
    ((Traversal.script recordingPoints recordingHandlerU recordingProducer
      VersionPolicy.unrestricted version commands).run.run []).2.reverse =
        record version commands := by
  simp only [record, Id.run]
  rw [script_U htakes, state_adapt]

/-- An error of the recording run with the library's handler is a syntax error. -/
theorem commands_U_error {start : BSmtLibSpec.Lexicon.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending} (htakes : Takes start commands taken ending)
    {version : BSmtLibSpec.Lexicon.Version} {e : Cause Unit} {events : List Event}
    (h : ((Traversal.script recordingPoints recordingHandlerU recordingProducer
      VersionPolicy.unrestricted version commands).run.run []) = (.error e, events)) :
    ∃ error, e = .syntax error := by
  rw [script_U htakes] at h
  simp only [ExceptT.run_adapt, StateT.run_map] at h
  revert h
  generalize ((Traversal.script recordingPoints recordingHandler recordingProducer
    VersionPolicy.unrestricted version commands).run.run []) = r
  rcases r with ⟨_ | _, s⟩
  · rename_i cause
    rcases cause with error | error
    · intro h
      refine ⟨error, ?_⟩
      have := congrArg Prod.fst h
      simp only [Functor.map, Except.mapError, mapCause] at this
      cases this
      rfl
    · exact nomatch error
  · intro h
    have := congrArg Prod.fst h
    simp [Functor.map, Except.mapError] at this

/-- The recording run of a script with the library's handler: the handler's switch to the
version, then the commands. -/
theorem script_U_run (version : BSmtLibSpec.Lexicon.Version) (commands : List Tree.Command) :
    (Traversal.script recordingPoints recordingHandlerU recordingProducer
      VersionPolicy.unrestricted version commands).run.run [] =
      (Traversal.commands recordingPoints recordingHandlerU recordingProducer
        VersionPolicy.unrestricted 0 commands).run.run [.handlerSwitch version] := by
  rfl

/-- The parser's recording run on what a parser takes, and any rest, the handler told the version
first: the recording run of the traversal with the library's handler, its errors as the parser's
causes. -/
theorem parserRun_takes {version : Token.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending}
    (htakes : Takes
        (Bridge.version version) commands taken ending) {inputs : List Parser.Internal.Input}
    (hs : inputs.map Bridge.received = taken.map some) (rest : List Parser.Internal.Input) :
    (driveInput recordingPoints recordingProducer version
      (ScriptParser.new (H := List Event) unrestrictedPosture)
        (inputs ++ rest)).run.run [] =
      match (Traversal.script recordingPoints recordingHandlerU recordingProducer
          VersionPolicy.unrestricted (Bridge.version version) commands).run.run [] with
      | (.ok (), events) => (.ok (some ((), rest)), events)
      | (.error e, events) => (.error (causeOf e), events) := by
  have hrun := takes_runs (H := List Event) (m := Id) (points := recordingPoints)
    (h := (recordingHandlerU :
      Traversal.Handler (StateT (List Event) Id) Unit (valuesOf (List Event))))
    agrees_recording recordingProducer unrestrictedPosture htakes version rfl 0 hs rest
  rw [driveInput_run, show ScriptParser.new (H := List Event) unrestrictedPosture =
    scriptAt unrestrictedPosture .awaiting 0 from rfl, hrun]
  simp only [policyOf_unrestricted, adaptRun, script_U_run]
  simp only [ExceptT.run_bind, ExceptT.run_adapt, StateT.run_bind, StateT.run_map]
  rcases hr : (Traversal.commands recordingPoints recordingHandlerU recordingProducer
    VersionPolicy.unrestricted 0 commands).run.run [.handlerSwitch (Bridge.version version)] with
    ⟨_ | _, s⟩ <;>
    (erw [hr]
     rfl)

/-- The parser's recording run on what a parser takes writes what `record` writes. -/
theorem parserRecord_takes {version : Token.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending}
    (htakes : Takes
        (Bridge.version version) commands taken ending) {inputs : List Parser.Internal.Input}
    (hs : inputs.map Bridge.received = taken.map some) :
    parserRecord version inputs = record (Bridge.version version) commands := by
  have hrun := parserRun_takes htakes hs []
  rw [List.append_nil, driveInput_run] at hrun
  unfold parserRecord recordedRun
  rw [hrun, ← record_eq_U_takes htakes]
  generalize ((Traversal.script recordingPoints recordingHandlerU recordingProducer
    VersionPolicy.unrestricted (Bridge.version version) commands).run.run []) = r
  rcases r with ⟨_ | _, s⟩ <;> rfl

/-- On what a parser takes, the parser's recording run finishes before the rest, or fails with
a cause that is no handler's. -/
theorem parserResult_takes {version : Token.Version} {commands : List Tree.Command}
    {taken : List Received} {ending : Ending}
    (htakes : Takes
        (Bridge.version version) commands taken ending) {inputs : List Parser.Internal.Input}
    (hs : inputs.map Bridge.received = taken.map some) (rest : List Parser.Internal.Input) :
    ((driveParse recordingPoints recordingProducer version
      (ScriptParser.new (H := List Event) unrestrictedPosture)
        (inputs ++ rest)).run.run (startEvents version)).1 = .ok (some ((), rest)) ∨
      ∃ error, ((driveParse recordingPoints recordingProducer version
        (ScriptParser.new (H := List Event) unrestrictedPosture) (inputs ++ rest)).run.run
          (startEvents version)).1 = .error (causeOf (.syntax error)) := by
  rw [← driveInput_run, parserRun_takes htakes hs rest]
  rcases hr : (Traversal.script recordingPoints recordingHandlerU recordingProducer
    VersionPolicy.unrestricted (Bridge.version version) commands).run.run [] with ⟨_ | e, s⟩
  · obtain ⟨error, rfl⟩ := commands_U_error htakes hr
    exact Or.inr ⟨error, rfl⟩
  · exact Or.inl rfl

end BSmtLib.Facts.Proofs.Parser.RefusedRecord

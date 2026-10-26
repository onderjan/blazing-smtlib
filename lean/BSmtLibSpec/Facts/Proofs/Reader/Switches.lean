module

public import BSmtLibSpec.Facts.Proofs.Reader
public import BSmtLibSpec.Facts.Proofs.Reader.Requests

@[expose] public section

/-!
# A declared version among the calls

The traversal of a script tells its handler the version of each version declaration, after the
declaration (`Traversal.switchVersion`); so the calls for a file's commands hold the switch to
each version a command declares (`handlerSwitch_mem_calls`).

A fact of the specification formalism (`BSmtLibSpec`).
-/

namespace BSmtLibSpec.Facts.Proofs.Reader.Switches

open BSmtLibSpec BSmtLibSpec.Lexicon BSmtLibSpec.Grammar BSmtLibSpec.Parser
open BSmtLibSpec.Parser.Properties
open BSmtLibSpec.Facts.Proofs.Parser.Recording BSmtLibSpec.Facts.Proofs.Parser.Simulation
open BSmtLibSpec.Facts.Proofs.Reader.Finishes BSmtLibSpec.Facts.Proofs.Reader.Requests

/-- The recording run of the commands of a script holds the switch to each version a command
declares. -/
theorem handlerSwitch_mem_record {version : Version} {commands : List Tree.Command}
    (h : Script version commands) :
    ∀ (declarations : Nat) (state : List Event) (command : Tree.Command) (declared : Version),
      command ∈ commands → command.declaredVersion = some declared →
      .handlerSwitch declared ∈ ((recordCommands declarations commands).run.run state).2 := by
  induction h with
  | done =>
    intro _ _ _ _ hmem
    cases hmem
  | @command version next rest first hv hm hrest ih =>
    intro declarations state command declared hmem hd
    have hne : first ≠ .exit := by
      rintro rfl
      simp [Tree.Command.modeAfter] at hm
    obtain ⟨events, hrun, -, -, -⟩ := command_events hv state
    cases hfd : first.declaredVersion with
    | none =>
      rw [recordCommands_none hne hfd, bind_run hrun, namesNoVersion_eq_false hm]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · rw [hfd] at hd
        cases hd
      · exact ih declarations _ command declared hmem hd
    | some v =>
      rw [recordCommands_some hne hfd, bind_run hrun, bind_run (switch_run declarations v _)]
      rcases List.mem_cons.mp hmem with rfl | hmem
      · rw [hfd] at hd
        injection hd with hd
        subst hd
        obtain ⟨later, hlater, -⟩ := commands_events (script_takes hrest) (declarations + 1)
          (.handlerSwitch v :: .producerSwitch v :: (events.reverse ++ state))
        rw [hlater]
        simp
      · exact ih (declarations + 1) _ command declared hmem hd
  | stop hv hm =>
    intro _ _ command declared hmem hd
    obtain rfl := modeAfter_unparsed hm
    rcases List.mem_singleton.mp hmem with rfl
    simp [Tree.Command.declaredVersion] at hd

/-- The calls for a file's commands hold the switch to each version a command declares. -/
theorem handlerSwitch_mem_calls {version : Version} {input : Regex.Chars}
    {commands : List Tree.Command} (hfile : File version input commands)
    {command : Tree.Command} (hmem : command ∈ commands) {declared : Version}
    (hd : command.declaredVersion = some declared) :
    .handlerSwitch declared ∈ BSmtLibSpec.Reader.calls version commands := by
  have hrec := handlerSwitch_mem_record (script_of_file hfile) 0 [.handlerSwitch version] command
    declared hmem hd
  have hscript : (Traversal.script (ε := Empty) recordingPoints recordingHandler recordingProducer
      VersionPolicy.unrestricted version commands).run.run [] =
        (recordCommands 0 commands).run.run [.handlerSwitch version] :=
    bind_run (setVersion_run version [])
  unfold BSmtLibSpec.Reader.calls record
  simp only [Id.run]
  rw [hscript]
  exact List.mem_filter.mpr ⟨List.mem_reverse.mpr hrec, rfl⟩

end BSmtLibSpec.Facts.Proofs.Reader.Switches

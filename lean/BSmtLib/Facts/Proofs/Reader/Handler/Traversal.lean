module

public import BSmtLib.Facts.Proofs.Reader.Handler.Reader
public import BSmtLib.Facts.Parser
import all BSmtLib.Facts.Parser.Adapters.Run

@[expose] public section

/-!
# The script reader with any handler that never fails makes the traversal's calls

`hRun_traversal`: the driver's run over items standing for what a parser receives for a valid
script is the traversal of the script as the specification formalism (`BSmtLibSpec`) defines it,
with token points and a producer that do nothing (`Facts.Parser.script_follows_traversal`). This
holds for every handler of the formalism the library handler agrees with.

So the script reader with a handler whose calls never fail, fed a file in any slices, reads to the
end with a result and leaves its handler where the traversal of the file's commands leaves it
(`reader_follows_traversal`).
-/

namespace BSmtLib.Facts.Proofs.Reader.Handler.Traversal

open BSmtLibSpec BSmtLibSpec.Grammar
open BSmtLibSpec.Parser BSmtLibSpec.Parser.Properties
open BSmtLib.Handler
open BSmtLib.Parser.Script (ScriptParser)
open BSmtLib.Facts.Lexer.Adapters (toVersion)
open BSmtLib.Facts.Parser.Adapters.Bridge BSmtLib.Facts.Parser.Adapters.Bridge.Rejection
open BSmtLib.Facts.Parser.Adapters.Run BSmtLib.Facts.Parser.Adapters.Run.Rejection
open BSmtLib.Facts.Proofs.Reader.Handler.Drive BSmtLib.Facts.Proofs.Reader.Handler.Loop
open BSmtLib.Facts.Proofs.Parser.Blank.Basic
open BSmtLib.Facts.PublicApi.Adapters (readThrough allVersions)

variable {H : Type} [CommandHandler H Id]

theorem version_libVersion (version : Lexicon.Version) :
    Bridge.version (Bridge.libVersion version) = version := by
  cases version <;> rfl

theorem received_items {items : List LibItem} {commands : List Tree.Command}
    (hst : items.map (rcv ∘ Subtype.val) = received commands) :
    (items.map Subtype.val).map Bridge.received = (received commands).map some := by
  rw [← hst, List.map_map, List.map_map]
  apply List.map_congr_left
  intro item _
  exact Proofs.Parser.Rejection.Script.received_rcv item.property

/-- Where the driver's run over items standing for what a parser receives for a valid script ends
the script, the traversal of the script from the same handler, with token points and a producer that
do nothing, does not fail and leaves the handler where the run does, for every handler of the
formalism the library handler agrees with. -/
theorem hRun_traversal
    {h : Traversal.Handler (StateT H Id) (Handler.Error H) (valuesOf H)}
    (hA : BSmtLib.Facts.Parser.Adapters.Bridge.Agrees h)
    {version : Lexicon.Version} {commands : List Tree.Command} (hscript : Script version commands)
    (init : H) {items : List LibItem} (hst : items.map (rcv ∘ Subtype.val) = received commands)
    {r : Unit × List BSmtLib.Parser.Internal.Input} {s : H}
    (hr : hRun version init items = (.ok (.inr r), s)) :
    (Traversal.script nullPoints h nullProducer VersionPolicy.unrestricted version
      commands).run.run init = (.ok (), s) := by
  have hscript' : Script (Bridge.version (Bridge.libVersion version)) commands := by
    rw [version_libVersion]; exact hscript
  have hsf := Facts.Parser.script_follows_traversal (points := nullPoints) hA nullProducer
    unrestrictedPosture hscript' (received_items hst) []
  rw [version_libVersion, Proofs.Parser.Cut.policyOf_unrestricted, List.append_nil] at hsf
  have hl := congrArg (fun x => (x.run.run init)) hsf
  unfold driveInput at hl
  rw [driveParse_eq] at hl
  simp only [ExceptT.run_bind, StateT.run_bind, ExceptT.run_lift, StateT.run_map, Drive.id_bind]
    at hl
  unfold hRun at hr
  generalize hS : (Handler.setVersion (H := H) (Bridge.libVersion version)).run init = S at hl hr
  obtain ⟨u, s₀⟩ := S
  dsimp only at hr
  have hm : ((fun p => (Except.ok p.fst, p.snd)) <$> (((u, s₀) : Unit × H) : Id (Unit × H)) :
      Id (Except (BSmtLib.Parser.ParseErrorKind (Handler.Error H)) Unit × H)) =
      (.ok u, s₀) := rfl
  rw [hm] at hl
  dsimp only at hl
  simp only [StateT.run_bind, Drive.id_bind] at hl
  rw [hr] at hl
  dsimp only at hl
  simp only [adaptRun, ExceptT.adapt, ExceptT.run_mk, StateT.run_map] at hl
  change StateT.run (Traversal.script nullPoints h nullProducer VersionPolicy.unrestricted version
    commands : StateT H Id _) init = _
  revert hl
  generalize StateT.run (Traversal.script nullPoints h nullProducer VersionPolicy.unrestricted
    version
    commands : StateT H Id _) init = T
  obtain ⟨t, s'⟩ := T
  rcases t with e | ⟨⟩
  · intro hl; cases hl
  · intro hl; cases hl; rfl

/-- The script reader with a handler whose calls never fail reads a file of commands to the end
with a result. The traversal of the file's commands from the same handler, with token points and
a producer that do nothing, does not fail and leaves the handler the reader leaves, for every
handler of the formalism the library handler agrees with. The reader starts from the handler in
the version the file is read in, allowing every version, and is fed the file in any slices and
then the end of the input. -/
theorem reader_follows_traversal [NoFails H]
    {h : Traversal.Handler (StateT H Id) (Handler.Error H) (valuesOf H)}
    (hA : BSmtLib.Facts.Parser.Adapters.Bridge.Agrees h) (version : Lexicon.Version)
    (slices : List Regex.Chars) (init : H) {commands : List Tree.Command}
    (hfile : File version slices.flatten commands) :
    ∃ result before after,
      readThrough (BSmtLib.Reader.script init allVersions (toVersion version)) slices =
        .ok (some result, before, after) ∧
      (Traversal.script nullPoints h nullProducer VersionPolicy.unrestricted version
        commands).run.run init = (.ok (), after.handler) := by
  obtain ⟨result, before, after, hread, items, hst, r, hr⟩ :=
    Reader.reader_reads_file version slices init hfile
  exact ⟨result, before, after, hread,
    hRun_traversal hA (Proofs.Reader.Valid.script_of_file hfile) init hst hr⟩

end BSmtLib.Facts.Proofs.Reader.Handler.Traversal

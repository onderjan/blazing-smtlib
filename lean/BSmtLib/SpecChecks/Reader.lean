import BSmtLib.Spec.Reader
import BSmtLib.SpecChecks.Parser.Bridge

/-!
# Readers

The calls for the commands of a file determine the file's version and commands: the commands
of a file make a script (`script_of_file`), the first call is the switch to the version the file
is read from, and the calls of a script's recording rebuild the script
(`Parser.recover_record`).

That a reader which lexes then parses (`Spec.Reader.LexesThenParses`) reads files and finishes
only on files is stated below (`LexesThenParsesReadsFiles`) and not proved here.

Not trusted: this is a check of the specification.
-/

namespace BSmtLib.SpecChecks.Reader

open BSmtLib.Spec BSmtLib.Spec.Lexicon BSmtLib.Spec.Grammar BSmtLib.Spec.Parser
open BSmtLib.Spec.Reader

/-- The commands of a file make a script. -/
theorem script_of_file {version : Version} {offset : Nat} {input : Chars}
    {commands : List Tree.Command} (h : FileFrom version offset input commands) :
    Script version commands := by
  induction h with
  | done => exact .done
  | command _ hic hm _ ih => exact .command hic.1 hm ih
  | stop _ hic hm => exact .stop hic.1 hm

/-- The calls for the commands of two files are equal only if the files are read from the same
version and have the same commands. -/
theorem calls_determine {version version' : Version} {input input' : Chars}
    {commands commands' : List Tree.Command} (h : File version input commands)
    (h' : File version' input' commands')
    (hc : calls version commands = calls version' commands') :
    version = version' ∧ commands = commands' := by
  have hs := script_of_file h
  have hs' := script_of_file h'
  obtain ⟨r, hr⟩ := Parser.record_head hs
  obtain ⟨r', hr'⟩ := Parser.record_head hs'
  have hv : version = version' := by
    have hc' := hc
    simp only [calls, hr, hr', List.filter_cons, Event.isCall, ↓reduceIte, List.cons.injEq,
      Event.handlerSwitch.injEq] at hc'
    exact hc'.1
  subst hv
  refine ⟨rfl, ?_⟩
  have h₁ := Parser.recover_record hs
  have h₂ := Parser.recover_record hs'
  simp only [calls] at hc
  rw [hc, h₂] at h₁
  exact (Option.some.inj h₁).symm

/-- An empty file: the handler is told the version and nothing else. -/
example : calls .v2_7 [] = [.handlerSwitch .v2_7] := rfl

/--
A reader that lexes then parses reads files and finishes only on files. Not proved here: the
proof follows a lexer that is correct with every consumer through the tokens of a file, command
by command, and is left to a later commit.
-/
def LexesThenParsesReadsFiles : Prop :=
  ∀ reader, LexesThenParses reader → ReadsFiles reader ∧ FinishesOnlyOnFiles reader

end BSmtLib.SpecChecks.Reader

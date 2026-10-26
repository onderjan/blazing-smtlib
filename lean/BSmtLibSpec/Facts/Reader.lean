module

public import BSmtLibSpec.Facts.Proofs.Reader

@[expose] public section

/-!
# Facts about readers

Readers: the calls on a file determine the file, and a reader that lexes then parses reads files
and finishes only on files.

Each theorem below proves a property of the specification, from the modules imported above.
Each is followed by the axioms its proof uses: only those of Lean's standard library, no
`sorry` and no axiom of its own. The build fails if that changes.
-/

namespace BSmtLibSpec.Facts

/-!
### Readers

The calls a reader makes on a file determine the file, but for its layout, what follows `exit`
and the spelling of strings in 2.0 (`BSmtLibSpec.Reader.CallsDetermineCommands`). A reader that is a
correct lexer with a parser that follows the traversal as its consumer
(`BSmtLibSpec.Reader.LexesThenParses`) tells its handler the calls for the commands of every file
and finishes on it (`BSmtLibSpec.Reader.ReadsFiles`), and finishes on nothing else
(`BSmtLibSpec.Reader.FinishesOnlyOnFiles`).
-/

/-- The calls for the commands of a file determine the file's initial version and its
commands. -/
theorem Reader.callsDetermineCommands : BSmtLibSpec.Reader.CallsDetermineCommands :=
  fun _ _ _ _ _ _ h h' hc => Proofs.Reader.calls_determine h h' hc

/--
info: 'BSmtLibSpec.Facts.Reader.callsDetermineCommands' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Reader.callsDetermineCommands

/-- A reader that lexes then parses reads files and finishes only on files. -/
theorem Reader.lexesThenParsesReads :
    ∀ reader, BSmtLibSpec.Reader.LexesThenParses reader →
      BSmtLibSpec.Reader.ReadsFiles reader ∧ BSmtLibSpec.Reader.FinishesOnlyOnFiles reader :=
  Proofs.Reader.lexesThenParses_reads

/--
info: 'BSmtLibSpec.Facts.Reader.lexesThenParsesReads' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Reader.lexesThenParsesReads

end BSmtLibSpec.Facts

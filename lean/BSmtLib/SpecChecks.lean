import BSmtLib.SpecChecks.Lemmas
import BSmtLib.SpecChecks.Examples
import BSmtLib.SpecChecks.Reserved
import BSmtLib.SpecChecks.Grammar
import BSmtLib.SpecChecks.Unique
import BSmtLib.SpecChecks.Streaming
import BSmtLib.SpecChecks.Grammar.Unique

/-!
# Checks of the specification

Proofs that the specification means what it says on the standard's own examples and lists,
and that every input has at most one tokenisation, with examples of what a lexer fed in slices
hands over; and that the grammar is unambiguous: every sequence of tokens of a term or of a
command has at most one syntax tree, and every script has at most one parse.
They are not part of the specification and are not trusted.
-/

/-!
## What holds

Each theorem below proves a property of the specification, from the modules imported above.
Each is followed by the axioms its proof uses: only those of Lean's standard library, no
`sorry` and no axiom of its own. The build fails if that changes.
-/

namespace BSmtLib.SpecChecks

open BSmtLib.Spec

/-- Every input has at most one tokenisation. -/
theorem Lexicon.unique : Lexicon.Unique :=
  fun _ _ _ _ h₁ h₂ => Lexicon.tokenizationFrom_unique h₁ h₂

/--
info: 'BSmtLib.SpecChecks.Lexicon.unique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexicon.unique

/-- The rules leave at most one syntax tree for every sequence of tokens of a term. -/
theorem Grammar.termsUnique : Grammar.TermsUnique :=
  fun _ _ _ _ h₁ h₂ => Grammar.Term.unique h₁ h₂ rfl

/--
info: 'BSmtLib.SpecChecks.Grammar.termsUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.termsUnique

/-- The rules leave at most one syntax tree for every sequence of tokens of a command. -/
theorem Grammar.commandsUnique : Grammar.CommandsUnique :=
  fun _ _ _ _ h₁ h₂ => Grammar.Command.unique h₁ h₂ rfl

/--
info: 'BSmtLib.SpecChecks.Grammar.commandsUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.commandsUnique

/-- Every script has at most one parse. -/
theorem Grammar.scriptsUnique : Grammar.ScriptsUnique :=
  fun _ _ _ _ h₁ h₂ => Grammar.scriptParseFrom_unique h₁ h₂

/--
info: 'BSmtLib.SpecChecks.Grammar.scriptsUnique' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Grammar.scriptsUnique

end BSmtLib.SpecChecks

import BSmtLib.SpecChecks.Lemmas
import BSmtLib.SpecChecks.Examples
import BSmtLib.SpecChecks.Reserved
import BSmtLib.SpecChecks.Grammar
import BSmtLib.SpecChecks.Unique

/-!
# Checks of the specification

Proofs that the specification means what it says on the standard's own examples and lists,
and that every input has at most one tokenisation; that the grammar is unambiguous is to come.
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

end BSmtLib.SpecChecks

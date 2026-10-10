import BSmtLib.Proofs.Lexer.VNaive
import BSmtLib.Proofs.Lexer.WRustPort
import BSmtLib.Proofs.Lexer.X1BatchInCore
import BSmtLib.Proofs.Adapter
import BSmtLib.Proofs.AdapterSteps
import BSmtLib.Proofs.Simulation
import BSmtLib.Proofs.VNaive
import BSmtLib.Proofs.VNaiveWRustPort
import BSmtLib.Proofs.WRustPortX1BatchInCore
import BSmtLib.Proofs.X1BatchInCoreLexer

/-!
# Proofs about the lexers

The chain of lexers that leads from the specification to the library's lexer, and what is
proved of them against the specification: each is `Spec.Lexer.Correct`, fed by the adapter
slices and then, if the input has ended, the end of the input. That each is then also
`Spec.Lexer.Sequential` and `Spec.Lexer.WholeInputCorrect` follows by `BSmtLib.SpecChecks`, which
proves both of every lexer that is correct.
-/

/-!
## What holds

Each theorem below proves a property of the specification of a lexer of the chain, from the
modules imported above. Each is followed by the axioms its proof uses: only those of Lean's
standard library, no `sorry` and no axiom of its own. The build fails if that changes.
-/

namespace BSmtLib.Proofs

open BSmtLib.Spec

/-- The naive lexer, fed by the adapter slices and then, if the input has ended, the end of the
input, with its consumer that takes every token and does not take whitespace and comments, is
correct. -/
theorem Lexer.VNaive.correct : Spec.Lexer.Correct (Adapter.fedInput Adapter.VNaive.ops) :=
  Lexer.VNaive.fedInput_correct

/--
info: 'BSmtLib.Proofs.Lexer.VNaive.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.VNaive.correct

/-- The Rust port, fed by the adapter slices and then, if the input has ended, the end of the
input, with its consumer that takes every token and does not take whitespace and comments, is
correct: it hands over what the naive lexer does, and fails where it does. -/
theorem Lexer.WRustPort.correct : Spec.Lexer.Correct (Adapter.fedInput Adapter.WRustPort.ops) := by
  rw [← Lexer.VNaive.fedInput_eq_fedInput_wRustPort]
  exact Lexer.VNaive.correct

/--
info: 'BSmtLib.Proofs.Lexer.WRustPort.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.WRustPort.correct

/-- The lexer with the batch kept in its state, fed by the adapter slices and then, if the input
has ended, the end of the input, with its consumer that takes every token and does not take
whitespace and comments, is correct: it hands over what the Rust port does, and fails where it
does. -/
theorem Lexer.X1BatchInCore.correct :
    Spec.Lexer.Correct (Adapter.fedInput Adapter.X1BatchInCore.ops) := by
  have e : Adapter.fedInput Adapter.WRustPort.ops = Adapter.fedInput Adapter.X1BatchInCore.ops := by
    funext version slices ended
    exact Lexer.WRustPort.fedInput_eq_fedInput_x1BatchInCore version slices ended
  rw [← e]
  exact Lexer.WRustPort.correct

/--
info: 'BSmtLib.Proofs.Lexer.X1BatchInCore.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.X1BatchInCore.correct

/-- The library's lexer, fed by the adapter slices and then, if the input has ended, the end of
the input, with its consumer that takes every token and does not take whitespace and comments,
is correct: it does for the slices what the lexer with the batch kept in its state does for
them with each slice too large for the positions of the library's lexer cut into chunks, and
the chunks make up the same input. -/
theorem Lexer.correct : Spec.Lexer.Correct (Adapter.fedInput Adapter.Lexer.ops) := by
  intro version slices ended start
  obtain ⟨e, hflat⟩ := Lexer.fedInput_eq_fedInput_x1BatchInCore version slices ended
  obtain ⟨e', -⟩ := Lexer.fedInput_eq_fedInput_x1BatchInCore version slices true
  have h := Lexer.X1BatchInCore.correct version (X1BatchInCoreLexer.Chunks.cutAll slices) ended
    start
  unfold Spec.Lexer.FailsCorrectly Spec.Lexer.HandsOverCorrectly Spec.Lexer.HandsOverAll
    Spec.Lexer.HandsOverMaximal at h ⊢
  rw [e, e', ← hflat]
  exact h

/--
info: 'BSmtLib.Proofs.Lexer.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.correct

end BSmtLib.Proofs

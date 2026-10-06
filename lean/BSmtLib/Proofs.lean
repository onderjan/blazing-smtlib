import BSmtLib.Proofs.Lexer.V1Naive
import BSmtLib.Proofs.Lexer.V2Batched
import BSmtLib.Proofs.Lexer.V3Runs
import BSmtLib.Proofs.Lexer.V4FastPaths
import BSmtLib.Proofs.Lexer.WRustPort
import BSmtLib.Proofs.Lexer.X1BatchInCore
import BSmtLib.Proofs.Lexer.X2Contents
import BSmtLib.Proofs.Adapter
import BSmtLib.Proofs.V1Naive
import BSmtLib.Proofs.V2BatchedV3Runs
import BSmtLib.Proofs.V3RunsV4FastPaths
import BSmtLib.Proofs.V1NaiveV2Batched

/-!
# Proofs about the lexers

The chain of lexers that leads from the specification to the library's lexer, and what is
proved of them against the specification.
-/

/-!
## What holds

Each theorem below proves a property of the specification of a lexer of the chain, from the
modules imported above. Each is followed by the axioms its proof uses: only those of Lean's
standard library, no `sorry` and no axiom of its own. The build fails if that changes.
-/

namespace BSmtLib.Proofs

open BSmtLib.Spec

/-- The naive lexer, run by the adapter with its consumer that takes every token and does not
take whitespace and comments, is correct on whole inputs, however they are cut into slices. -/
theorem Lexer.V1Naive.lexerCorrect :
    Spec.Lexer.LexerCorrect (Adapter.handed Adapter.V1Naive.ops) :=
  Lexer.V1Naive.lex_correct

/--
info: 'BSmtLib.Proofs.Lexer.V1Naive.lexerCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.V1Naive.lexerCorrect

/-- The batched lexer, run by the adapter with its consumer that takes every token and does not
take whitespace and comments, is correct on whole inputs, however they are cut into slices: it
hands over what the naive lexer does. -/
theorem Lexer.V2Batched.lexerCorrect :
    Spec.Lexer.LexerCorrect (Adapter.handed Adapter.V2Batched.ops) := by
  rw [← Lexer.V1Naive.handed_eq_handed_v2Batched]
  exact Lexer.V1Naive.lexerCorrect

/--
info: 'BSmtLib.Proofs.Lexer.V2Batched.lexerCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.V2Batched.lexerCorrect

/-- The lexer over runs, run by the adapter with its consumer that takes every token and does
not take whitespace and comments, is correct on whole inputs, however they are cut into slices:
it lexes every slice as the batched lexer does. -/
theorem Lexer.V3Runs.lexerCorrect :
    Spec.Lexer.LexerCorrect (Adapter.handed Adapter.V3Runs.ops) := by
  have e : Adapter.V2Batched.ops = Adapter.V3Runs.ops := by
    unfold Adapter.V2Batched.ops Adapter.V3Runs.ops
    congr 1
    funext lexer slice
    exact Lexer.V2Batched.lexSlice_eq_lexSlice_v3Runs lexer slice
  rw [← e]
  exact Lexer.V2Batched.lexerCorrect

/--
info: 'BSmtLib.Proofs.Lexer.V3Runs.lexerCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.V3Runs.lexerCorrect

/-- The lexer with fast paths, run by the adapter with its consumer that takes every token and
does not take whitespace and comments, is correct on whole inputs, however they are cut into
slices: it lexes every slice as the lexer over runs does. -/
theorem Lexer.V4FastPaths.lexerCorrect :
    Spec.Lexer.LexerCorrect (Adapter.handed Adapter.V4FastPaths.ops) := by
  have e : Adapter.V3Runs.ops = Adapter.V4FastPaths.ops := by
    unfold Adapter.V3Runs.ops Adapter.V4FastPaths.ops
    congr 1
    funext lexer slice
    exact Lexer.V3Runs.lexSlice_eq_lexSlice_v4FastPaths lexer slice
  rw [← e]
  exact Lexer.V3Runs.lexerCorrect

/--
info: 'BSmtLib.Proofs.Lexer.V4FastPaths.lexerCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.V4FastPaths.lexerCorrect

end BSmtLib.Proofs

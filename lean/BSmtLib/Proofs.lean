import BSmtLib.Proofs.Lexer.V1Naive
import BSmtLib.Proofs.Lexer.V2Batched
import BSmtLib.Proofs.Lexer.V3Runs
import BSmtLib.Proofs.Lexer.V4FastPaths
import BSmtLib.Proofs.Lexer.WRustPort
import BSmtLib.Proofs.Lexer.X1BatchInCore
import BSmtLib.Proofs.Lexer.X2Contents
import BSmtLib.Proofs.Adapter
import BSmtLib.Proofs.Simulation
import BSmtLib.Proofs.V1Naive
import BSmtLib.Proofs.V2BatchedV3Runs
import BSmtLib.Proofs.V3RunsV4FastPaths
import BSmtLib.Proofs.V1NaiveV2Batched
import BSmtLib.Proofs.X2ContentsLexer
import BSmtLib.Proofs.X1BatchInCoreX2Contents
import BSmtLib.Proofs.WRustPortX1BatchInCore
import BSmtLib.Proofs.V4FastPathsWRustPort

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

/-- The Rust port, run by the adapter with its consumer that takes every token and does not take
whitespace and comments, is correct on whole inputs, however they are cut into slices: it hands
over what the lexer with fast paths does. -/
theorem Lexer.WRustPort.lexerCorrect :
    Spec.Lexer.LexerCorrect (Adapter.handed Adapter.WRustPort.ops) := by
  rw [← Lexer.V4FastPaths.handed_eq_handed_wRustPort]
  exact Lexer.V4FastPaths.lexerCorrect

/--
info: 'BSmtLib.Proofs.Lexer.WRustPort.lexerCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.WRustPort.lexerCorrect

/-- The lexer with the batch kept in its state, run by the adapter with its consumer that takes
every token and does not take whitespace and comments, is correct on whole inputs, however they
are cut into slices: it hands over what the Rust port does. -/
theorem Lexer.X1BatchInCore.lexerCorrect :
    Spec.Lexer.LexerCorrect (Adapter.handed Adapter.X1BatchInCore.ops) := by
  have e : Adapter.handed Adapter.WRustPort.ops = Adapter.handed Adapter.X1BatchInCore.ops := by
    funext version slices
    exact Lexer.WRustPort.handed_eq_handed_x1BatchInCore version slices
  rw [← e]
  exact Lexer.WRustPort.lexerCorrect

/--
info: 'BSmtLib.Proofs.Lexer.X1BatchInCore.lexerCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.X1BatchInCore.lexerCorrect

/-- The lexer with the content buffer, run by the adapter with its consumer that takes every
token and does not take whitespace and comments, is correct on whole inputs, however they are
cut into slices: it hands over what the lexer with the batch kept in its state does. -/
theorem Lexer.X2Contents.lexerCorrect :
    Spec.Lexer.LexerCorrect (Adapter.handed Adapter.X2Contents.ops) := by
  rw [← Lexer.X1BatchInCore.handed_eq_handed_x2Contents]
  exact Lexer.X1BatchInCore.lexerCorrect

/--
info: 'BSmtLib.Proofs.Lexer.X2Contents.lexerCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.X2Contents.lexerCorrect

/-- The library's lexer, run by the adapter with its consumer that takes every token and does
not take whitespace and comments, is correct on whole inputs, however they are cut into slices:
it hands over for the slices what it hands over for them cut into chunks short enough for its
positions, which is what the lexer with the content buffer hands over for the chunks, and the
chunks make up the same input. -/
theorem Lexer.lexerCorrect :
    Spec.Lexer.LexerCorrect (Adapter.handed Adapter.Lexer.ops) := by
  intro version slices handed
  obtain ⟨e, hflat, hb⟩ := Lexer.handed_eq_handed_cutAll version slices
  rw [e, ← Lexer.X2Contents.handed_eq_handed_lexer version _ hb]
  have h := Lexer.X2Contents.lexerCorrect version (X2ContentsLexer.Chunks.cutAll slices) handed
  simp only [hflat] at h
  exact h

/--
info: 'BSmtLib.Proofs.Lexer.lexerCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.lexerCorrect

end BSmtLib.Proofs

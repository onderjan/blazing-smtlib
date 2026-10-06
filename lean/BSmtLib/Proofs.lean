import BSmtLib.Proofs.Lexer.V1Naive
import BSmtLib.Proofs.Lexer.WRustPort
import BSmtLib.Proofs.Lexer.X1BatchInCore
import BSmtLib.Proofs.Adapter
import BSmtLib.Proofs.AdapterSteps
import BSmtLib.Proofs.Simulation
import BSmtLib.Proofs.V1Naive
import BSmtLib.Proofs.V1NaiveWRustPort
import BSmtLib.Proofs.WRustPortX1BatchInCore
import BSmtLib.Proofs.X1BatchInCoreLexer

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

/-- The naive lexer, fed slices by the adapter with its consumer that takes every token and does
not take whitespace and comments, before the end of the input, has failed exactly when the input
is not viable, and has handed over the tokens maximal to hand over on its longest viable start. -/
theorem Lexer.V1Naive.streamingInputCorrect (version : Lexicon.Version)
    (slices : List Lexicon.Chars) (start : Lexicon.Chars) :
    Spec.Lexer.StreamingInputCorrect (Adapter.fed Adapter.V1Naive.ops) version slices start :=
  Lexer.V1Naive.streaming_correct version slices start

/--
info: 'BSmtLib.Proofs.Lexer.V1Naive.streamingInputCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.V1Naive.streamingInputCorrect

/-- The naive lexer, run and fed slices by the adapter with its consumer that takes every token and
does not take whitespace and comments, is correct on whole inputs and fed in slices. -/
theorem Lexer.V1Naive.correct :
    Spec.Lexer.Correct (Adapter.handed Adapter.V1Naive.ops) (Adapter.fed Adapter.V1Naive.ops) :=
  fun version slices handed start =>
    ⟨Lexer.V1Naive.lexerCorrect version slices handed,
      Lexer.V1Naive.streamingInputCorrect version slices start⟩

/--
info: 'BSmtLib.Proofs.Lexer.V1Naive.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.V1Naive.correct

/-- The Rust port, run by the adapter with its consumer that takes every token and does not take
whitespace and comments, is correct on whole inputs, however they are cut into slices: it hands
over what the naive lexer does. -/
theorem Lexer.WRustPort.lexerCorrect :
    Spec.Lexer.LexerCorrect (Adapter.handed Adapter.WRustPort.ops) := by
  rw [← Lexer.V1Naive.handed_eq_handed_wRustPort]
  exact Lexer.V1Naive.lexerCorrect

/--
info: 'BSmtLib.Proofs.Lexer.WRustPort.lexerCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.WRustPort.lexerCorrect

/-- The Rust port, run and fed slices by the adapter with its consumer that takes every token and
does not take whitespace and comments, is correct on whole inputs and fed in slices: it hands
over what the naive lexer does, and fails where it does. -/
theorem Lexer.WRustPort.correct :
    Spec.Lexer.Correct (Adapter.handed Adapter.WRustPort.ops)
      (Adapter.fed Adapter.WRustPort.ops) := by
  rw [← Lexer.V1Naive.handed_eq_handed_wRustPort, ← Lexer.V1Naive.fed_eq_fed_wRustPort]
  exact Lexer.V1Naive.correct

/--
info: 'BSmtLib.Proofs.Lexer.WRustPort.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.WRustPort.correct

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

/-- The lexer with the batch kept in its state, run and fed slices by the adapter with its
consumer that takes every token and does not take whitespace and comments, is correct on whole
inputs and fed in slices: it hands over what the Rust port does, and fails where it does. -/
theorem Lexer.X1BatchInCore.correct :
    Spec.Lexer.Correct (Adapter.handed Adapter.X1BatchInCore.ops)
      (Adapter.fed Adapter.X1BatchInCore.ops) := by
  have e : Adapter.handed Adapter.WRustPort.ops = Adapter.handed Adapter.X1BatchInCore.ops := by
    funext version slices
    exact Lexer.WRustPort.handed_eq_handed_x1BatchInCore version slices
  have f : Adapter.fed Adapter.WRustPort.ops = Adapter.fed Adapter.X1BatchInCore.ops := by
    funext version slices
    exact Lexer.WRustPort.fed_eq_fed_x1BatchInCore version slices
  rw [← e, ← f]
  exact Lexer.WRustPort.correct

/--
info: 'BSmtLib.Proofs.Lexer.X1BatchInCore.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.X1BatchInCore.correct

/-- The library's lexer, run by the adapter with its consumer that takes every token and does
not take whitespace and comments, is correct on whole inputs, however they are cut into slices:
it hands over for the slices what the lexer with the batch kept in its state hands over for them
with each slice too large for the positions of the library's lexer cut into chunks, and the
chunks make up the same input. -/
theorem Lexer.lexerCorrect :
    Spec.Lexer.LexerCorrect (Adapter.handed Adapter.Lexer.ops) := by
  intro version slices handed
  obtain ⟨e, hflat⟩ := Lexer.handed_eq_handed_x1BatchInCore version slices
  rw [e]
  have h := Lexer.X1BatchInCore.lexerCorrect version (X1BatchInCoreLexer.Chunks.cutAll slices)
    handed
  simp only [hflat] at h
  exact h

/--
info: 'BSmtLib.Proofs.Lexer.lexerCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.lexerCorrect

/-- The library's lexer, run and fed slices by the adapter with its consumer that takes every
token and does not take whitespace and comments, is correct on whole inputs and fed in slices:
it does for the slices what the lexer with the batch kept in its state does for them with each
slice too large for the positions of the library's lexer cut into chunks, and the chunks make up
the same input. -/
theorem Lexer.correct :
    Spec.Lexer.Correct (Adapter.handed Adapter.Lexer.ops) (Adapter.fed Adapter.Lexer.ops) := by
  intro version slices handed start
  refine ⟨Lexer.lexerCorrect version slices handed, ?_⟩
  obtain ⟨e, hflat⟩ := Lexer.fed_eq_fed_x1BatchInCore version slices
  have h := (Lexer.X1BatchInCore.correct version (X1BatchInCoreLexer.Chunks.cutAll slices) []
    start).2
  simp only [Spec.Lexer.StreamingInputCorrect, Spec.Lexer.FailsCorrectly,
    Spec.Lexer.HandsOverCorrectly, hflat, ← e] at h ⊢
  exact h

/--
info: 'BSmtLib.Proofs.Lexer.correct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.correct

end BSmtLib.Proofs

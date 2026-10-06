import BSmtLib.Proofs.Lexer.V1Naive
import BSmtLib.Proofs.Lexer.WRustPort
import BSmtLib.Proofs.Lexer.X1BatchInCore
import BSmtLib.Proofs.Adapter
import BSmtLib.Proofs.Simulation
import BSmtLib.Proofs.V1Naive
import BSmtLib.Proofs.V1NaiveWRustPort
import BSmtLib.Proofs.WRustPortX1BatchInCore

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

/-
Currently broken: the theorem below rests on the link between the lexers, which the change of
the lexers' code broke: `X2ContentsLexer` (the library's lexer against the lexer with the
content buffer, which is now the lexer with the batch kept in its state). Its modules are not
imported until they are proved again.

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
-/

end BSmtLib.Proofs

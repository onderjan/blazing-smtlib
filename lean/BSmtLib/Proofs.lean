import BSmtLib.Proofs.Lexer.V1Naive
import BSmtLib.Proofs.Lexer.V2Batched
import BSmtLib.Proofs.Lexer.V3Runs
import BSmtLib.Proofs.Lexer.V4FastPaths
import BSmtLib.Proofs.V1Naive

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

/-- The naive lexer, with a consumer that takes every token and does not take whitespace and
comments, is correct on whole inputs, however they are cut into slices. -/
theorem Lexer.V1Naive.lexerCorrect : Spec.Lexer.LexerCorrect V1Spec.lex :=
  Lexer.V1Naive.lex_correct

/--
info: 'BSmtLib.Proofs.Lexer.V1Naive.lexerCorrect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lexer.V1Naive.lexerCorrect

end BSmtLib.Proofs

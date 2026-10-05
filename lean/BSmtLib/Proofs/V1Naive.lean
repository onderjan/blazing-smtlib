import BSmtLib.Proofs.V1Naive.Correct

/-!
# The naive lexer against the specification

The proof that the naive lexer `Lexer.V1Naive`, as the adapter `Adapter.handed` runs it, is
correct on whole inputs, in parts:

- `V1Naive.Run`: the lexing as a pure run over the bytes, whatever the slices;
- `V1Naive.Facts`: the byte classes and the locations;
- `V1Naive.Modes`: what each mode of a token in progress stands for;
- `V1Naive.Sound` and `V1Naive.Complete`: the run hands over exactly the tokenisations;
- `V1Naive.Reserved`: the lookup of reserved words;
- `V1Naive.Correct`: the assembly.
-/

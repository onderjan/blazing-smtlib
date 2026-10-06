import BSmtLib.Proofs.V1Naive.Correct
import BSmtLib.Proofs.V1Naive.Streaming

/-!
# The naive lexer against the specification

The proof that the naive lexer `Lexer.V1Naive`, as the adapter `Adapter.handed` runs it, is
correct on whole inputs, and as the adapter `Adapter.fed` feeds it slices, correct before the
end of the input, in parts:

- `V1Naive.Run`: the lexing as a pure run over the bytes, whatever the slices, also up to an
  error;
- `V1Naive.Facts`: the byte classes and the locations;
- `V1Naive.Modes`: what each mode of a token in progress stands for;
- `V1Naive.Sound` and `V1Naive.Complete`: the run hands over exactly the tokenisations;
- `V1Naive.Reserved`: the lookup of reserved words;
- `V1Naive.Correct`: the assembly for whole inputs;
- `V1Naive.Prefix`: the run over a start of the input: the lexemes the consumer takes, where
  they end, and the completion of every state to an input that the run finishes;
- `V1Naive.Streaming`: the assembly for slices before the end of the input.
-/

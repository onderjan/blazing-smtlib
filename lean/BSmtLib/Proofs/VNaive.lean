import BSmtLib.Proofs.VNaive.Correct
import BSmtLib.Proofs.VNaive.Streaming

/-!
# The naive lexer against the specification

The proof that the naive lexer `Lexer.VNaive`, as the adapter `Adapter.handed` runs it, is
correct on whole inputs, and as the adapter `Adapter.fed` feeds it slices, correct before the
end of the input, in parts:

- `VNaive.Run`: the lexing as a pure run over the bytes, whatever the slices, also up to an
  error;
- `VNaive.Facts`: the byte classes and the locations;
- `VNaive.Modes`: what each mode of a token in progress stands for;
- `VNaive.Sound` and `VNaive.Complete`: the run hands over exactly the tokenisations;
- `VNaive.Reserved`: the lookup of reserved words;
- `VNaive.Correct`: the assembly for whole inputs;
- `VNaive.Prefix`: the run over a start of the input: the lexemes the consumer takes, where
  they end, and the completion of every state to an input that the run finishes;
- `VNaive.Streaming`: the assembly for slices before the end of the input.
-/

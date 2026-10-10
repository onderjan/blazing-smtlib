import BSmtLib.Proofs.VNaive.Streaming

/-!
# The naive lexer against the specification

The proof that the naive lexer `Lexer.VNaive`, as the adapter `Adapter.fedInput` feeds it slices
and then, if the input has ended, the end of the input, is correct, in parts:

- `VNaive.Run`: the lexing as a pure run over the bytes, whatever the slices, also up to an
  error, and then the end of the input;
- `VNaive.Facts`: the byte classes and the locations;
- `VNaive.Modes`: what each mode of a token in progress stands for;
- `VNaive.Sound` and `VNaive.Complete`: the run of the whole input hands over exactly the
  tokenisations;
- `VNaive.Reserved`: the lookup of reserved words;
- `VNaive.Prefix`: the run over a start of the input: the lexemes the consumer takes, where
  they end, and the completion of every state to an input that the run finishes;
- `VNaive.Streaming`: what the consumer records of the tokens, and the assembly, before the end
  of the input and after it.
-/

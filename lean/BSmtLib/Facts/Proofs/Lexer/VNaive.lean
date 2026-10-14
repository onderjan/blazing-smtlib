import BSmtLib.Facts.Proofs.Lexer.VNaive.Streaming

/-!
# The naive lexer against the specification

The proof that the pure run of the naive lexer `Lexer.VNaive`, over slices and then, if the input
has ended, the end of the input (`VNaive.fedRun`), is correct, in parts:

- `VNaive.Run`: the lexing as a pure run over the bytes, whatever the slices, also up to an
  error, and then the end of the input;
- `VNaive.Facts`: the byte classes and the locations;
- `VNaive.Modes`: what each mode of a token in progress stands for;
- `VNaive.Sound` and `VNaive.Complete`: the run of the whole input hands over exactly the
  tokenisations;
- `VNaive.Reserved`: the lookup of reserved words;
- `VNaive.Prefix`: the run over a start of the input: the lexemes it hands over, where they end,
  and the completion of every state to an input that the run finishes;
- `VNaive.Streaming`: the tokens the run hands over, and the assembly, before the end of the
  input and after it.
-/

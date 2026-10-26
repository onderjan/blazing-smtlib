module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls

@[expose] public section

/-!
# The naive lexer and the Rust port with every consumer

`VNaiveWRustPort.lexing_wRustPort_vNaive`: what the adapter makes of the Rust port `WRustPort` with
every consumer of the specification formalism (`BSmtLibSpec`) is what it makes of the naive lexer
`VNaive` (`Adapters.lexing`), however the input is cut into slices. The two cut their hand-overs
differently: the Rust port lexes a whole slice ahead into one batch, and hands a token in progress
at a slice's end over alone. So the proof compares the Rust port's code, run with the adapter's
consumer, with the naive lexer's pure run over the bytes it consumes: the Rust port's lexer state is
the naive lexer's pure state at the index of the slice it has reached, with the lexemes of its batch
still to be handed over. In parts:

- `VNaiveWRustPort.Bytes`, `Tables`, `Runs`, `Pure`: runs and bytes of a slice, the Rust port's
  byte tables and run scans against the naive lexer's byte classes, cursors and contents, and the
  locations of the indices of a slice;
- `VNaiveWRustPort.WP`: weakest preconditions for the Rust port's monad with the adapter's
  consumer;
- `VNaiveWRustPort.Model`, `Cursor`, `Consume`: what the adapter's consumer does with the lexemes
  handed over, and with a cursor over a batch that holds them (`Batch`);
- `VNaiveWRustPort.HandOver`, `Agree`, `Feed`, `Step`, `Push`: the hand-overs of a cursor, the
  correspondence of the lexer states, the naive lexer's pure run over a slice from an index, what
  a step keeps, and the hand-overs of batches and tokens;
- `VNaiveWRustPort.StartWs`, `Normal`, `NormalStep`: the step in the normal state, with its fast
  paths, by induction on the bytes left;
- `VNaiveWRustPort.Arms`, `ArmsNumbers`, `ArmsQuoted`, `ArmsRuns`, `ArmsStrings`, `ArmsWs`,
  `LexStep`: the steps for a token in progress, and the step in every state;
- `VNaiveWRustPort.Slice`, `Loop`, `EofModel`, `Eof`: the loop over a slice up to a
  stop of the consumer, the loop over the stops, and the end of the input;
- `VNaiveWRustPort.VHand`, `VOut`, `VBytes`, `VEof`: what the naive lexer does with the same
  lexemes and bytes, as the outcome of the pure run says;
- `VNaiveWRustPort.Taken`: what the pure run finishes for a consumer that does not take
  whitespace and comments, which the consumer takes, so that it never stops at them;
- `VNaiveWRustPort.Calls`: the calls of the two lexers, and what the adapter makes of them; and
  that the Rust port's calls never fail with the adapter's error for whitespace or a comment
  handed to a consumer that does not take them (`slice_step_noNone`, `eof_step_noNone`).
-/

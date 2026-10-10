import BSmtLib.Proofs.VNaiveWRustPort.Run

/-!
# The naive lexer and the Rust port as the spec sees them

`Lexer.VNaive.fedInput_eq_fedInput_wRustPort`: the naive lexer `VNaive` and the Rust port
`WRustPort`, fed by the adapter slices and then, if the input has ended, the end of the input,
hand over the same tokens and fail alike, however the input is cut into slices. The two cut
their hand-overs differently: the Rust port lexes a whole slice ahead into one batch, and hands
a token in progress at a slice's end over alone. So only what the adapter's consumer records is
equal; both record what the naive lexer's pure run over the bytes of the slices and then its end
of the input give, also up to an error (`VNaive.fedOf`): the naive lexer by
`VNaive.fedOf_fedInput`, the Rust port by `VNaiveWRustPort.fedInput_eq_run`.

The Rust port's part is proved slice by slice: after any slices the Rust port fed them by its
step run, which gives the lexer back also when a call fails, has handed over what the naive
lexer's pure run over their bytes finishes, also up to an error, and has failed exactly when that
run fails or the consumer fails on a lexeme (`VNaiveWRustPort.fedSteps_eq`). The end of the input
then finishes as the naive lexer's end of the input, and when that fails, it hands over nothing
more (`VNaiveWRustPort.feedEnd_ops`).

The proof that the Rust port records the naive lexer's pure run compares the Rust port's code,
run with the adapter's consumer, with the naive lexer's pure run over the bytes it consumes:
the Rust port's lexer state is the naive lexer's pure state at the index of the slice it has
reached, with the lexemes of its batch still to be handed over. In parts:

- `VNaiveWRustPort.Bytes`, `Cursor`: runs and bytes of a slice, the naive lexer's steps
  over a run, cursors, and what the consumer records;
- `VNaiveWRustPort.Feed`: the naive lexer's pure run over a slice from an index, and what
  the consumer is left with at the end of the slice;
- `VNaiveWRustPort.WP`: weakest preconditions for the Rust port's monad with the adapter's
  consumer, whose interruptions are errors;
- `VNaiveWRustPort.Batch`, `HandOver`, `NoStop`: the Rust port's batch, the hand-overs of
  batches and tokens to the consumer, and that the consumer never stops a hand-over;
- `VNaiveWRustPort.Agree`, `Step`: the correspondence of the lexer states and what a step
  keeps;
- `VNaiveWRustPort.Tables`, `Runs`, `Pure`: the Rust port's byte tables and run scans
  against the naive lexer's byte classes, and the naive lexer's pure run over runs of bytes;
- `VNaiveWRustPort.Normal`, `NormalStep`: the step in the normal state, with its fast
  paths, by induction on the bytes left;
- `VNaiveWRustPort.Arms`, `ArmsRuns`, `ArmsNumbers`, `ArmsQuoted`, `ArmsStrings`,
  `LexStep`: the steps for a token in progress, and the step in every state;
- `VNaiveWRustPort.Slice`, `Eof`, `Run`: the loop over a slice, the end of the input, the
  calls of the step run, the feeding of the slices one at a time, and the adapter's feeding of
  the slices and the end of the input.
-/

namespace BSmtLib.Proofs.Lexer

open BSmtLib.Proofs.Adapter

/-- The naive lexer and the Rust port, fed by the adapter slices and then, if the input has
ended, the end of the input, hand over the same tokens and fail alike. -/
theorem VNaive.fedInput_eq_fedInput_wRustPort :
    fedInput Adapter.VNaive.ops = fedInput Adapter.WRustPort.ops := by
  funext version slices ended
  rw [VNaiveWRustPort.fedInput_eq_run version slices ended _ _
    (VNaive.fedOf_fedInput version slices ended)]

/--
info: 'BSmtLib.Proofs.Lexer.VNaive.fedInput_eq_fedInput_wRustPort' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VNaive.fedInput_eq_fedInput_wRustPort

end BSmtLib.Proofs.Lexer

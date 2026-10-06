import BSmtLib.Proofs.VNaiveWRustPort.Run

/-!
# The naive lexer and the Rust port as the spec sees them

`Lexer.VNaive.handed_eq_handed_wRustPort`: the naive lexer `VNaive` and the Rust port
`WRustPort`, run by the adapter, hand over the same tokens, however the input is cut into
slices. The two cut their hand-overs differently: the Rust port lexes a whole slice ahead into
one batch, and hands a token in progress at a slice's end over alone. So only what the
adapter's consumer records is equal; both record what the naive lexer's pure run `VNaive.run`
finishes: the naive lexer by `VNaive.handed_eq_run`, the Rust port by
`VNaiveWRustPort.handed_eq_run`.

The Rust port's part is proved slice by slice: after any slices, before the end of the input,
the Rust port fed them by its step run, which gives the lexer back also when a call fails, has
handed over what the naive lexer's pure run over their bytes finishes, also up to an error, and
has failed exactly when that run fails or the consumer fails on a lexeme
(`VNaiveWRustPort.fedSteps_new`). So the two lexers fed slices by the adapter before the end
of the input have done the same (`Lexer.VNaive.fed_eq_fed_wRustPort`), as the naive lexer has
done what its pure run gives too (`VNaive.fedOf_fed`). The whole input follows from it with
the end of the input.

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
  calls of the step run and of the adapter, the feeding of the slices one at a time, and the
  adapter's feeding of the whole input.
-/

namespace BSmtLib.Proofs.Lexer

open BSmtLib.Proofs.Adapter

/-- The naive lexer and the Rust port, run by the adapter, hand over the same tokens. -/
theorem VNaive.handed_eq_handed_wRustPort :
    handed Adapter.VNaive.ops = handed Adapter.WRustPort.ops := by
  funext version slices
  rw [VNaive.handed_eq_run, VNaiveWRustPort.handed_eq_run]

/--
info: 'BSmtLib.Proofs.Lexer.VNaive.handed_eq_handed_wRustPort' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VNaive.handed_eq_handed_wRustPort

/--
info: 'BSmtLib.Proofs.Lexer.VNaiveWRustPort.fedSteps_new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VNaiveWRustPort.fedSteps_new

/-- The naive lexer and the Rust port, fed slices by the adapter before the end of the input,
hand over the same tokens and fail alike. -/
theorem VNaive.fed_eq_fed_wRustPort : fed Adapter.VNaive.ops = fed Adapter.WRustPort.ops := by
  funext version slices
  rw [VNaiveWRustPort.fed_eq_run version slices _ _ (VNaive.fedOf_fed version slices)]

/--
info: 'BSmtLib.Proofs.Lexer.VNaive.fed_eq_fed_wRustPort' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VNaive.fed_eq_fed_wRustPort

end BSmtLib.Proofs.Lexer

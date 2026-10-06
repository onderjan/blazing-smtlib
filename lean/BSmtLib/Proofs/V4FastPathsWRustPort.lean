import BSmtLib.Proofs.V4FastPathsWRustPort.Run

/-!
# The naive lexer and the Rust port as the spec sees them

`Lexer.V1Naive.handed_eq_handed_wRustPort`: the naive lexer `V1Naive` and the Rust port
`WRustPort`, run by the adapter, hand over the same tokens, however the input is cut into
slices. The two cut their hand-overs differently: the Rust port lexes a whole slice ahead into
one batch, and hands a token in progress at a slice's end over alone. So only what the
adapter's consumer records is equal; both record what the naive lexer's pure run `V1Naive.run`
finishes: the naive lexer by `V1Naive.handed_eq_run`, the Rust port by
`V4FastPathsWRustPort.handed_eq_run`.

The proof that the Rust port records the naive lexer's pure run compares the Rust port's code,
run with the adapter's consumer, with the naive lexer's pure run over the bytes it consumes:
the Rust port's lexer state is the naive lexer's pure state at the index of the slice it has
reached, with the lexemes of its batch still to be handed over. In parts:

- `V4FastPathsWRustPort.Bytes`, `Cursor`: runs and bytes of a slice, the naive lexer's steps
  over a run, cursors, and what the consumer records;
- `V4FastPathsWRustPort.Feed`: the naive lexer's pure run over a slice from an index, and what
  the consumer is left with at the end of the slice;
- `V4FastPathsWRustPort.WP`: weakest preconditions for the Rust port's monad with the adapter's
  consumer, whose interruptions are errors;
- `V4FastPathsWRustPort.Batch`, `HandOver`, `NoStop`: the Rust port's batch, the hand-overs of
  batches and tokens to the consumer, and that the consumer never stops a hand-over;
- `V4FastPathsWRustPort.Agree`, `Step`: the correspondence of the lexer states and what a step
  keeps;
- `V4FastPathsWRustPort.Tables`, `Runs`, `Pure`: the Rust port's byte tables and run scans
  against the naive lexer's byte classes, and the naive lexer's pure run over runs of bytes;
- `V4FastPathsWRustPort.Normal`, `NormalStep`: the step in the normal state, with its fast
  paths, by induction on the bytes left;
- `V4FastPathsWRustPort.Arms`, `ArmsRuns`, `ArmsNumbers`, `ArmsQuoted`, `ArmsStrings`,
  `LexStep`: the steps for a token in progress, and the step in every state;
- `V4FastPathsWRustPort.Slice`, `Eof`, `Run`: the loop over a slice, the end of the input, the
  calls of the adapter, and the adapter's feeding of the slices.
-/

namespace BSmtLib.Proofs.Lexer

open BSmtLib.Proofs.Adapter

/-- The naive lexer and the Rust port, run by the adapter, hand over the same tokens. -/
theorem V1Naive.handed_eq_handed_wRustPort :
    handed Adapter.V1Naive.ops = handed Adapter.WRustPort.ops := by
  funext version slices
  rw [V1Naive.handed_eq_run, V4FastPathsWRustPort.handed_eq_run]

/--
info: 'BSmtLib.Proofs.Lexer.V1Naive.handed_eq_handed_wRustPort' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms V1Naive.handed_eq_handed_wRustPort

end BSmtLib.Proofs.Lexer

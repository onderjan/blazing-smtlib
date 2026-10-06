import BSmtLib.Proofs.V1NaiveWRustPort.Run

/-!
# The naive lexer and the Rust port as the spec sees them

`Lexer.V1Naive.handed_eq_handed_wRustPort`: the naive lexer `V1Naive` and the Rust port
`WRustPort`, run by the adapter, hand over the same tokens, however the input is cut into
slices. The two cut their hand-overs differently: the Rust port lexes a whole slice ahead into
one batch, and hands a token in progress at a slice's end over alone. So only what the
adapter's consumer records is equal; both record what the naive lexer's pure run `V1Naive.run`
finishes: the naive lexer by `V1Naive.handed_eq_run`, the Rust port by
`V1NaiveWRustPort.handed_eq_run`.

The Rust port's part is proved slice by slice: after any slices, before the end of the input,
the Rust port fed them by its step run, which gives the lexer back also when a call fails, has
handed over what the naive lexer's pure run over their bytes finishes, and has failed exactly
when that run fails or the consumer fails on a lexeme (`V1NaiveWRustPort.fedSteps_new`). The
whole input follows from it with the end of the input.

The proof that the Rust port records the naive lexer's pure run compares the Rust port's code,
run with the adapter's consumer, with the naive lexer's pure run over the bytes it consumes:
the Rust port's lexer state is the naive lexer's pure state at the index of the slice it has
reached, with the lexemes of its batch still to be handed over. In parts:

- `V1NaiveWRustPort.Bytes`, `Cursor`: runs and bytes of a slice, the naive lexer's steps
  over a run, cursors, and what the consumer records;
- `V1NaiveWRustPort.Feed`: the naive lexer's pure run over a slice from an index, and what
  the consumer is left with at the end of the slice;
- `V1NaiveWRustPort.WP`: weakest preconditions for the Rust port's monad with the adapter's
  consumer, whose interruptions are errors;
- `V1NaiveWRustPort.Batch`, `HandOver`, `NoStop`: the Rust port's batch, the hand-overs of
  batches and tokens to the consumer, and that the consumer never stops a hand-over;
- `V1NaiveWRustPort.Agree`, `Step`: the correspondence of the lexer states and what a step
  keeps;
- `V1NaiveWRustPort.Tables`, `Runs`, `Pure`: the Rust port's byte tables and run scans
  against the naive lexer's byte classes, and the naive lexer's pure run over runs of bytes;
- `V1NaiveWRustPort.Normal`, `NormalStep`: the step in the normal state, with its fast
  paths, by induction on the bytes left;
- `V1NaiveWRustPort.Arms`, `ArmsRuns`, `ArmsNumbers`, `ArmsQuoted`, `ArmsStrings`,
  `LexStep`: the steps for a token in progress, and the step in every state;
- `V1NaiveWRustPort.Slice`, `Eof`, `Run`: the loop over a slice, the end of the input, the
  calls of the step run and of the adapter, the feeding of the slices one at a time, and the
  adapter's feeding of the whole input.
-/

namespace BSmtLib.Proofs.Lexer

open BSmtLib.Proofs.Adapter

/-- The naive lexer and the Rust port, run by the adapter, hand over the same tokens. -/
theorem V1Naive.handed_eq_handed_wRustPort :
    handed Adapter.V1Naive.ops = handed Adapter.WRustPort.ops := by
  funext version slices
  rw [V1Naive.handed_eq_run, V1NaiveWRustPort.handed_eq_run]

/--
info: 'BSmtLib.Proofs.Lexer.V1Naive.handed_eq_handed_wRustPort' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms V1Naive.handed_eq_handed_wRustPort

/--
info: 'BSmtLib.Proofs.Lexer.V1NaiveWRustPort.fedSteps_new' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms V1NaiveWRustPort.fedSteps_new

end BSmtLib.Proofs.Lexer

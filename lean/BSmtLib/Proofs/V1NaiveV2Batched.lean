import BSmtLib.Proofs.V1NaiveV2Batched.Run

/-!
# The naive lexer and the batched lexer as the spec sees them

`Lexer.V1Naive.handed_eq_handed_v2Batched`: the naive lexer `V1Naive` and the batched lexer
`V2Batched`, run by the adapter, hand over the same tokens, however the input is cut into
slices. The two cut their hand-overs differently, so only what the adapter's consumer records
is equal; both record what the naive lexer's pure run `V1Naive.run` finishes.

The proof, in parts:

- `V1NaiveV2Batched.Cursor`: what a batch of lexemes holds, and that a cursor over it reports
  each token as the naive lexer reports the lexeme alone;
- `V1NaiveV2Batched.HandOver`: the consumer handed a cursor over a batch;
- `V1NaiveV2Batched.Run`: the batched lexer against the naive lexer's pure run.
-/

namespace BSmtLib.Proofs.Lexer

open BSmtLib.Proofs.Adapter

/-- The naive lexer and the batched lexer, run by the adapter, hand over the same tokens. -/
theorem V1Naive.handed_eq_handed_v2Batched :
    handed Adapter.V1Naive.ops = handed Adapter.V2Batched.ops := by
  funext version slices
  rw [V1Naive.handed_eq_run, V1NaiveV2Batched.handed_eq_run]

end BSmtLib.Proofs.Lexer

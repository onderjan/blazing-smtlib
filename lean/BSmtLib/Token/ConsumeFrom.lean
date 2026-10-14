import BSmtLib.Token.Produce

/-!
# Consumers of a producer

The class of the consumers that take the tokens of a producer (`SmtConsumeFrom`).
-/

namespace BSmtLib.Token.ConsumeFrom

/- LEAN: Rust's `SmtConsumeFrom<Z: SmtProduce>: SmtConsume`. The supertrait is the instance
argument `Consume H R E`, which fixes the result and the error; the monad `m` is a parameter
marked `outParam`, as the consumer type determines it. A lexer requires the class for the
cursors of all its batches, as Rust requires `for<'a> SmtConsumeFrom<SmtBatchCursor<'a>>`. The
Rust blanket `impl SmtConsumeFrom<Z> for &mut T` has no counterpart, as Lean has no
references. -/
/-- A sequential consumer of tokens for given producers. -/
class _root_.BSmtLib.Token.ConsumeFrom (H Z : Type) (m : outParam (Type → Type))
    {R E : outParam Type} [Consume H R E]
    [Produce Z] where
  /- LEAN: Rust's `consume(&mut self, cursor: &mut Z)`. The consumer's state is the state of the
  monad, and the producer is handed over with the proof that it has a token and given back with
  the proof that the consumer consumed at least one token of it: the two obligations that Rust
  states in words and checks with a panic. -/
  /--
  Consumes the tokens handed over in the producer, in order.

  The caller ensures that the producer contains at least one token.
  The consumer ensures that at least one token is consumed before
  return, no matter the result (even when returning an error).

  If the consumer returns `ControlFlow.continue`, the consumer is
  not finished yet and is ready to consume more tokens. Tokens that
  remain unconsumed in the producer must be handed over again before
  any new ones.

  If the consumer returns `ControlFlow.break`, it has finished
  consuming the current value, is returning a result, and is ready
  to start consuming a new value.

  If the consumer returns an error, it has failed at the last
  consumed token. The state of the consumer is unspecified.
  -/
  consume : (producer : Z) → Produce.HasNext producer →
    StateT H m (Except E (ControlFlow R) × { next : Z // Produce.Consumed next producer })


end BSmtLib.Token.ConsumeFrom

module

public import BSmtLib.Token.Cursor

public section

/-!
# Consumers of a producer

The class of the consumers that take the tokens of a producer.
-/

namespace BSmtLib.Token.ConsumeFrom

/- LEAN: Rust's `SmtConsumeFrom<Z: SmtCursor>: SmtConsume`. The supertrait is the instance
argument `Consume H R E`, which fixes the result and the error; the monad `m` is a parameter
marked `outParam`, as the consumer type determines it. A lexer requires the class for the
cursors of all its batches, as Rust requires `for<'a> SmtConsumeFrom<SmtLexerCursor<'a>>`. The
Rust blanket `impl SmtConsumeFrom<Z> for &mut T` has no counterpart, as Lean has no
references. -/
/--
Consumes tokens sequentially from the given cursor.

It takes an instance of `Consume`, which defines the cursor result and error types and whether
the consumer is concrete. If the consumer does not use cursor-specific data such as token
locations from `Lexer.Cursor.LexerCursor`, `ConsumeFrom` can be implemented generically over all
cursors.
-/
class _root_.BSmtLib.Token.ConsumeFrom (H Z : Type) (m : outParam (Type → Type))
    {R E : outParam Type} [Consume H R E]
    [Cursor Z] where
  /- LEAN: Rust's `consume(&mut self, cursor: &mut Z)`. The consumer's state is the state of the
  monad, and the producer is handed over with the proof that it has a token and given back with
  the proof that the consumer consumed at least one token of it: the two obligations that Rust
  states in words and checks with a panic. -/
  /--
  Consumes the tokens handed over in the cursor, in order.

  The caller must ensure that the cursor contains at least one token.
  The consumer must ensure that at least one token is consumed before
  return, no matter the result (even when returning an error).

  If the consumer returns `ControlFlow.continue`, the consumer is
  not finished yet and is ready to consume more tokens. Tokens that
  remain unconsumed in the cursor must be handed over again before
  any new ones. The consumer must not return `ControlFlow.continue`
  when an EOF token is encountered.

  If the consumer returns `ControlFlow.break`, it has finished
  consuming the current value, is returning a result, and is ready
  to start consuming a new value.

  If the consumer returns `Except.error`, it has failed at the last
  consumed token. The state of the consumer is unspecified.
  -/
  consume : (cursor : Z) → Cursor.HasNext cursor →
    StateT H m (Except E (ControlFlow R) × { next : Z // Cursor.Consumed next cursor })


end BSmtLib.Token.ConsumeFrom

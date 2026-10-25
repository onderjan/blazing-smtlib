module

public import BSmtLib.Token

public section

namespace BSmtLib.Lexer.Recovery

/- LEAN: Rust's uninhabited enum; an inductive type without constructors. -/
/--
The lexer stops at its first error.

This is the default and can be used with any token consumer.
-/
inductive FailFast : Type

@[no_expose] instance : Repr FailFast := ⟨fun failFast _ => nomatch failFast⟩

/- LEAN: Rust hides the type from the documentation (`#[doc(hidden)]`); Lean has no such
attribute. -/
/--
The lexer recovers from errors (EXPERIMENTAL).

For recovery to be possible not just on the side of the lexer
but also the token consumer, the token consumer must be able
to abandon unfinished work and recover (see `Recover`).

Lexer recovery is implemented but experimental
since the exact semantics have not yet been set in stone.
It can change or be removed in any version and should not be used.
-/
inductive Recovering : Type

@[no_expose] instance : Repr Recovering := ⟨fun recovering _ => nomatch recovering⟩

/- LEAN: the constant `RECOVERS` of the Rust sealed trait `Recovery`, in a class of its own: the
types of what a failed lexer call gives back depend on it (`Lexer.AfterError`), and they depend
on the recovery alone, not on the consumer and its monad, which `LexerRecovery` takes. The lexer
calls require both classes, where Rust requires `SmtLexerRecovery` and gets the constant from its
supertrait: a class that extended `Recovers` would give the instance a second way, which
elaboration does not always see to be the same. The class is public, as a caller generic in the
recovery names it beside `LexerRecovery`. -/
/-- Whether the lexer recovers from errors. -/
class Recovers (R : Type) where
  /-- Whether the lexer recovers from errors. -/
  recovers : Bool

instance : Recovers FailFast := ⟨false⟩

instance : Recovers Recovering := ⟨true⟩

/- LEAN: the Rust sealed trait `SmtLexerRecovery` with the methods of its sealed supertrait,
which only the lexer can call. Lean cannot seal a class; its two instances below are the only
ones meant to exist. Neither can it hide an item from the documentation. So the last sentence
of the Rust documentation, that the trait cannot be implemented outside of the crate, is left
out, and recovery is called experimental but not documentation-hidden. The methods of the
instance for `FailFast`, which Rust makes panic, are never called, and do nothing. -/
/--
Determines the lexer behaviour after an error occurs.

Currently, only fail-fast behaviour is supported,
implemented by `FailFast` for every token consumer.

Lexer error recovery is an experimental
feature in this version,
and may change or be removed in any version.
-/
class LexerRecovery (R : Type) (H : Type) (m : Type → Type) where
  /--
  Makes the consumer abandon its unfinished work.

  Only called if the lexer recovers from errors.
  -/
  abandon : Span.Location → StateT H m Unit
  /--
  Reports to the consumer where the skipped input ends.

  Only called if the lexer recovers from errors.
  -/
  recover : Span.Location → StateT H m Unit

instance [Monad m] : LexerRecovery FailFast H m where
  abandon _ := pure ()
  recover _ := pure ()

/- LEAN: Rust's `SmtRecover: SmtConsume`. The supertrait is the instance argument `Consume H R E`,
as for `ConsumeFrom`. The calls cannot fail, and run in the consumer's monad with its state. The
Rust blanket `impl SmtRecover for &mut T` has no counterpart, as Lean has no references. Rust
declares it after the implementations for `SmtRecovering`; Lean needs it before them. -/
/--
A token consumer that can recover after an error (EXPERIMENTAL).

This is an experimental feature for processing of SMT-LIB scripts
with error recovery: after an error, the current command is abandoned
and the lexer closes all open parentheses before announcing recovery.
If the command remains unclosed at the end of input, recovery is made
before the end of input is handed over (only the unclosed command is
abandoned and dropped).

Lexer recovery is implemented but experimental
since the exact semantics have not yet been set in stone.
It can change or be removed in any version and should not be used.
-/
class Recover (H : Type) (m : outParam (Type → Type)) {R E : outParam Type}
    [Token.Consume H R E] where
  /--
  Abandons everything the consumer has not finished.

  Called when the input is lexically malformed or the consumer itself
  returns an error, before the failing call returns. The location is
  where the failure occurred: the input from there on is skipped, up
  to the location given to `recover`.

  The tokens consumed so far that belong to an unfinished top-level
  value (typically, an SMT-LIB command) are to be abandoned, as if
  they never were handed over.
  -/
  abandon : Span.Location → StateT H m Unit
  /--
  Finishes the recovery after abandoning.

  Called exactly once after every `abandon` before the
  new token is handed over after the recovery. The tokens handed over
  after the recovery are to be considered to follow the tokens before
  the abandoned top-level value started, as if the abandoned top-level
  value was never started. The input between abandonment and recovery
  is not handed over in any way.
  -/
  recover : Span.Location → StateT H m Unit

instance {R E : Type} [Token.Consume H R E] [Recover H m] : LexerRecovery Recovering H m where
  abandon := Recover.abandon
  recover := Recover.recover

end BSmtLib.Lexer.Recovery

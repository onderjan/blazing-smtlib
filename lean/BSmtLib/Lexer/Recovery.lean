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

/- LEAN: the constant `RECOVERS` of the Rust sealed trait `Recovery`, in a class of its own: the
types of what a failed lexer call gives back depend on it (`Lexer.AfterError`), and they depend
on the recovery alone, not on the consumer and its monad, which `LexRecovery` takes. The lexer
calls require both classes, where Rust requires `SmtLexRecovery` and gets the constant from its
supertrait: a class that extended `Recovers` would give the instance a second way, which
elaboration does not always see to be the same. The class is public, as a caller generic in the
recovery names it beside `LexRecovery`. -/
/-- Whether the lexer recovers from errors. -/
class Recovers (R : Type) where
  /-- Whether the lexer recovers from errors. -/
  recovers : Bool

instance : Recovers FailFast := ⟨false⟩

instance : Recovers Recovering := ⟨true⟩

/- LEAN: the Rust sealed trait `SmtLexRecovery` with the methods of its sealed supertrait,
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
class LexRecovery (R : Type) (H : Type) (m : Type → Type) where
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

instance [Monad m] : LexRecovery FailFast H m where
  abandon _ := pure ()
  recover _ := pure ()

instance {R E : Type} [Token.Consume H R E] [Token.Recover H m] : LexRecovery Recovering H m where
  abandon := Token.Recover.abandon
  recover := Token.Recover.recover

end BSmtLib.Lexer.Recovery

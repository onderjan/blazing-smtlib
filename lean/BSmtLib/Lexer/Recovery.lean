import BSmtLib.Token

namespace BSmtLib

/- LEAN: Rust's marker types `SmtFailFast` and `SmtRecovering`, given to the lexer as its type
parameter `R`. Here the lexer is indexed by a value of this type instead, as the result types
of its calls depend on the choice: a call that fails gives back no lexer that stops at its
first error, but gives back a recovering one. -/
/-- Determines the lexer behaviour after an error occurs. -/
inductive Recovery where
  /--
  The lexer stops at its first error.

  This is the default and can be used with any token consumer.
  -/
  | failFast
  /--
  The lexer recovers from errors.

  For recovery to be possible not just on the side of the lexer
  but also the token consumer, the token consumer must be able
  to abandon unfinished work and recover (see `Recover`).
  -/
  | recovering
  deriving BEq, Repr, Inhabited

/- LEAN: the Rust sealed trait `SmtLexRecovery`, whose methods only the lexer can call. Lean
cannot seal a class; its two instances below are the only ones meant to exist. The methods of
the instance for a lexer that stops at its first error, which Rust makes panic, are never
called, and do nothing. -/
/--
Recovery methods of the consumer under the lexer's recovery.

Exists for every token consumer for `failFast`, and for the token consumers
that can abandon unfinished work (see `Recover`) for `recovering`.
-/
class LexRecovery (recovery : Recovery) (H : Type) (m : Type → Type) where
  /-- Makes the consumer abandon its unfinished work. -/
  abandon : Location → StateT H m Unit
  /-- Reports to the consumer where the skipped input ends. -/
  recover : Location → StateT H m Unit

instance [Monad m] : LexRecovery .failFast H m where
  abandon _ := pure ()
  recover _ := pure ()

instance [Recover H m] : LexRecovery .recovering H m where
  abandon := Recover.abandon
  recover := Recover.recover

end BSmtLib

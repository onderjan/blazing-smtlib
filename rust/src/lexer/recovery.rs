use crate::{span::SmtLocation, token::SmtConsume};

/// Marker for a lexer that stops at its first error.
///
/// This is the default and can be used with any token consumer.
#[derive(Debug)]
pub enum SmtFailFast {}

/// Marker for a lexer that recovers from errors (EXPERIMENTAL).
///
/// For recovery to be possible not just on the side of the lexer
/// but also the token consumer, the token consumer must be able
/// to abandon unfinished work and recover (see [`SmtRecover`]).
///
/// Lexer recovery is implemented but experimental
/// since the exact semantics have not yet been set in stone.
/// It can change or be removed in any version and should not be used.
#[doc(hidden)]
#[derive(Debug)]
pub enum SmtRecovering {}

pub(super) mod sealed {
    use crate::{span::SmtLocation, token::SmtConsume};

    /// Recovery information and methods only the lexer can access.
    ///
    /// The trait cannot be named outside of this crate, so its items
    /// are not a part of the public interface.
    pub trait Recovery<C: SmtConsume> {
        /// Whether the lexer recovers from errors.
        const RECOVERS: bool;

        /// Makes the consumer abandon its unfinished work.
        ///
        /// Only called if the lexer recovers from errors.
        fn abandon(consumer: &mut C, location: SmtLocation);

        /// Reports to the consumer where the skipped input ends.
        ///
        /// Only called if the lexer recovers from errors.
        fn recover(consumer: &mut C, location: SmtLocation);
    }
}

/// Determines lexer behaviour after an error occurs.
///
/// Currently, only fail-fast behaviour is supported,
/// implemented by [`SmtFailFast`] for every token consumer.
///
/// Lexer error recovery is an experimental,
/// documentation-hidden feature in this version,
/// and may change or be removed in any version.
///
/// This trait cannot be implemented outside of this crate.
pub trait SmtLexerRecovery<C: SmtConsume>: sealed::Recovery<C> {}

impl<C: SmtConsume> SmtLexerRecovery<C> for SmtFailFast {}

impl<C: SmtConsume> sealed::Recovery<C> for SmtFailFast {
    const RECOVERS: bool = false;

    #[inline]
    fn abandon(_consumer: &mut C, _location: SmtLocation) {
        panic!("fail-fast lexer cannot abandon")
    }

    #[inline]
    fn recover(_consumer: &mut C, _location: SmtLocation) {
        panic!("fail-fast lexer cannot recover")
    }
}

impl<C: SmtRecover> SmtLexerRecovery<C> for SmtRecovering {}

impl<C: SmtRecover> sealed::Recovery<C> for SmtRecovering {
    const RECOVERS: bool = true;

    #[inline]
    fn abandon(consumer: &mut C, location: SmtLocation) {
        consumer.abandon(location)
    }

    #[inline]
    fn recover(consumer: &mut C, location: SmtLocation) {
        consumer.recover(location)
    }
}

/// A token consumer that can recover after an error (EXPERIMENTAL).
///
/// This is an experimental feature for processing of SMT-LIB scripts
/// with error recovery: after an error, the current command is abandoned
/// and the lexer closes all open parentheses before announcing recovery.
/// If the command remains unclosed at the end of input, recovery is made
/// before the end of input is handed over (only the unclosed command is
/// abandoned and dropped).
///
/// Lexer recovery is implemented but experimental
/// since the exact semantics have not yet been set in stone.
/// It can change or be removed in any version and should not be used.
#[doc(hidden)]
pub trait SmtRecover: SmtConsume {
    /// Abandons everything the consumer has not finished.
    ///
    /// Called when the input is lexically malformed or the consumer itself
    /// returns an error, before the failing call returns. The location is
    /// where the failure occurred: the input from there on is skipped, up
    /// to the location given to [`recover`](Self::recover).
    ///
    /// The tokens consumed so far that belong to an unfinished top-level
    /// value (typically, an SMT-LIB command) are to be abandoned, as if
    /// they never were handed over.
    fn abandon(&mut self, location: SmtLocation);

    /// Finishes the recovery after abandoning.
    ///
    /// Called exactly once after every [`abandon`](Self::abandon) before the
    /// new token is handed over after the recovery. The tokens handed over
    /// after the recovery are to be considered to follow the tokens before
    /// the abandoned top-level value started, as if the abandoned top-level
    /// value was never started. The input between abandonment and recovery
    /// is not handed over in any way.
    fn recover(&mut self, location: SmtLocation);
}

/// Mutable references over token consumers that can recover can recover.
impl<T: SmtRecover + ?Sized> SmtRecover for &mut T {
    #[inline]
    fn abandon(&mut self, location: SmtLocation) {
        (**self).abandon(location)
    }

    #[inline]
    fn recover(&mut self, location: SmtLocation) {
        (**self).recover(location)
    }
}

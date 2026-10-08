use crate::{
    SmtLocation,
    token::{SmtConsume, SmtRecover},
};

/// The lexer stops at its first error.
///
/// This is the default and can be used with any token consumer.
pub enum SmtFailFast {}

/// The lexer recovers from errors (EXPERIMENTAL).
///
/// For recovery to be possible not just on the side of the lexer
/// but also the token consumer, the token consumer must be able
/// to abandon unfinished work and recover (see [`SmtRecover`]).
///
/// Lexer recovery is implemented but experimental
/// since the exact semantics have not yet been set in stone.
/// It can change or be removed in any version and should not be used.
#[doc(hidden)]
pub enum SmtRecovering {}

pub(super) mod sealed {
    use crate::{SmtLocation, token::SmtConsume};

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

/// Determines the lexer behaviour after an error occurs.
///
/// Currently, only fail-fast behaviour is supported,
/// implemented by [`SmtFailFast`] for every token consumer.
///
/// Lexer error recovery is an experimental,
/// documentation-hidden feature in this version,
/// and may change or be removed in any version.
///
/// It cannot be implemented outside of this crate.
pub trait SmtLexRecovery<C: SmtConsume>: sealed::Recovery<C> {}

impl<C: SmtConsume> SmtLexRecovery<C> for SmtFailFast {}

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

impl<C: SmtRecover> SmtLexRecovery<C> for SmtRecovering {}

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

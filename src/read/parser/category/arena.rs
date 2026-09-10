use crate::{SmtHandler, SmtMultiple};

/// An arena of bytes and handled values.
///
/// The bytes and values are waiting to be consumed by a handler method
/// that handles a structure they are a part of.
///
/// The values are pushed on the stack, and the handling effectively
/// drains the stack from some point onward. This means that each
/// owner of multiple values to be parsed can remember just the index
/// of the first element to be handled under it.
pub(crate) struct Arena<H: SmtHandler + ?Sized> {
    /// Handled terms, waiting to be consumed.
    pub(crate) terms: Vec<H::Term>,
}

impl<H: SmtHandler + ?Sized> Arena<H> {
    pub(crate) fn new() -> Self {
        Self { terms: Vec::new() }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        self.terms.is_empty()
    }

    pub(crate) fn clear(&mut self) {
        self.terms.clear();
    }

    /// Hands the terms from `start` onward to `f`, removing them afterwards.
    ///
    /// The handling may or may not remove the terms by itself,
    /// so the arena is truncated after `f` returns regardless.
    #[inline]
    pub(crate) fn hand_over_terms<R>(
        &mut self,
        start: usize,
        f: impl FnOnce(SmtMultiple<'_, H::Term>) -> R,
    ) -> R {
        let access = ArenaAccess { _priv: () };
        let result = f(SmtMultiple::new(access, &mut self.terms, start));
        self.terms.truncate(start);
        result
    }
}

/// Proof that a hand-over comes from the arena.
///
/// Only the arena can construct it, so only the arena can create an [`SmtMultiple`].
pub(crate) struct ArenaAccess {
    _priv: (),
}

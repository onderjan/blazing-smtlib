use crate::{SmtBindings, SmtHandler, SmtMultiple, SmtSymbolView, String8View};

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
    /// Bytes of names waiting to be consumed, currently let binding names.
    pub(crate) text: Vec<u8>,
    /// Let binding names waiting to be consumed, as handles into the text.
    pub(crate) symbols: Vec<TextHandle>,
    /// Handled terms, waiting to be consumed.
    pub(crate) terms: Vec<H::Term>,
}

impl<H: SmtHandler + ?Sized> Arena<H> {
    pub(crate) fn new() -> Self {
        Self {
            text: Vec::new(),
            symbols: Vec::new(),
            terms: Vec::new(),
        }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        self.text.is_empty() && self.symbols.is_empty() && self.terms.is_empty()
    }

    pub(crate) fn clear(&mut self) {
        self.text.clear();
        self.symbols.clear();
        self.terms.clear();
    }

    /// Appends the bytes to the text, returning their handle.
    #[inline]
    pub(crate) fn push_text(&mut self, bytes: &[u8]) -> TextHandle {
        let start = self.text.len();
        self.text.extend_from_slice(bytes);
        TextHandle {
            start,
            len: bytes.len(),
        }
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

    /// Hands the let bindings to `f`, removing them afterwards: the names
    /// from `names_start` onward with their text from `text_start` onward,
    /// and the terms from `terms_start` onward.
    ///
    /// The handling may or may not remove the terms by itself,
    /// so the arena is truncated after `f` returns regardless.
    pub(crate) fn hand_over_bindings<R>(
        &mut self,
        text_start: usize,
        names_start: usize,
        terms_start: usize,
        f: impl FnOnce(SmtBindings<'_, H>) -> R,
    ) -> R {
        let names = SmtMultiple::new(ArenaAccess { _priv: () }, &mut self.symbols, names_start);
        let terms = SmtMultiple::new(ArenaAccess { _priv: () }, &mut self.terms, terms_start);
        let bindings = SmtBindings::new(ArenaAccess { _priv: () }, &self.text, names, terms);
        let result = f(bindings);
        self.symbols.truncate(names_start);
        self.terms.truncate(terms_start);
        self.text.truncate(text_start);
        result
    }
}

/// Proof that a hand-over comes from the arena.
///
/// Only the arena can construct it, so only the arena
/// can create [`SmtMultiple`] or [`SmtBindings`].
pub(crate) struct ArenaAccess {
    _priv: (),
}

/// A run of bytes in the arena text.
#[derive(Clone, Copy, Debug)]
pub(crate) struct TextHandle {
    pub(crate) start: usize,
    pub(crate) len: usize,
}

impl TextHandle {
    /// Views the bytes as a symbol.
    #[inline]
    pub(crate) fn symbol_view(self, text: &[u8]) -> SmtSymbolView<'_> {
        SmtSymbolView::new_unchecked(String8View::new(&text[self.start..self.start + self.len]))
    }
}

use crate::{
    SmtBindings, SmtHandler, SmtIdentView, SmtIndexView, SmtIndices, SmtKeywordView, SmtMultiple,
    SmtNumeralView, SmtPatternView, SmtQualifiedIdentView, SmtSimplePatternView, SmtSimplePatterns,
    SmtSort, SmtSymbolView,
    token::{SmtVersion, Token, TokenKind},
};

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
    /// Bytes of names waiting to be consumed: identifiers, their indices,
    /// and let binding names.
    pub(crate) text: Vec<u8>,
    /// Identifier indices waiting to be consumed, as handles into the text.
    pub(crate) indices: Vec<IndexHandle>,
    /// Let binding names waiting to be consumed, as handles into the text.
    pub(crate) symbols: Vec<TextHandle>,
    /// Handled S-expressions waiting to be consumed, inside S-expression lists.
    pub(crate) s_exprs: Vec<H::SExpr>,
    /// Handled attributes waiting to be consumed, inside attribute lists.
    pub(crate) attributes: Vec<H::Attribute>,
    /// Simple patterns waiting to be consumed, as constructor pattern arguments.
    pub(crate) simple_patterns: Vec<SimplePatternHandle>,
    /// Handled sorts waiting to be consumed.
    pub(crate) sorts: Vec<H::Sort>,
    /// Handled terms, waiting to be consumed.
    pub(crate) terms: Vec<H::Term>,
}

impl<H: SmtHandler + ?Sized> Arena<H> {
    pub(crate) fn new() -> Self {
        Self {
            text: Vec::new(),
            indices: Vec::new(),
            symbols: Vec::new(),
            s_exprs: Vec::new(),
            attributes: Vec::new(),
            simple_patterns: Vec::new(),
            sorts: Vec::new(),
            terms: Vec::new(),
        }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        self.text.is_empty()
            && self.indices.is_empty()
            && self.symbols.is_empty()
            && self.s_exprs.is_empty()
            && self.attributes.is_empty()
            && self.simple_patterns.is_empty()
            && self.sorts.is_empty()
            && self.terms.is_empty()
    }

    pub(crate) fn clear(&mut self) {
        self.text.clear();
        self.indices.clear();
        self.symbols.clear();
        self.s_exprs.clear();
        self.attributes.clear();
        self.simple_patterns.clear();
        self.sorts.clear();
        self.terms.clear();
    }

    /// Translates a token into its kind.
    ///
    /// This depends on the keyword list and thus the version,
    /// which will be stored in the arena in future.
    #[inline]
    pub(crate) fn token_kind<'a>(&self, token: Token<'a>) -> TokenKind<'a> {
        // TODO: classify kind by currently set version
        TokenKind::from_token(token, SmtVersion::V2_7)
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

    /// Pushes a non-indexed identifier into the arena and returns its handle.
    pub(crate) fn push_nonindexed_ident(&mut self, name: SmtSymbolView) -> IdentHandle {
        IdentHandle {
            name: self.push_text(name.as_slice()),
            indices_start: self.indices.len(),
        }
    }

    /// Hands an application to `f`, removing it afterwards: its function
    /// identifier and the arguments from `args_start` onward.
    #[inline]
    pub(crate) fn hand_over_application<R>(
        &mut self,
        function: QualifiedIdentHandle<H>,
        args_start: usize,
        f: impl FnOnce(SmtQualifiedIdentView<'_, H>, SmtMultiple<'_, H::Term>) -> R,
    ) -> R {
        let QualifiedIdentHandle { ident, sort } = function;
        let function = SmtQualifiedIdentView {
            ident: ident_view(&self.text, &self.indices, ident),
            sort,
        };
        let args = SmtMultiple::new(ArenaAccess { _priv: () }, &mut self.terms, args_start);
        let result = f(function, args);
        self.terms.truncate(args_start);
        self.indices.truncate(ident.indices_start);
        self.text.truncate(ident.name.start);
        result
    }

    /// Views a simple identifier: a name with no indices.
    #[inline]
    pub(crate) fn simple_ident_view<'a>(&'a self, name: SmtSymbolView<'a>) -> SmtIdentView<'a> {
        SmtIdentView {
            name,
            indices: SmtIndices::new(ArenaAccess { _priv: () }, &self.text, &[]),
        }
    }

    /// Hands the let bindings to `f`, removing them afterwards: the names
    /// from `names_start` onward with their text from `text_start` onward,
    /// and the terms from `terms_start` onward.
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

    /// Hands the identifier to `f`, removing it afterwards.
    #[inline]
    pub(crate) fn hand_over_ident<R>(
        &mut self,
        ident: IdentHandle,
        f: impl FnOnce(SmtIdentView<'_>) -> R,
    ) -> R {
        let result = f(ident_view(&self.text, &self.indices, ident));
        self.indices.truncate(ident.indices_start);
        self.text.truncate(ident.name.start);
        result
    }

    /// Hands the qualified identifier to `f`, removing it afterwards.
    #[inline]
    pub(crate) fn hand_over_qualified_ident<R>(
        &mut self,
        qualified_ident: QualifiedIdentHandle<H>,
        f: impl FnOnce(SmtQualifiedIdentView<'_, H>) -> R,
    ) -> R {
        let QualifiedIdentHandle { ident, sort } = qualified_ident;
        let view = SmtQualifiedIdentView {
            ident: ident_view(&self.text, &self.indices, ident),
            sort,
        };
        let result = f(view);
        self.indices.truncate(ident.indices_start);
        self.text.truncate(ident.name.start);
        result
    }

    /// Hands a sorted variable to `f`, removing its name afterwards.
    #[inline]
    pub(crate) fn hand_over_sorted_var<R>(
        &mut self,
        name: TextHandle,
        sort: H::Sort,
        f: impl FnOnce(SmtSymbolView<'_>, H::Sort) -> R,
    ) -> R {
        let result = f(name.symbol_view(&self.text), sort);
        self.text.truncate(name.start);
        result
    }

    /// Hands a sort to `f`, removing it afterwards.
    #[inline]
    pub(crate) fn hand_over_sort<R>(
        &mut self,
        ident: IdentHandle,
        applied_start: usize,
        f: impl FnOnce(SmtSort<'_, H>) -> R,
    ) -> R {
        let sort = SmtSort {
            ident: ident_view(&self.text, &self.indices, ident),
            applied: SmtMultiple::new(ArenaAccess { _priv: () }, &mut self.sorts, applied_start),
        };
        let result = f(sort);
        self.sorts.truncate(applied_start);
        self.indices.truncate(ident.indices_start);
        self.text.truncate(ident.name.start);
        result
    }

    /// Hands the S-expressions from `start` onward to `f`, removing them afterwards.
    #[inline]
    pub(crate) fn hand_over_s_exprs<R>(
        &mut self,
        start: usize,
        f: impl FnOnce(SmtMultiple<'_, H::SExpr>) -> R,
    ) -> R {
        let s_exprs = SmtMultiple::new(ArenaAccess { _priv: () }, &mut self.s_exprs, start);
        let result = f(s_exprs);
        self.s_exprs.truncate(start);
        result
    }

    /// Hands an attribute name to `f`, removing it afterwards.
    #[inline]
    pub(crate) fn hand_over_keyword<R>(
        &mut self,
        name: TextHandle,
        f: impl FnOnce(SmtKeywordView<'_>) -> R,
    ) -> R {
        let result = f(name.keyword_view(&self.text));
        self.text.truncate(name.start);
        result
    }

    /// Hands an attribute name with its S-expression value to `f`, removing them afterwards.
    #[inline]
    pub(crate) fn hand_over_keyword_s_exprs<R>(
        &mut self,
        name: TextHandle,
        start: usize,
        f: impl FnOnce(SmtKeywordView<'_>, SmtMultiple<'_, H::SExpr>) -> R,
    ) -> R {
        let s_exprs = SmtMultiple::new(ArenaAccess { _priv: () }, &mut self.s_exprs, start);
        let result = f(name.keyword_view(&self.text), s_exprs);
        self.s_exprs.truncate(start);
        self.text.truncate(name.start);
        result
    }

    /// Hands the attributes from `start` onward to `f`, removing them afterwards.
    #[inline]
    pub(crate) fn hand_over_attributes<R>(
        &mut self,
        start: usize,
        f: impl FnOnce(SmtMultiple<'_, H::Attribute>) -> R,
    ) -> R {
        let attributes = SmtMultiple::new(ArenaAccess { _priv: () }, &mut self.attributes, start);
        let result = f(attributes);
        self.attributes.truncate(start);
        result
    }

    /// Hands a match pattern to `f`, removing it afterwards.
    #[inline]
    pub(crate) fn hand_over_pattern<R>(
        &mut self,
        pattern: PatternHandle<'_>,
        f: impl FnOnce(SmtPatternView<'_>) -> R,
    ) -> R {
        match pattern {
            PatternHandle::Simple(simple) => f(SmtPatternView::Simple(simple)),
            PatternHandle::Application {
                constructor,
                args_start,
            } => {
                let pattern = SmtPatternView::Application {
                    constructor: constructor.symbol_view(&self.text),
                    args: SmtSimplePatterns::new(
                        ArenaAccess { _priv: () },
                        &self.text,
                        &self.simple_patterns[args_start..],
                    ),
                };
                let result = f(pattern);
                self.simple_patterns.truncate(args_start);
                self.text.truncate(constructor.start);
                result
            }
        }
    }
}

/// Views the identifier in the arena text and indices.
#[inline]
fn ident_view<'a>(
    text: &'a [u8],
    indices: &'a [IndexHandle],
    ident: IdentHandle,
) -> SmtIdentView<'a> {
    SmtIdentView {
        name: ident.name.symbol_view(text),
        indices: SmtIndices::new(
            ArenaAccess { _priv: () },
            text,
            &indices[ident.indices_start..],
        ),
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
        SmtSymbolView::new_unchecked(&text[self.start..self.start + self.len])
    }

    /// Views the bytes as a keyword.
    #[inline]
    pub(crate) fn keyword_view(self, text: &[u8]) -> SmtKeywordView<'_> {
        SmtKeywordView::new_unchecked(&text[self.start..self.start + self.len])
    }

    /// Views the bytes as a numeral.
    #[inline]
    pub(crate) fn numeral_view(self, text: &[u8]) -> SmtNumeralView<'_> {
        SmtNumeralView::new_unchecked(&text[self.start..self.start + self.len])
    }
}

/// An identifier index in the arena text.
#[derive(Clone, Copy, Debug)]
pub(crate) enum IndexHandle {
    Numeral(TextHandle),
    Symbol(TextHandle),
}

impl IndexHandle {
    /// Views the index.
    #[inline]
    pub(crate) fn view(self, text: &[u8]) -> SmtIndexView<'_> {
        match self {
            IndexHandle::Numeral(handle) => SmtIndexView::Numeral(handle.numeral_view(text)),
            IndexHandle::Symbol(handle) => SmtIndexView::Symbol(handle.symbol_view(text)),
        }
    }
}

/// An identifier in the arena: its name in the text, its indices
/// in the arena indices starting at the given position.
#[derive(Clone, Copy, Debug)]
pub(crate) struct IdentHandle {
    pub(crate) name: TextHandle,
    pub(crate) indices_start: usize,
}

/// A qualified identifier: an identifier in the arena and its handled sort, if any.
pub(crate) struct QualifiedIdentHandle<H: SmtHandler + ?Sized> {
    pub(crate) ident: IdentHandle,
    pub(crate) sort: Option<H::Sort>,
}

impl<H: SmtHandler + ?Sized> QualifiedIdentHandle<H> {
    pub(crate) fn unqualified(ident: IdentHandle) -> Self {
        Self { ident, sort: None }
    }
}

/// A simple pattern: a symbol in the arena text, or a wildcard.
#[derive(Clone, Copy, Debug)]
pub(crate) enum SimplePatternHandle {
    Symbol(TextHandle),
    Wildcard,
}

impl SimplePatternHandle {
    /// Views the simple pattern.
    #[inline]
    pub(crate) fn view(self, text: &[u8]) -> SmtSimplePatternView<'_> {
        match self {
            SimplePatternHandle::Symbol(handle) => {
                SmtSimplePatternView::Symbol(handle.symbol_view(text))
            }
            SimplePatternHandle::Wildcard => SmtSimplePatternView::Wildcard,
        }
    }
}

/// A parsed match pattern: a simple pattern from its token, or a constructor
/// application with the constructor in the arena text and the arguments in the
/// arena simple patterns from the given position onward.
pub(crate) enum PatternHandle<'t> {
    Simple(SmtSimplePatternView<'t>),
    Application {
        constructor: TextHandle,
        args_start: usize,
    },
}

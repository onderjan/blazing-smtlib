use std::fmt;

use crate::{
    SmtHandler,
    grammar::{
        SmtIdent, SmtIndex, SmtIndices, SmtMatchCases, SmtMultiple, SmtNamedValues, SmtPattern,
        SmtPatternApplication, SmtQualifiedIdent, SmtSimplePattern, SmtSimplePatterns, SmtSort,
    },
    lexicon::{SmtKeyword, SmtNumeral, SmtSymbol},
    parser::{
        AttributeSlot, IdentSlot, PatternSlot, QualifiedIdentSlot, SExprSlot, SortSlot,
        SortedVarSlot, TermSlot,
    },
};

/// Current state of library parsers.
///
/// Parsers that are constructed multiple times in locations where their use
/// does not overlap can have unnecessarily duplicated resources (e.g.
/// collections). This structure is only constructed once (usually by
/// [SmtParseAdapter](super::SmtParseAdapter)) for the root parser and
/// propagated to smaller parsers.
pub struct SmtParseState<H: SmtHandler + ?Sized> {
    pub(crate) arena: Arena<H>,
    pub(crate) ident_slot: IdentSlot,
    pub(crate) qualified_ident_slot: QualifiedIdentSlot<H>,
    pub(crate) sort_slot: SortSlot<H>,
    pub(crate) sorted_var_slot: SortedVarSlot<H>,
    pub(crate) s_expr_slot: SExprSlot,
    pub(crate) attribute_slot: AttributeSlot,
    pub(crate) pattern_slot: PatternSlot,
    pub(crate) term_slot: TermSlot<H>,
}

impl<H: SmtHandler + ?Sized> fmt::Debug for SmtParseState<H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SmtParseState").finish_non_exhaustive()
    }
}

impl<H: SmtHandler + ?Sized> SmtParseState<H> {
    pub fn new() -> Self {
        Self {
            arena: Arena::new(),
            ident_slot: IdentSlot::new(),
            qualified_ident_slot: QualifiedIdentSlot::new(),
            sort_slot: SortSlot::new(),
            sorted_var_slot: SortedVarSlot::new(),
            s_expr_slot: SExprSlot::new(),
            attribute_slot: AttributeSlot::new(),
            pattern_slot: PatternSlot::new(),
            term_slot: TermSlot::new(),
        }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        self.arena.is_pristine()
            && self.ident_slot.is_pristine()
            && self.qualified_ident_slot.is_pristine()
            && self.sort_slot.is_pristine()
            && self.sorted_var_slot.is_pristine()
            && self.s_expr_slot.is_pristine()
            && self.attribute_slot.is_pristine()
            && self.pattern_slot.is_pristine()
            && self.term_slot.is_pristine()
    }

    pub(crate) fn clear(&mut self) {
        self.arena.clear();
        self.ident_slot.clear();
        self.qualified_ident_slot.clear();
        self.sort_slot.clear();
        self.sorted_var_slot.clear();
        self.s_expr_slot.clear();
        self.attribute_slot.clear();
        self.pattern_slot.clear();
        self.term_slot.clear();
    }
}

impl<H: SmtHandler + ?Sized> Default for SmtParseState<H> {
    fn default() -> Self {
        Self::new()
    }
}

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
    pub(crate) symbols: Vec<SymbolHandle>,
    /// Handled S-expressions waiting to be consumed, inside S-expression lists.
    pub(crate) s_exprs: Vec<H::SExpr>,
    /// Handled attributes waiting to be consumed, inside attribute lists.
    pub(crate) attributes: Vec<H::Attribute>,
    /// Simple patterns waiting to be consumed, as constructor pattern arguments.
    pub(crate) simple_patterns: Vec<SimplePatternHandle>,
    /// Patterns waiting to be consumed.
    pub(crate) patterns: Vec<PatternHandleBuf>,
    /// Handled sorts waiting to be consumed.
    pub(crate) sorts: Vec<H::Sort>,
    /// Handled terms, waiting to be consumed.
    pub(crate) terms: Vec<H::Term>,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct MatchCasesStarts {
    pub(crate) text: usize,
    pub(crate) simple_patterns: usize,
    pub(crate) patterns: usize,
    pub(crate) terms: usize,
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
            patterns: Vec::new(),
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
            && self.patterns.is_empty()
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
        self.patterns.clear();
        self.sorts.clear();
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

    /// Appends the symbol to the text, returning its handle.
    ///
    /// A quoted symbol is pushed with a leading pipe.
    #[inline]
    pub(crate) fn push_symbol(&mut self, symbol: SmtSymbol) -> SymbolHandle {
        SymbolHandle::create_by_push(&mut self.text, symbol)
    }

    /// Pushes a non-indexed identifier into the arena and returns its handle.
    pub(crate) fn push_nonindexed_ident(&mut self, name: SmtSymbol) -> IdentHandle {
        IdentHandle {
            name: self.push_symbol(name),
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
        f: impl FnOnce(SmtQualifiedIdent<'_, H>, SmtMultiple<'_, H::Term>) -> R,
    ) -> R {
        let QualifiedIdentHandle { ident, sort } = function;
        let function = SmtQualifiedIdent {
            ident: ident_view(&self.text, &self.indices, ident),
            sort,
        };
        let args = SmtMultiple::new_starting(&mut self.terms, args_start);
        let result = f(function, args);
        self.terms.truncate(args_start);
        self.indices.truncate(ident.indices_start);
        self.text.truncate(ident.name.start());
        result
    }

    /// Views a simple identifier: a name with no indices.
    #[inline]
    pub(crate) fn simple_ident_view<'a>(&'a self, name: SmtSymbol<'a>) -> SmtIdent<'a> {
        SmtIdent {
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
        f: impl FnOnce(SmtNamedValues<'_, H::Term>) -> R,
    ) -> R {
        let names = SmtMultiple::new_starting(&mut self.symbols, names_start);
        let terms = SmtMultiple::new_starting(&mut self.terms, terms_start);
        let bindings = SmtNamedValues::new(&self.text, names, terms);
        let result = f(bindings);
        self.symbols.truncate(names_start);
        self.terms.truncate(terms_start);
        self.text.truncate(text_start);
        result
    }

    /// Hands the sorted variables to `f`, removing them afterwards.
    pub(crate) fn hand_over_sorted_vars<R>(
        &mut self,
        text_start: usize,
        names_start: usize,
        sorts_start: usize,
        f: impl FnOnce(SmtNamedValues<'_, H::Sort>) -> R,
    ) -> R {
        let names = SmtMultiple::new_starting(&mut self.symbols, names_start);
        let sorts = SmtMultiple::new_starting(&mut self.sorts, sorts_start);
        let sorted_vars = SmtNamedValues::new(&self.text, names, sorts);
        let result = f(sorted_vars);
        self.symbols.truncate(names_start);
        self.sorts.truncate(sorts_start);
        self.text.truncate(text_start);
        result
    }

    /// Hands the identifier to `f`, removing it afterwards.
    #[inline]
    pub(crate) fn hand_over_ident<R>(
        &mut self,
        ident: IdentHandle,
        f: impl FnOnce(SmtIdent<'_>) -> R,
    ) -> R {
        let result = f(ident_view(&self.text, &self.indices, ident));
        self.indices.truncate(ident.indices_start);
        self.text.truncate(ident.name.start());
        result
    }

    /// Hands the qualified identifier to `f`, removing it afterwards.
    #[inline]
    pub(crate) fn hand_over_qualified_ident<R>(
        &mut self,
        qualified_ident: QualifiedIdentHandle<H>,
        f: impl FnOnce(SmtQualifiedIdent<'_, H>) -> R,
    ) -> R {
        let QualifiedIdentHandle { ident, sort } = qualified_ident;
        let view = SmtQualifiedIdent {
            ident: ident_view(&self.text, &self.indices, ident),
            sort,
        };
        let result = f(view);
        self.indices.truncate(ident.indices_start);
        self.text.truncate(ident.name.start());
        result
    }

    /// Hands a sorted variable to `f`, removing its name afterwards.
    #[inline]
    pub(crate) fn hand_over_sorted_var<R>(
        &mut self,
        name: SymbolHandle,
        sort: H::Sort,
        f: impl FnOnce(SmtSymbol<'_>, H::Sort) -> R,
    ) -> R {
        let result = f(name.symbol_view(&self.text), sort);
        self.text.truncate(name.start());
        result
    }

    /// Hands a sort to `f`, removing it afterwards.
    #[inline]
    pub(crate) fn hand_over_sort<R>(
        &mut self,
        ident: IdentHandle,
        args_start: usize,
        f: impl FnOnce(SmtSort<'_, H>) -> R,
    ) -> R {
        let sort = SmtSort {
            ident: ident_view(&self.text, &self.indices, ident),
            args: SmtMultiple::new_starting(&mut self.sorts, args_start),
        };
        let result = f(sort);
        self.sorts.truncate(args_start);
        self.indices.truncate(ident.indices_start);
        self.text.truncate(ident.name.start());
        result
    }

    /// Hands the S-expressions from `start` onward to `f`, removing them afterwards.
    #[inline]
    pub(crate) fn hand_over_s_exprs<R>(
        &mut self,
        start: usize,
        f: impl FnOnce(SmtMultiple<'_, H::SExpr>) -> R,
    ) -> R {
        let s_exprs = SmtMultiple::new_starting(&mut self.s_exprs, start);
        let result = f(s_exprs);
        self.s_exprs.truncate(start);
        result
    }

    /// Hands an attribute name to `f`, removing it afterwards.
    #[inline]
    pub(crate) fn hand_over_keyword<R>(
        &mut self,
        name: TextHandle,
        f: impl FnOnce(SmtKeyword<'_>) -> R,
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
        f: impl FnOnce(SmtKeyword<'_>, SmtMultiple<'_, H::SExpr>) -> R,
    ) -> R {
        let s_exprs = SmtMultiple::new_starting(&mut self.s_exprs, start);
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
        let attributes = SmtMultiple::new_starting(&mut self.attributes, start);
        let result = f(attributes);
        self.attributes.truncate(start);
        result
    }

    /// Hands the match cases from `starts` onward to `f`, removing them afterwards.
    #[inline]
    pub(crate) fn hand_over_match_cases<R>(
        &mut self,
        starts: MatchCasesStarts,
        f: impl FnOnce(SmtMatchCases<'_, H>) -> R,
    ) -> R {
        let patterns = SmtMultiple::new_starting(&mut self.patterns, starts.patterns);
        let terms = SmtMultiple::new_starting(&mut self.terms, starts.terms);
        let match_cases = SmtMatchCases::new(
            ArenaAccess { _priv: () },
            &self.text,
            &self.simple_patterns,
            patterns,
            terms,
        );
        let result = f(match_cases);
        self.text.truncate(starts.text);
        self.simple_patterns.truncate(starts.simple_patterns);
        self.patterns.truncate(starts.patterns);
        self.terms.truncate(starts.terms);
        result
    }

    /// Hands a match pattern to `f`, removing it afterwards.
    #[inline]
    pub(crate) fn hand_over_pattern<R>(
        &mut self,
        pattern: PatternHandle<'_>,
        f: impl FnOnce(SmtPattern<'_>) -> R,
    ) -> R {
        match pattern {
            PatternHandle::Simple(simple) => f(SmtPattern::Simple(simple)),
            PatternHandle::Application {
                constructor,
                args_start,
                args_end,
            } => {
                let pattern = SmtPattern::Application(SmtPatternApplication::new_unchecked(
                    constructor.symbol_view(&self.text),
                    SmtSimplePatterns::new(
                        ArenaAccess { _priv: () },
                        &self.text,
                        &self.simple_patterns[args_start..args_end],
                    ),
                ));
                let result = f(pattern);
                self.simple_patterns.truncate(args_start);
                self.text.truncate(constructor.start());
                result
            }
        }
    }

    /// Views a match pattern.
    #[inline]
    pub(crate) fn pattern_view<'a>(
        text: &'a [u8],
        simple_patterns: &'a [SimplePatternHandle],
        pattern: &PatternHandleBuf,
    ) -> SmtPattern<'a> {
        match pattern {
            PatternHandleBuf::Simple(simple) => SmtPattern::Simple(simple.view(text)),
            PatternHandleBuf::Application {
                constructor,
                args_start,
                args_end,
            } => SmtPattern::Application(SmtPatternApplication::new_unchecked(
                constructor.symbol_view(text),
                SmtSimplePatterns::new(
                    ArenaAccess { _priv: () },
                    text,
                    &simple_patterns[*args_start..*args_end],
                ),
            )),
        }
    }
}

/// Views the identifier in the arena text and indices.
#[inline]
fn ident_view<'a>(text: &'a [u8], indices: &'a [IndexHandle], ident: IdentHandle) -> SmtIdent<'a> {
    SmtIdent {
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
/// can create [SmtMultiple] or [SmtNamedValues].
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
    /// Views the bytes as a keyword.
    #[inline]
    pub(crate) fn keyword_view(self, text: &[u8]) -> SmtKeyword<'_> {
        SmtKeyword::new_unchecked(&text[self.start..self.start + self.len])
    }

    /// Views the bytes as a numeral.
    #[inline]
    pub(crate) fn numeral_view(self, text: &[u8]) -> SmtNumeral<'_> {
        SmtNumeral::new_unchecked(&text[self.start..self.start + self.len])
    }
}

/// A symbol with is-quoted information in the arena text.
///
/// The quoted symbols are stored with a non-content pipe
/// at the start of the arena. This type makes sure that
/// the symbols are not produced as text, which could
/// silently convert a quoted symbol into an unquoted one.
///
/// This type is created by [SymbolHandle::create_by_push],
/// and returns the proper symbol view.
#[derive(Clone, Copy, Debug)]
pub(crate) struct SymbolHandle(TextHandle);

impl SymbolHandle {
    /// Start of the symbol in the text arena, including the quoting pipe if present.
    #[inline]
    pub(crate) fn start(self) -> usize {
        self.0.start
    }

    /// Views the bytes as a symbol.
    #[inline]
    pub(crate) fn symbol_view(self, text: &[u8]) -> SmtSymbol<'_> {
        let TextHandle { start, len } = self.0;
        let end = start + len;
        if text[start] == b'|' {
            // quoted symbol, skip the marker pipe
            SmtSymbol::new_unchecked(true, &text[start + 1..end])
        } else {
            // unquoted symbol
            SmtSymbol::new_unchecked(false, &text[start..end])
        }
    }

    /// Pushes the symbol into `text`.
    ///
    /// A quoted symbol is represented with a leading pipe.
    pub(crate) fn create_by_push(text: &mut Vec<u8>, symbol: SmtSymbol) -> SymbolHandle {
        let start = text.len();
        if symbol.is_quoted() {
            text.push(b'|');
        }
        text.extend_from_slice(symbol.as_slice());
        SymbolHandle(TextHandle {
            start,
            len: text.len() - start,
        })
    }
}

/// An identifier index in the arena text.
#[derive(Clone, Copy, Debug)]
pub(crate) enum IndexHandle {
    Numeral(TextHandle),
    Symbol(SymbolHandle),
}

impl IndexHandle {
    /// Views the index.
    #[inline]
    pub(crate) fn view(self, text: &[u8]) -> SmtIndex<'_> {
        match self {
            IndexHandle::Numeral(handle) => SmtIndex::Numeral(handle.numeral_view(text)),
            IndexHandle::Symbol(handle) => SmtIndex::Symbol(handle.symbol_view(text)),
        }
    }

    /// Pushes the index into `text`.
    pub(crate) fn create_by_push(text: &mut Vec<u8>, index: SmtIndex) -> IndexHandle {
        match index {
            SmtIndex::Numeral(numeral) => {
                let start = text.len();
                text.extend_from_slice(numeral.as_slice());
                IndexHandle::Numeral(TextHandle {
                    start,
                    len: text.len() - start,
                })
            }
            SmtIndex::Symbol(symbol) => {
                IndexHandle::Symbol(SymbolHandle::create_by_push(text, symbol))
            }
        }
    }
}

/// An identifier in the arena: its name in the text, its indices
/// in the arena indices starting at the given position.
#[derive(Clone, Copy, Debug)]
pub(crate) struct IdentHandle {
    pub(crate) name: SymbolHandle,
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
    Symbol(SymbolHandle),
    Wildcard,
}

impl SimplePatternHandle {
    /// Views the simple pattern.
    #[inline]
    pub(crate) fn view(self, text: &[u8]) -> SmtSimplePattern<'_> {
        match self {
            SimplePatternHandle::Symbol(handle) => {
                SmtSimplePattern::Symbol(handle.symbol_view(text))
            }
            SimplePatternHandle::Wildcard => SmtSimplePattern::Wildcard,
        }
    }

    /// Pushes the simple pattern into `text`.
    pub(crate) fn create_by_push(
        text: &mut Vec<u8>,
        pattern: SmtSimplePattern,
    ) -> SimplePatternHandle {
        match pattern {
            SmtSimplePattern::Symbol(symbol) => {
                SimplePatternHandle::Symbol(SymbolHandle::create_by_push(text, symbol))
            }
            SmtSimplePattern::Wildcard => SimplePatternHandle::Wildcard,
        }
    }
}

/// A parsed match pattern: a simple pattern from its token, or a constructor
/// application with the constructor in the arena text and the arguments in the
/// arena simple patterns from the given position onward.
pub(crate) enum PatternHandle<'t> {
    Simple(SmtSimplePattern<'t>),
    Application {
        constructor: SymbolHandle,
        args_start: usize,
        args_end: usize,
    },
}
#[derive(Clone, Copy)]
pub(crate) enum PatternHandleBuf {
    Simple(SimplePatternHandle),
    Application {
        constructor: SymbolHandle,
        args_start: usize,
        args_end: usize,
    },
}

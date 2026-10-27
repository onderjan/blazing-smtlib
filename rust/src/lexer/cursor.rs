use std::fmt;

use crate::{
    SmtVersion,
    span::SmtSpan,
    token::{SmtCursor, SmtLookahead, SmtToken, SmtTokenCategory, SmtVersionRefused},
};

/// Lexer token.
///
/// Lexer tokens are given out by [SmtLexerCursor]. Each token includes its
/// location span and can be viewed as [SmtToken](crate::token::SmtToken) via
/// [SmtCursor::syntax] on [SmtLexerCursor].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SmtLexerToken<'a> {
    /// Entry where End of File is kept as None.
    ///
    /// This is for performance reasons: instead of having to
    /// overwrite the whole token when the referenced buffer
    /// is no longer available, we have to only overwrite
    /// the Option variant byte to None.
    entry: &'a Option<(InnerCategory, &'a [u8])>,
    span: &'a SmtSpan,
}

impl<'a> SmtLexerToken<'a> {
    #[inline]
    pub(crate) fn new(
        entry: &'a Option<(InnerCategory, &'a [u8])>,
        span: &'a SmtSpan,
    ) -> SmtLexerToken<'a> {
        Self { entry, span }
    }

    #[inline]
    pub fn category(&self) -> SmtTokenCategory {
        match self.entry {
            Some((ty, _)) => ty.into_category(),
            None => SmtTokenCategory::EndOfFile,
        }
    }

    #[inline]
    pub fn content(&self) -> &'a [u8] {
        match self.entry {
            Some((_, content)) => content,
            None => &[],
        }
    }

    #[inline]
    pub fn span(&self) -> SmtSpan {
        *self.span
    }
}

/// SmtTokenCategory but without End of File.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InnerCategory {
    ParenOpen,
    ParenClose,
    Numeral,
    Decimal,
    Hexadecimal,
    Binary,
    String,
    Keyword,
    UnquotedSymbol,
    QuotedSymbol,
    Whitespace,
    Comment,
}

impl InnerCategory {
    fn into_category(self) -> SmtTokenCategory {
        match self {
            InnerCategory::ParenOpen => SmtTokenCategory::ParenOpen,
            InnerCategory::ParenClose => SmtTokenCategory::ParenClose,
            InnerCategory::Numeral => SmtTokenCategory::Numeral,
            InnerCategory::Decimal => SmtTokenCategory::Decimal,
            InnerCategory::Hexadecimal => SmtTokenCategory::Hexadecimal,
            InnerCategory::Binary => SmtTokenCategory::Binary,
            InnerCategory::String => SmtTokenCategory::String,
            InnerCategory::Keyword => SmtTokenCategory::Keyword,
            InnerCategory::UnquotedSymbol => SmtTokenCategory::UnquotedSymbol,
            InnerCategory::QuotedSymbol => SmtTokenCategory::QuotedSymbol,
            InnerCategory::Whitespace => SmtTokenCategory::Whitespace,
            InnerCategory::Comment => SmtTokenCategory::Comment,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LexerCursorAction {
    None,
    Relex,
    Discard,
}

/// Cursor into a batch of lexer tokens.
///
/// A parser reads a batch through a cursor: it consumes the tokens one at
/// a time, can look at the next one, and can attempt to take several at once.
/// However, it is not guaranteed how many tokens the batch will actually have,
/// so an attempt is only useful for fast paths that fall back to slow paths
/// with the same behaviour if the tokens are not available.
pub struct SmtLexerCursor<'a> {
    version: SmtVersion,
    entries: &'a [Option<(InnerCategory, &'a [u8])>],
    spans: &'a [SmtSpan],
    start: usize,
    next: usize,
    action: LexerCursorAction,
}

impl fmt::Debug for SmtLexerCursor<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SmtLexerCursor")
            .field("version", &self.version)
            .finish_non_exhaustive()
    }
}

impl<'a> SmtLexerCursor<'a> {
    /// Returns a cursor at the start of the batch given as its entries and
    /// their spans, of equal length.
    #[inline]
    pub(crate) fn new(
        version: SmtVersion,
        entries: &'a [Option<(InnerCategory, &'a [u8])>],
        spans: &'a [SmtSpan],
    ) -> Self {
        debug_assert_eq!(entries.len(), spans.len());
        Self {
            version,
            entries,
            spans,
            start: 0,
            next: 0,
            action: LexerCursorAction::None,
        }
    }

    /// The token at `index` of the batch, if any.
    #[inline]
    fn at(&self, index: usize) -> Option<SmtLexerToken<'a>> {
        match (self.entries.get(index), self.spans.get(index)) {
            (Some(entry), Some(span)) => Some(SmtLexerToken::new(entry, span)),
            _ => None,
        }
    }

    /// Span of the last consumed token in this handover (if any).
    #[inline]
    pub(crate) fn consumed_span(&self) -> Option<SmtSpan> {
        if self.next > self.start {
            self.at(self.next - 1).map(|token| token.span())
        } else {
            None
        }
    }

    // Ensures no more tokens are produced.
    #[inline]
    fn truncate(&mut self) {
        self.entries = &self.entries[..self.next];
        self.spans = &self.spans[..self.next];
    }

    #[inline]
    pub(crate) fn action(&self) -> LexerCursorAction {
        self.action
    }

    /// The entries of the tokens of the batch consumed so far.
    #[inline]
    pub(crate) fn consumed_entries(&self) -> &'a [Option<(InnerCategory, &'a [u8])>] {
        &self.entries[..self.next]
    }

    /// Resets the number of consumed tokens to zero.
    #[inline]
    pub(crate) fn reset_consumed(&mut self) {
        self.start = self.next;
    }
}

impl<'a> SmtCursor for SmtLexerCursor<'a> {
    type Token = SmtLexerToken<'a>;
    type Lookahead = SmtLexerWindow<'a>;

    #[inline]
    fn syntax<'t>(&self, token: &'t SmtLexerToken) -> SmtToken<'t> {
        SmtToken::from_lexer_token(*token, self.version)
    }

    #[inline]
    fn peek(&self) -> Option<SmtLexerToken<'a>> {
        self.at(self.next)
    }

    #[allow(clippy::should_implement_trait)]
    #[inline]
    fn next(&mut self) -> Option<SmtLexerToken<'a>> {
        let token = self.at(self.next)?;
        self.next += 1;
        Some(token)
    }

    #[inline]
    fn attempt<R>(&mut self, extract: impl Fn(&mut SmtLexerWindow<'a>) -> Option<R>) -> Option<R> {
        let mut window = SmtLexerWindow {
            version: self.version,
            entries: self.entries,
            spans: self.spans,
            next: self.next,
        };
        let result = extract(&mut window)?;
        // the extractor succeeded, consume what it took
        self.next = window.next;
        Some(result)
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.next >= self.entries.len()
    }

    #[inline]
    fn consume_all(&mut self) {
        self.next = self.entries.len()
    }

    fn version(&self) -> SmtVersion {
        self.version
    }

    fn set_version(&mut self, version: SmtVersion) -> Result<(), SmtVersionRefused> {
        // the lexer supports all versions,
        // but needs to relex when switching between 2.0 and 2.5+
        let is_current_2_0 = self.version == SmtVersion::V2_0;
        let is_new_2_0 = version == SmtVersion::V2_0;
        if is_current_2_0 != is_new_2_0 {
            // we need to relex; if already relexing/discarding, do nothing
            if matches!(self.action, LexerCursorAction::None) {
                self.truncate();
                self.action = LexerCursorAction::Relex;
            }
        }
        self.version = version;
        Ok(())
    }

    fn discard_rest(&mut self) {
        // just truncate and set to discard
        self.truncate();
        self.action = LexerCursorAction::Discard;
    }
}

/// Lookahead window for an attempt to extract tokens from a lexer cursor.
///
/// This window is given by [SmtLexerCursor] to the extraction function passed
/// to [SmtLexerCursor::attempt] so it can attempt extraction of multiple tokens.
pub struct SmtLexerWindow<'a> {
    version: SmtVersion,
    entries: &'a [Option<(InnerCategory, &'a [u8])>],
    spans: &'a [SmtSpan],
    next: usize,
}

impl<'a> fmt::Debug for SmtLexerWindow<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SmtLexerWindow").finish_non_exhaustive()
    }
}

impl<'a> SmtLookahead<SmtLexerToken<'a>> for SmtLexerWindow<'a> {
    fn next(&mut self) -> Option<SmtLexerToken<'a>> {
        let token = match (self.entries.get(self.next), self.spans.get(self.next)) {
            (Some(entry), Some(span)) => SmtLexerToken::new(entry, span),
            _ => return None,
        };
        self.next += 1;
        Some(token)
    }

    fn syntax<'t>(&self, token: &'t SmtLexerToken<'a>) -> SmtToken<'t> {
        SmtToken::from_lexer_token(*token, self.version)
    }
}

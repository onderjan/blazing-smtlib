use std::ops::ControlFlow;

use crate::{
    SmtBinDigitsView, SmtCommentView, SmtDecimalView, SmtHexDigitsView, SmtKeywordView,
    SmtLocation, SmtNumeralView, SmtSpan, SmtStringContentView, SmtSymbolView, SmtWhitespaceView,
};

mod reserved;

pub use reserved::{SmtCommandNameReserved, SmtGeneralReserved, SmtReserved};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtTokenCategory {
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
    // PERFORMANCE: leave EOF last for easy construction
    // from InnerCategory in the lexer
    EndOfFile,
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
pub enum SmtSyntaxToken<'a> {
    ParenOpen,
    ParenClose,
    Numeral(SmtNumeralView<'a>),
    Decimal(SmtDecimalView<'a>),
    Hexadecimal(SmtHexDigitsView<'a>),
    Binary(SmtBinDigitsView<'a>),
    String(SmtStringContentView<'a>),
    Keyword(SmtKeywordView<'a>),
    Symbol(SmtSymbolView<'a>),
    Reserved(SmtReserved),
    Whitespace(SmtWhitespaceView<'a>),
    Comment(SmtCommentView<'a>),
    EndOfFile,
}

/// Version of the SMT-LIB standard.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, PartialOrd, Ord)]
pub enum SmtVersion {
    V2_0,
    V2_5,
    V2_6,
    #[default]
    V2_7,
}

impl SmtVersion {
    pub fn from_decimal_opt(decimal: &[u8]) -> Option<Self> {
        match decimal {
            b"2.0" => Some(SmtVersion::V2_0),
            b"2.5" => Some(SmtVersion::V2_5),
            b"2.6" => Some(SmtVersion::V2_6),
            b"2.7" => Some(SmtVersion::V2_7),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtVersionPosture {
    allowed: Vec<SmtVersion>,
    max_declarations: Option<u64>,
}

impl SmtVersionPosture {
    pub fn allowed(&self) -> &[SmtVersion] {
        &self.allowed
    }

    pub fn max_declarations(&self) -> Option<u64> {
        self.max_declarations
    }
}

impl Default for SmtVersionPosture {
    fn default() -> Self {
        SmtVersionPostureBuilder::new().build()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtVersionPostureBuilder {
    allowed: Vec<SmtVersion>,
    max_declarations: Option<u64>,
}

impl SmtVersionPostureBuilder {
    pub fn new() -> Self {
        Self {
            allowed: vec![SmtVersion::V2_5, SmtVersion::V2_6, SmtVersion::V2_7],
            max_declarations: Some(1),
        }
    }

    pub fn allowed(&self) -> &[SmtVersion] {
        &self.allowed
    }

    pub fn max_declarations(&self) -> Option<u64> {
        self.max_declarations
    }

    pub fn clear_allowed(&mut self) -> &mut Self {
        self.allowed.clear();
        self
    }

    pub fn add_allowed(&mut self, allowed: SmtVersion) -> &mut Self {
        self.allowed.push(allowed);
        self
    }

    pub fn remove_allowed(&mut self, allowed: SmtVersion) -> &mut Self {
        while let Some(index) = self.allowed.iter().position(|elem| *elem == allowed) {
            self.allowed.remove(index);
        }
        self
    }

    pub fn set_max_declarations(&mut self, max_declarations: Option<u64>) -> &mut Self {
        self.max_declarations = max_declarations;
        self
    }

    pub fn build(self) -> SmtVersionPosture {
        SmtVersionPosture {
            allowed: self.allowed,
            max_declarations: self.max_declarations,
        }
    }
}

impl Default for SmtVersionPostureBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a> SmtSyntaxToken<'a> {
    /// Construct the token kind from the token and version.
    #[inline]
    pub fn from_token(token: SmtToken<'a>, version: SmtVersion) -> Self {
        let content = token.content();
        match token.category() {
            SmtTokenCategory::ParenOpen => SmtSyntaxToken::ParenOpen,
            SmtTokenCategory::ParenClose => SmtSyntaxToken::ParenClose,
            SmtTokenCategory::Numeral => {
                SmtSyntaxToken::Numeral(SmtNumeralView::new_unchecked(content))
            }
            SmtTokenCategory::Decimal => {
                SmtSyntaxToken::Decimal(SmtDecimalView::new_unchecked(content))
            }
            SmtTokenCategory::Hexadecimal => {
                SmtSyntaxToken::Hexadecimal(SmtHexDigitsView::new_unchecked(content))
            }
            SmtTokenCategory::Binary => {
                SmtSyntaxToken::Binary(SmtBinDigitsView::new_unchecked(content))
            }
            SmtTokenCategory::UnquotedSymbol => {
                // only the words reserved in the version are reserved words
                if let Some(reserved) = SmtReserved::from_bytes_opt(content, version) {
                    SmtSyntaxToken::Reserved(reserved)
                } else {
                    SmtSyntaxToken::Symbol(SmtSymbolView::new_unchecked(content))
                }
            }
            SmtTokenCategory::QuotedSymbol => {
                SmtSyntaxToken::Symbol(SmtSymbolView::new_unchecked(content))
            }
            SmtTokenCategory::String => {
                SmtSyntaxToken::String(SmtStringContentView::new_unchecked(content))
            }
            SmtTokenCategory::Keyword => {
                SmtSyntaxToken::Keyword(SmtKeywordView::new_unchecked(content))
            }
            SmtTokenCategory::Whitespace => {
                SmtSyntaxToken::Whitespace(SmtWhitespaceView::new_unchecked(content))
            }
            SmtTokenCategory::Comment => {
                SmtSyntaxToken::Comment(SmtCommentView::new_unchecked(content))
            }
            SmtTokenCategory::EndOfFile => SmtSyntaxToken::EndOfFile,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SmtToken<'a> {
    /// Entry where End of File is kept as None.
    ///
    /// This is for performance reasons: instead of having to
    /// overwrite the whole token when the referenced buffer
    /// is no longer available, we have to only overwrite
    /// the Option variant byte to None.
    entry: &'a Option<(InnerCategory, &'a [u8])>,
    span: &'a SmtSpan,
}

impl<'a> SmtToken<'a> {
    #[inline]
    pub(crate) fn new(
        entry: &'a Option<(InnerCategory, &'a [u8])>,
        span: &'a SmtSpan,
    ) -> SmtToken<'a> {
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

    #[inline]
    pub fn syntax(self, version: SmtVersion) -> SmtSyntaxToken<'a> {
        SmtSyntaxToken::from_token(self, version)
    }
}

/// A cursor into a batch of tokens, from which elements are consumed sequentially.
///
/// A parser reads a batch through a cursor: it consumes the tokens one at
/// a time, can look at the next one, and can attempt to take several at once.
/// However, it is not guaranteed how many tokens the batch will actually have,
/// so an attempt is only useful for fast paths that fall back to slow paths
/// with the same behaviour if the tokens are not available.
pub struct SmtBatchCursor<'a> {
    version: SmtVersion,
    entries: &'a [Option<(InnerCategory, &'a [u8])>],
    spans: &'a [SmtSpan],
    start: usize,
    next: usize,
    relex: bool,
}

impl<'a> SmtBatchCursor<'a> {
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
            relex: false,
        }
    }

    pub fn version(&self) -> SmtVersion {
        self.version
    }

    /// The token at `index` of the batch, if any.
    #[inline]
    fn at(&self, index: usize) -> Option<SmtToken<'a>> {
        match (self.entries.get(index), self.spans.get(index)) {
            (Some(entry), Some(span)) => Some(SmtToken::new(entry, span)),
            _ => None,
        }
    }

    /// Returns a cursor over a single token.
    ///
    /// This can be used for parsing one token using a cursor-parsing function.
    #[inline]
    pub fn single(version: SmtVersion, token: SmtToken<'a>) -> Self {
        Self::new(
            version,
            std::slice::from_ref(token.entry),
            std::slice::from_ref(token.span),
        )
    }

    /// Returns the next token (if any) without consuming it.
    #[inline]
    pub fn peek(&self) -> Option<SmtToken<'a>> {
        self.at(self.next)
    }

    /// Returns the token `ahead` positions after the next one without consuming anything.
    ///
    /// `get(0)` is the next token, also available through `peek`.
    #[inline]
    pub(crate) fn get(&self, ahead: usize) -> Option<SmtToken<'a>> {
        self.at(self.next + ahead)
    }

    /// Consumes the next token (if any).
    // CLIPPY: do not warn on next() without implementing Iterator,
    // as we implement an iterator-like but more powerful API
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn next(&mut self) -> Option<SmtToken<'a>> {
        let token = self.at(self.next)?;
        self.next += 1;
        Some(token)
    }

    /// Attempts to consume several tokens at once.
    ///
    /// The extractor takes tokens from the window ahead of the cursor, in order.
    /// If it returns [`Option::Some`], exactly the tokens it took are consumed.
    /// If it returns [`Option::None`], nothing is consumed.
    ///
    /// The window ends where the cursor does, which may be after any token.
    /// An extractor that runs out of tokens must return [`Option::None`]; the
    /// caller must then reach the same result by consuming token by token.
    #[inline]
    pub fn attempt<R>(
        &mut self,
        extract: impl Fn(&mut SmtTokenWindow<'a>) -> Option<R>,
    ) -> Option<R> {
        let mut window = SmtTokenWindow {
            entries: self.entries,
            spans: self.spans,
            next: self.next,
        };
        let result = extract(&mut window)?;
        // the extractor succeeded, consume what it took
        self.next = window.next;
        Some(result)
    }

    /// Consumes the next `count` tokens.
    ///
    /// Behaves as if [`SmtBatchCursor::next`] was called `count` times
    /// with the results discarded, stopping at the end of the cursor.
    #[inline]
    pub(crate) fn advance(&mut self, count: usize) {
        self.next = self.next.saturating_add(count).min(self.entries.len());
    }

    /// Returns the most recently consumed token in this handover (if any).
    #[inline]
    pub(crate) fn last_consumed(&self) -> Option<SmtToken<'a>> {
        if self.next > self.start {
            self.at(self.next - 1)
        } else {
            None
        }
    }

    /// Location of the end of the last consumed token in this handover (if any).
    #[inline]
    pub fn consumed_end(&self) -> Option<SmtLocation> {
        self.last_consumed().map(|token| token.span().end())
    }

    /// Consumes all tokens remaining in the cursor.
    #[inline]
    pub fn consume_all(&mut self) {
        self.next = self.entries.len()
    }

    /// Whether every token has been consumed.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.next >= self.entries.len()
    }

    /// Sets the SMT-LIB version that should apply from now on.
    ///
    /// This will adjust the non-consumed tokens so they correspond
    /// to the set version. There is no guarantee on their shape
    /// or whether any remain at all; the caller must not use any
    /// information gathered on them beforehand.
    pub fn set_version(&mut self, version: SmtVersion) {
        let is_current_2_0 = self.version == SmtVersion::V2_0;
        let is_new_2_0 = version == SmtVersion::V2_0;
        if is_current_2_0 != is_new_2_0 {
            // we need to relex
            self.relex();
        }
        self.version = version;
    }

    /// Requests that the input is lexed again from the end of the last
    /// consumed token.
    ///
    /// The tokens not consumed through this cursor are discarded and will be
    /// produced again by the lexer, so the cursor yields no more tokens:
    /// it is empty from now on, and the consumed count stays where it is.
    #[inline]
    pub(crate) fn relex(&mut self) {
        self.entries = &self.entries[..self.next];
        self.spans = &self.spans[..self.next];
        self.relex = true;
    }

    /// Whether [`SmtBatchCursor::relex`] has been called on this cursor.
    #[inline]
    pub(crate) fn relex_requested(&self) -> bool {
        self.relex
    }

    /// Resets the number of consumed tokens to zero.
    #[inline]
    pub(crate) fn reset_consumed(&mut self) {
        self.start = self.next;
    }
}

/// The tokens ahead of a cursor, as the extractor of [`SmtBatchCursor::attempt`]
/// sees them: they can only be taken in order.
pub struct SmtTokenWindow<'a> {
    entries: &'a [Option<(InnerCategory, &'a [u8])>],
    spans: &'a [SmtSpan],
    next: usize,
}

impl<'a> SmtTokenWindow<'a> {
    /// Takes the next token of the window (if any).
    // CLIPPY: do not warn on next() without implementing Iterator,
    // as the window mirrors the cursor it belongs to
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn next(&mut self) -> Option<SmtToken<'a>> {
        let token = match (self.entries.get(self.next), self.spans.get(self.next)) {
            (Some(entry), Some(span)) => SmtToken::new(entry, span),
            _ => return None,
        };
        self.next += 1;
        Some(token)
    }
}

/// A sequential consumer of tokens.
pub trait SmtConsume {
    /// The value the consumer finishes with.
    type Result;
    /// The error emitted by the consumer.
    type Error;
    /// Whether the consumer consumes whitespace and comments.
    ///
    /// If false, the consumer operates over abstract tokens:
    /// it is not interested in whitespace and comments,
    /// and the caller must not hand them over for consumption.
    ///
    /// If true, the consumer operates over concrete tokens:
    /// it can reconstruct the byte stream precisely thanks
    /// to the whitespace and comments. The caller must hand
    /// over the whitespace and comment tokens present between
    /// true syntactic tokens.
    const CONSUMES_WHITESPACE_AND_COMMENTS: bool;

    /// Consumes the tokens handed over in the cursor, in order.
    ///
    /// The caller must ensure that the cursor contains at least one token.
    /// The consumer must ensure that at least one token is consumed before
    /// return, no matter the result (even when returning an error).
    ///
    /// If the consumer returns [`ControlFlow::Continue`], the consumer is
    /// not finished yet and is ready to consume more tokens. Tokens that
    /// remain unconsumed in the cursor must be handed over again before
    /// any new ones.
    ///
    /// If the consumer returns [`ControlFlow::Break`], it has finished
    /// consuming the current value, is returning a result, and is ready
    /// to start consuming a new value.
    ///
    /// If the consumer returns [`Result::Err`], it has failed at the last
    /// consumed token. The state of the consumer is unspecified.
    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error>;
}

/// Mutable references over token consumers are token consumers.
impl<T: SmtConsume + ?Sized> SmtConsume for &mut T {
    type Result = T::Result;
    type Error = T::Error;
    const CONSUMES_WHITESPACE_AND_COMMENTS: bool = T::CONSUMES_WHITESPACE_AND_COMMENTS;

    #[inline]
    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        (**self).consume(cursor)
    }
}

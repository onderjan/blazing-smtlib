use std::ops::ControlFlow;

use crate::{
    SmtBinDigitsView, SmtDecimalView, SmtHexDigitsView, SmtKeywordView, SmtNumeralView, SmtSpan,
    SmtStringContentView, SmtSymbolView,
};

mod reserved;

pub use reserved::{CommandNameReserved, GeneralReserved, Reserved};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenType {
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
    // PERFORMANCE: leave EOF last for easy construction
    // from InnerType in the lexer
    EndOfFile,
}

/// TokenType but without End of File.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InnerType {
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
}

impl InnerType {
    fn into_type(self) -> TokenType {
        match self {
            InnerType::ParenOpen => TokenType::ParenOpen,
            InnerType::ParenClose => TokenType::ParenClose,
            InnerType::Numeral => TokenType::Numeral,
            InnerType::Decimal => TokenType::Decimal,
            InnerType::Hexadecimal => TokenType::Hexadecimal,
            InnerType::Binary => TokenType::Binary,
            InnerType::String => TokenType::String,
            InnerType::Keyword => TokenType::Keyword,
            InnerType::UnquotedSymbol => TokenType::UnquotedSymbol,
            InnerType::QuotedSymbol => TokenType::QuotedSymbol,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind<'a> {
    ParenOpen,
    ParenClose,
    Numeral(SmtNumeralView<'a>),
    Decimal(SmtDecimalView<'a>),
    Hexadecimal(SmtHexDigitsView<'a>),
    Binary(SmtBinDigitsView<'a>),
    String(SmtStringContentView<'a>),
    Keyword(SmtKeywordView<'a>),
    Symbol(SmtSymbolView<'a>),
    Reserved(Reserved),
    EndOfFile,
}

/// Version of the SMT-LIB standard.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum SmtVersion {
    V2_5,
    V2_6,
    #[default]
    V2_7,
}

impl SmtVersion {
    pub fn from_decimal_opt(decimal: &[u8]) -> Option<Self> {
        match decimal {
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

impl<'a> TokenKind<'a> {
    /// Construct the token kind from the token and version.
    #[inline]
    pub fn from_token(token: Token<'a>, version: SmtVersion) -> Self {
        let content = token.content();
        match token.ty() {
            TokenType::ParenOpen => TokenKind::ParenOpen,
            TokenType::ParenClose => TokenKind::ParenClose,
            TokenType::Numeral => TokenKind::Numeral(SmtNumeralView::new_unchecked(content)),
            TokenType::Decimal => TokenKind::Decimal(SmtDecimalView::new_unchecked(content)),
            TokenType::Hexadecimal => {
                TokenKind::Hexadecimal(SmtHexDigitsView::new_unchecked(content))
            }
            TokenType::Binary => TokenKind::Binary(SmtBinDigitsView::new_unchecked(content)),
            TokenType::UnquotedSymbol => {
                // filter the reserved words by the version
                if let Some(reserved) = Reserved::from_bytes_opt(content)
                    .filter(|reserved| reserved.is_in_version(version))
                {
                    TokenKind::Reserved(reserved)
                } else {
                    TokenKind::Symbol(SmtSymbolView::new_unchecked(content))
                }
            }
            TokenType::QuotedSymbol => TokenKind::Symbol(SmtSymbolView::new_unchecked(content)),
            TokenType::String => TokenKind::String(SmtStringContentView::new_unchecked(content)),
            TokenType::Keyword => TokenKind::Keyword(SmtKeywordView::new_unchecked(content)),
            TokenType::EndOfFile => TokenKind::EndOfFile,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token<'a> {
    /// Entry where End of File is kept as None.
    ///
    /// This is for performance reasons: instead of having to
    /// overwrite the whole token when the referenced buffer
    /// is no longer available, we have to only overwrite
    /// the Option variant byte to None.
    entry: &'a Option<(InnerType, &'a [u8])>,
    span: &'a SmtSpan,
}

impl<'a> Token<'a> {
    #[inline]
    pub(crate) fn new(entry: &'a Option<(InnerType, &'a [u8])>, span: &'a SmtSpan) -> Token<'a> {
        Self { entry, span }
    }

    #[inline]
    pub fn ty(&self) -> TokenType {
        match self.entry {
            Some((ty, _)) => ty.into_type(),
            None => TokenType::EndOfFile,
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
    pub fn kind(self, version: SmtVersion) -> TokenKind<'a> {
        TokenKind::from_token(self, version)
    }
}

/// A cursor into a batch of tokens, from which elements are consumed sequentially.
///
/// A parser reads a batch through a cursor: it can look at the
/// tokens ahead, consume them one at a time or several at once, look back at
/// what it consumed last, and tell how many tokens it has taken. However,
/// it is not guaranteed how many elements the batch will actually have,
/// so the lookahead is only useful for fast paths that fall back to
/// slow paths with the same behaviour if the lookahead is not available.
#[derive(Clone, Copy)]
pub struct TokenCursor<'a> {
    version: SmtVersion,
    entries: &'a [Option<(InnerType, &'a [u8])>],
    spans: &'a [SmtSpan],
    next: usize,
    relex: bool,
}

impl<'a> TokenCursor<'a> {
    /// Returns a cursor at the start of the batch given as its entries and
    /// their spans, of equal length.
    #[inline]
    pub(crate) fn new(
        version: SmtVersion,
        entries: &'a [Option<(InnerType, &'a [u8])>],
        spans: &'a [SmtSpan],
    ) -> Self {
        debug_assert_eq!(entries.len(), spans.len());
        Self {
            version,
            entries,
            spans,
            next: 0,
            relex: false,
        }
    }

    pub fn version(&self) -> SmtVersion {
        self.version
    }

    /// The token at `index` of the batch, if any.
    #[inline]
    fn at(&self, index: usize) -> Option<Token<'a>> {
        match (self.entries.get(index), self.spans.get(index)) {
            (Some(entry), Some(span)) => Some(Token::new(entry, span)),
            _ => None,
        }
    }

    /// Returns a cursor over a single token.
    ///
    /// This can be used for parsing one token using a cursor-parsing function.
    #[inline]
    pub fn single(version: SmtVersion, token: Token<'a>) -> Self {
        Self::new(
            version,
            std::slice::from_ref(token.entry),
            std::slice::from_ref(token.span),
        )
    }

    /// Returns the next token (if any) without consuming it.
    #[inline]
    pub fn peek(&self) -> Option<Token<'a>> {
        self.at(self.next)
    }

    /// Returns the token `ahead` positions after the next one without consuming anything.
    ///
    /// `get(0)` is the next token, also available through `peek`.
    #[inline]
    pub fn get(&self, ahead: usize) -> Option<Token<'a>> {
        self.at(self.next + ahead)
    }

    /// Consumes the next token (if any).
    // CLIPPY: do not warn on next() without implementing Iterator,
    // as we implement an iterator-like but more powerful API
    #[allow(clippy::should_implement_trait)]
    #[inline]
    pub fn next(&mut self) -> Option<Token<'a>> {
        let token = self.at(self.next)?;
        self.next += 1;
        Some(token)
    }

    /// Consumes the next `count` tokens.
    ///
    /// Behaves as if [`TokenCursor::next`] was called `count` times
    /// with the results discarded, stopping at the end of the cursor.
    #[inline]
    pub fn advance(&mut self, count: usize) {
        self.next = self.next.saturating_add(count).min(self.entries.len());
    }

    /// Consumes all tokens remaining in the cursor.
    #[inline]
    pub fn consume_all(&mut self) {
        self.next = self.entries.len()
    }

    /// Returns the most recently consumed token, if any was consumed through
    /// this cursor.
    #[inline]
    pub fn last_consumed(&self) -> Option<Token<'a>> {
        self.at(self.next.checked_sub(1)?)
    }

    /// How many tokens have been consumed.
    #[inline]
    pub fn consumed(&self) -> usize {
        self.next
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
        // TODO: relex on 2.0/2.5+ switch
        self.version = version;
    }

    /// Requests that the input is lexed again from the end of the last
    /// consumed token.
    ///
    /// The tokens not consumed through this cursor are discarded and will be
    /// produced again by the lexer, so the cursor yields no more tokens:
    /// it is empty from now on, and the consumed count stays where it is.
    #[inline]
    pub fn relex(&mut self) {
        self.entries = &self.entries[..self.next];
        self.spans = &self.spans[..self.next];
        self.relex = true;
    }

    /// Whether [`TokenCursor::relex`] has been called on this cursor.
    #[inline]
    pub fn relex_requested(&self) -> bool {
        self.relex
    }
}

/// A sequential handler of tokens.
pub trait TokenHandler {
    /// The value the handler finishes with.
    type Result;
    type Error;

    /// Handles the tokens handed over in the cursor, in order.
    ///
    /// If the handler returns [`ControlFlow::Continue`], it means all tokens
    /// were handled and more are wanted: the cursor must be empty, which it
    /// also is after a [`TokenCursor::relex`] request.
    ///
    /// If the handler returns [`ControlFlow::Break`], it means
    /// it finished the input it accepts (consuming exactly its tokens),
    /// is returning a result and waiting for processing of the next value.
    ///
    /// Returning an error means the handler failed at the token after
    /// the consumed ones. The state of the handler and cursor is unspecified.
    fn handle_tokens(
        &mut self,
        cursor: &mut TokenCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error>;
}

/// Mutable references over token handlers are token handlers.
impl<T: TokenHandler + ?Sized> TokenHandler for &mut T {
    type Result = T::Result;
    type Error = T::Error;

    #[inline]
    fn handle_tokens(
        &mut self,
        cursor: &mut TokenCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        (**self).handle_tokens(cursor)
    }
}

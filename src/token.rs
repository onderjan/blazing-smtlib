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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtVersion {
    V2_7,
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
                // process reserved words
                // TODO: multiple versions
                match version {
                    SmtVersion::V2_7 => {
                        match Reserved::from_bytes_opt(content) {
                            Some(reserved) => {
                                // reserved word, not a symbol
                                TokenKind::Reserved(reserved)
                            }
                            None => TokenKind::Symbol(SmtSymbolView::new_unchecked(content)),
                        }
                    }
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
    entries: &'a [Option<(InnerType, &'a [u8])>],
    spans: &'a [SmtSpan],
    next: usize,
}

impl<'a> TokenCursor<'a> {
    /// Returns a cursor at the start of the batch given as its entries and
    /// their spans, of equal length.
    #[inline]
    pub(crate) fn new(entries: &'a [Option<(InnerType, &'a [u8])>], spans: &'a [SmtSpan]) -> Self {
        debug_assert_eq!(entries.len(), spans.len());
        Self {
            entries,
            spans,
            next: 0,
        }
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
    pub fn single(token: Token<'a>) -> Self {
        Self::new(
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
    #[inline]
    pub fn take(&mut self) -> Option<Token<'a>> {
        let token = self.at(self.next)?;
        self.next += 1;
        Some(token)
    }

    /// Consumes the next `count` tokens.
    ///
    /// Behaves as if [`TokenCursor::take`] was called `count` times
    /// with the results discarded, stopping at the end of the cursor.
    #[inline]
    pub fn advance(&mut self, count: usize) {
        self.next = self.next.saturating_add(count).min(self.entries.len());
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
}

/// A sequential handler of tokens.
pub trait TokenHandler {
    type Error;

    /// Handles the tokens handed over in the cursor, in order.
    ///
    /// Returning `Ok(())` means all tokens were handled: the cursor must
    /// be empty. Returning a [`TokenStop`] leaves the cursor after the
    /// last consumed token, which is where the stop takes effect.
    fn handle_tokens(&mut self, cursor: &mut TokenCursor<'_>)
    -> Result<(), TokenStop<Self::Error>>;
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokenStop<E> {
    /// Lex again from the end of the last consumed token.
    Relex,
    /// The handler failed at the token after the consumed ones.
    Error(E),
}

/// Mutable references over token handlers are token handlers.
impl<T: TokenHandler + ?Sized> TokenHandler for &mut T {
    type Error = T::Error;

    #[inline]
    fn handle_tokens(
        &mut self,
        cursor: &mut TokenCursor<'_>,
    ) -> Result<(), TokenStop<Self::Error>> {
        (**self).handle_tokens(cursor)
    }
}

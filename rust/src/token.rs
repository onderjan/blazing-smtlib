use std::ops::ControlFlow;

use crate::{
    SmtBinDigits, SmtComment, SmtDecimal, SmtHexDigits, SmtKeyword, SmtLocation, SmtNumeral,
    SmtSpan, SmtStringContent, SmtSymbol, SmtWhitespace,
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
    Numeral(SmtNumeral<'a>),
    Decimal(SmtDecimal<'a>),
    Hexadecimal(SmtHexDigits<'a>),
    Binary(SmtBinDigits<'a>),
    String(SmtStringContent<'a>),
    Keyword(SmtKeyword<'a>),
    Symbol(SmtSymbol<'a>),
    Reserved(SmtReserved),
    Whitespace(SmtWhitespace<'a>),
    Comment(SmtComment<'a>),
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
                SmtSyntaxToken::Numeral(SmtNumeral::new_unchecked(content))
            }
            SmtTokenCategory::Decimal => {
                SmtSyntaxToken::Decimal(SmtDecimal::new_unchecked(content))
            }
            SmtTokenCategory::Hexadecimal => {
                SmtSyntaxToken::Hexadecimal(SmtHexDigits::new_unchecked(content))
            }
            SmtTokenCategory::Binary => {
                SmtSyntaxToken::Binary(SmtBinDigits::new_unchecked(content))
            }
            SmtTokenCategory::UnquotedSymbol => {
                // only the words reserved in the version are reserved words
                if let Some(reserved) = SmtReserved::from_bytes_opt(content, version) {
                    SmtSyntaxToken::Reserved(reserved)
                } else {
                    SmtSyntaxToken::Symbol(SmtSymbol::new_unchecked(content))
                }
            }
            SmtTokenCategory::QuotedSymbol => {
                SmtSyntaxToken::Symbol(SmtSymbol::new_unchecked(content))
            }
            SmtTokenCategory::String => {
                SmtSyntaxToken::String(SmtStringContent::new_unchecked(content))
            }
            SmtTokenCategory::Keyword => {
                SmtSyntaxToken::Keyword(SmtKeyword::new_unchecked(content))
            }
            SmtTokenCategory::Whitespace => {
                SmtSyntaxToken::Whitespace(SmtWhitespace::new_unchecked(content))
            }
            SmtTokenCategory::Comment => {
                SmtSyntaxToken::Comment(SmtComment::new_unchecked(content))
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
}

/// Producer refused to switch to a requested version.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SmtVersionRefused;

/// A sequential producer of tokens.
pub trait SmtProduce {
    /// The user type of the token.
    ///
    /// The producer must implement [`SmtProduce::syntax`] to view
    /// the user token type as a library type.
    type Token: Copy;

    /// Lookahead window, set to `()` if not implementing [`SmtProduce::attempt`].
    type Lookahead: SmtLookahead<Self::Token>;

    /// Views the user token as a library token under the version in force.
    fn syntax<'t>(&self, token: &'t Self::Token) -> SmtSyntaxToken<'t>;

    /// Consumes the next token (if any).
    fn next(&mut self) -> Option<Self::Token>;

    /// Returns the next token (if any) without consuming it.
    ///
    /// Peeking must return [`Option::Some`] containing
    /// the next token that would be consumed if there
    /// is some such token waiting.
    ///
    /// Do not forget to consume the token later if it should be taken.
    fn peek(&self) -> Option<Self::Token>;

    /// Returns whether the producer has no tokens left to consume.
    ///
    /// This must be true exactly if [`SmtProduce::peek`] or
    /// [`SmtProduce::next`] would produce [`Option::None`].
    fn is_empty(&self) -> bool {
        self.peek().is_none()
    }

    /// Attempts to consume several tokens at once (lookahead).
    ///
    /// The extractor takes tokens from the window ahead of the cursor, in order.
    /// If it returns [`Option::Some`], exactly the tokens it took are consumed.
    /// If it returns [`Option::None`], nothing is consumed.
    /// An extractor that runs out of tokens must return [`Option::None`].
    /// The window may end after any token.
    ///
    /// This function can be provided for ultra-fast processing,
    /// and the caller must ensure that a successful attempt results in
    /// the same observable behaviour as when it failed one.
    /// Use standard [`SmtProduce::next`] processing unless
    /// absolutely necessary and supported by measurements.
    fn attempt<R>(&mut self, extract: impl Fn(&mut Self::Lookahead) -> Option<R>) -> Option<R> {
        let _ = extract;
        None
    }

    /// Consumes all tokens the producer has left to hand over.
    #[inline]
    fn consume_all(&mut self) {
        while self.next().is_some() {}
    }

    /// The SMT-LIB version that applies for currently consumed tokens.
    ///
    /// The version is guaranteed not to change during a call
    /// to the consumer except as a result of the consumer calling
    /// [`SmtProduce::set_version`] and the producer accepting.
    fn version(&self) -> SmtVersion;

    /// Sets the SMT-LIB version that should apply from now on.
    ///
    /// If the producer returns [`Result::Ok`], it has switched
    /// to the new version, and will return it in subsequent
    /// calls of [`SmtProduce::version`]. The version change
    /// applies between the last consumed and first unconsumed
    /// token, and the producer can adjust the non-consumed tokens
    /// so they correspond to the set version. There is no guarantee
    /// on their shape or whether any remain at all; the caller must
    /// not use any information gathered on them beforehand.
    ///
    /// If the producer returns [`Result::Err`], it has refused
    /// the version set request. It guarantees that no changes
    /// were made, as if the method was never called.
    fn set_version(&mut self, version: SmtVersion) -> Result<(), SmtVersionRefused>;

    /// Forces the producer to discard all tokens before an EOF token.
    ///
    /// It follows that the first produced token, if any, must be EOF.
    fn discard_rest(&mut self);
}

/// A lookahead window for [SmtProduce::attempt].
pub trait SmtLookahead<T> {
    /// Looks at the next token and advances the window.
    fn next(&mut self) -> Option<T>;

    /// Views the user token as a library token.
    fn syntax<'t>(&self, token: &'t T) -> SmtSyntaxToken<'t>;
}

impl<T> SmtLookahead<T> for () {
    fn next(&mut self) -> Option<T> {
        None
    }

    /// Views the user token as a library token.
    fn syntax<'t>(&self, _token: &'t T) -> SmtSyntaxToken<'t> {
        panic!("unit lookahead cannot view user token as it produces no tokens")
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BatchCursorAction {
    None,
    Relex,
    Discard,
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
    action: BatchCursorAction,
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
            action: BatchCursorAction::None,
        }
    }

    /// The token at `index` of the batch, if any.
    #[inline]
    fn at(&self, index: usize) -> Option<SmtToken<'a>> {
        match (self.entries.get(index), self.spans.get(index)) {
            (Some(entry), Some(span)) => Some(SmtToken::new(entry, span)),
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
    pub(crate) fn action(&self) -> BatchCursorAction {
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

impl<'a> SmtProduce for SmtBatchCursor<'a> {
    type Token = SmtToken<'a>;
    type Lookahead = SmtTokenWindow<'a>;

    #[inline]
    fn syntax<'t>(&self, token: &'t SmtToken) -> SmtSyntaxToken<'t> {
        SmtSyntaxToken::from_token(*token, self.version)
    }

    #[inline]
    fn peek(&self) -> Option<SmtToken<'a>> {
        self.at(self.next)
    }

    #[allow(clippy::should_implement_trait)]
    #[inline]
    fn next(&mut self) -> Option<SmtToken<'a>> {
        let token = self.at(self.next)?;
        self.next += 1;
        Some(token)
    }

    #[inline]
    fn attempt<R>(&mut self, extract: impl Fn(&mut SmtTokenWindow<'a>) -> Option<R>) -> Option<R> {
        let mut window = SmtTokenWindow {
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
            if matches!(self.action, BatchCursorAction::None) {
                self.truncate();
                self.action = BatchCursorAction::Relex;
            }
        }
        self.version = version;
        Ok(())
    }

    fn discard_rest(&mut self) {
        // just truncate and set to discard
        self.truncate();
        self.action = BatchCursorAction::Discard;
    }
}

/// The tokens ahead of a cursor, as the extractor of [`SmtBatchCursor::attempt`]
/// sees them: they can only be taken in order.
pub struct SmtTokenWindow<'a> {
    version: SmtVersion,
    entries: &'a [Option<(InnerCategory, &'a [u8])>],
    spans: &'a [SmtSpan],
    next: usize,
}

pub(crate) struct SingleTokenProducer<'a, P: SmtProduce> {
    cursor: &'a P,
    token: Option<P::Token>,
}

impl<'a, P: SmtProduce> SingleTokenProducer<'a, P> {
    pub fn new(cursor: &'a P, token: P::Token) -> Self {
        Self {
            cursor,
            token: Some(token),
        }
    }
}

impl<'a, P: SmtProduce> SmtProduce for SingleTokenProducer<'a, P> {
    type Token = P::Token;
    type Lookahead = ();

    fn syntax<'t>(&self, token: &'t Self::Token) -> SmtSyntaxToken<'t> {
        self.cursor.syntax(token)
    }

    fn next(&mut self) -> Option<Self::Token> {
        self.token.take()
    }

    fn peek(&self) -> Option<Self::Token> {
        self.token
    }

    fn version(&self) -> SmtVersion {
        self.cursor.version()
    }

    fn set_version(&mut self, _version: SmtVersion) -> Result<(), SmtVersionRefused> {
        // single-token producer does not support switching versions
        Err(SmtVersionRefused)
    }

    fn discard_rest(&mut self) {
        panic!("single-token producer cannot discard the rest of the input")
    }
}

impl<'a> SmtLookahead<SmtToken<'a>> for SmtTokenWindow<'a> {
    fn next(&mut self) -> Option<SmtToken<'a>> {
        let token = match (self.entries.get(self.next), self.spans.get(self.next)) {
            (Some(entry), Some(span)) => SmtToken::new(entry, span),
            _ => return None,
        };
        self.next += 1;
        Some(token)
    }

    fn syntax<'t>(&self, token: &'t SmtToken<'a>) -> SmtSyntaxToken<'t> {
        SmtSyntaxToken::from_token(*token, self.version)
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
    /// If true, the consumer operates over concrete tokens:
    /// it can reconstruct the byte stream precisely thanks
    /// to the whitespace and comments. The caller must hand
    /// over the whitespace and comment tokens present between
    /// true syntactic tokens.
    ///
    /// If false, the consumer operates over abstract tokens:
    /// it is not interested in whitespace and comments,
    /// and the caller must not hand them over for consumption.
    const IS_CONCRETE: bool;
}

/// A sequential consumer of tokens for given producers.
pub trait SmtConsumeFrom<Z: SmtProduce>: SmtConsume {
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
    fn consume(&mut self, cursor: &mut Z) -> Result<ControlFlow<Self::Result>, Self::Error>;
}

/// Mutable references over token consumers are token consumers.
impl<T: SmtConsume + ?Sized> SmtConsume for &mut T {
    type Result = T::Result;
    type Error = T::Error;
    const IS_CONCRETE: bool = T::IS_CONCRETE;
}

/// Mutable references over token consumers are token consumers.
impl<Z: SmtProduce, T: SmtConsumeFrom<Z> + ?Sized> SmtConsumeFrom<Z> for &mut T {
    #[inline]
    fn consume(&mut self, cursor: &mut Z) -> Result<ControlFlow<Self::Result>, Self::Error> {
        (**self).consume(cursor)
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

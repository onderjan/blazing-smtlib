//! Syntax tokens and traits for their manipulation.
//!
//! A token is one unit of SMT-LIB input, e.g. `(`, `|quoted|`, or `"string"`.
//! It is also a natural point around which **blazing-smtlib** is split: token
//! consumers implement [`SmtConsume`] and [`SmtConsumeFrom`] over a token cursor
//! type that implements [`SmtCursor`], and token producers call
//! [`SmtConsumeFrom::consume`], giving it the cursor to consume tokens from.
//!
//! The most important producer in the library is
//! [`SmtLexer`](crate::lexer::SmtLexer), but [`SmtTokensCursor`] or a custom cursor
//! can also be used. [`SmtConsume`] is implemented by
//! [`SmtParseAdapter`](crate::parser::SmtParseAdapter) and
//! [`SmtWriter`](crate::SmtWriter).
//!
//! [`SmtToken`] itself is an enumeration over lexical categories with a view into
//! their content, with the end of file marker (EOF) represented as a token to
//! simplify the API. Whitespace and comments are also [`SmtToken`] categories,
//! and a [`SmtConsume`] implementation can choose whether those should be passed
//! through via [`SmtConsume::IS_CONCRETE`]. This can be used e.g. for
//! pretty-printing while preserving comments.
//!
//! ```rust
//! # use blazing_smtlib::{SmtVersion, SmtWriterConfig, SmtWriteStyle, SmtWriter, lexer::SmtLexer};
//! let input = b"   ; comment\r  (check-sat    )";
//! // rewrite in a compact style to get rid of excess whitespace and normalise line endings
//! let mut output = Vec::new();
//! let config = SmtWriterConfig::new(SmtVersion::V2_7).with_style(SmtWriteStyle::Compact);
//! let writer = SmtWriter::new(&mut output, config);
//! let mut lexer = SmtLexer::new(writer, SmtVersion::V2_7);
//! lexer.lex_all(input);
//! assert_eq!(output, b"; comment\n(check-sat)\n")
//! ```
//!
//! The cursor methods do not return [`SmtToken`] directly, but values of type
//! [`SmtCursor::Token`], so that consumers implementing [`SmtConsumeFrom`] for a
//! specific cursor type can use its additional token information, e.g.
//! [span](crate::span) of [`SmtLexerToken`]. The tokens can be converted to
//! syntax tokens using [`SmtCursor::syntax`]. For sanity, the cursor must make
//! sure that the tokens produced are valid under its version in force announced
//! by [`SmtCursor::version`], e.g. unquoted `lambda` must be produced as
//! [`SmtToken::Symbol`] in SMT-LIB 2.6, but [`SmtToken::Reserved`] in SMT-LIB 2.7.
//! See [`SmtCursor`] for further information.
//!

use std::{collections::VecDeque, error::Error, fmt, io::Write, ops::ControlFlow};

use crate::{
    SmtVersion, SmtWriteError, SmtWriteErrorKind,
    lexer::SmtLexerToken,
    lexicon::{
        SmtBinDigits, SmtBinDigitsBuf, SmtComment, SmtCommentBuf, SmtDecimal, SmtDecimalBuf,
        SmtHexDigits, SmtHexDigitsBuf, SmtKeyword, SmtKeywordBuf, SmtNumeral, SmtNumeralBuf,
        SmtReserved, SmtStringContent, SmtStringContentBuf, SmtSymbol, SmtSymbolBuf, SmtWhitespace,
        SmtWhitespaceBuf,
    },
};

/// Category of a token.
///
/// The category does not differentiate between versions:
/// both simple tokens and reserved words are categorised
/// as an unquoted symbol.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

/// View of a syntax token.
#[derive(Debug, Clone, Copy)]
pub enum SmtToken<'a> {
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

impl<'a> SmtToken<'a> {
    /// Constructs the syntax token from the lexer token in the version.
    #[inline]
    pub fn from_lexer_token(token: SmtLexerToken<'a>, version: SmtVersion) -> Self {
        let content = token.content();
        match token.category() {
            SmtTokenCategory::ParenOpen => SmtToken::ParenOpen,
            SmtTokenCategory::ParenClose => SmtToken::ParenClose,
            SmtTokenCategory::Numeral => SmtToken::Numeral(SmtNumeral::new_unchecked(content)),
            SmtTokenCategory::Decimal => SmtToken::Decimal(SmtDecimal::new_unchecked(content)),
            SmtTokenCategory::Hexadecimal => {
                SmtToken::Hexadecimal(SmtHexDigits::new_unchecked(content))
            }
            SmtTokenCategory::Binary => SmtToken::Binary(SmtBinDigits::new_unchecked(content)),
            SmtTokenCategory::UnquotedSymbol => {
                // only the words reserved in the version are reserved words
                if let Some(reserved) = SmtReserved::from_bytes(content, version) {
                    SmtToken::Reserved(reserved)
                } else {
                    SmtToken::Symbol(SmtSymbol::new_unchecked(false, content))
                }
            }
            SmtTokenCategory::QuotedSymbol => {
                SmtToken::Symbol(SmtSymbol::new_unchecked(true, content))
            }
            SmtTokenCategory::String => SmtToken::String(SmtStringContent::new_unchecked(content)),
            SmtTokenCategory::Keyword => SmtToken::Keyword(SmtKeyword::new_unchecked(content)),
            SmtTokenCategory::Whitespace => {
                SmtToken::Whitespace(SmtWhitespace::new_unchecked(content))
            }
            SmtTokenCategory::Comment => SmtToken::Comment(SmtComment::new_unchecked(content)),
            SmtTokenCategory::EndOfFile => SmtToken::EndOfFile,
        }
    }

    /// Writes the token as SMT-LIB text in the given version.
    ///
    /// No delimiter is written, only the SMT-LIB token as
    /// it should appear in a byte stream.
    /// 2.0 string literals have backslashes always written escaped
    /// for sanity even if a single backslash would have been acceptable.
    ///
    /// If a simple symbol collides with a reserved word in the given
    /// version, it is written as a quoted symbol, so version upgrades
    /// are possible without problems.
    ///
    /// Returns an error if the reserved word is not present
    /// in the given version or if the underlying writer returns one.
    pub fn write_smt<W: Write + ?Sized>(
        &self,
        writer: &mut W,
        version: SmtVersion,
    ) -> Result<(), SmtWriteError> {
        match self {
            SmtToken::ParenOpen => writer.write_all(b"(")?,
            SmtToken::ParenClose => writer.write_all(b")")?,
            SmtToken::Numeral(numeral) => writer.write_all(numeral.as_slice())?,
            SmtToken::Decimal(decimal) => writer.write_all(decimal.as_slice())?,
            SmtToken::Hexadecimal(digits) => {
                writer.write_all(b"#x")?;
                writer.write_all(digits.as_slice())?;
            }
            SmtToken::Binary(digits) => {
                writer.write_all(b"#b")?;
                writer.write_all(digits.as_slice())?;
            }
            SmtToken::String(content) => {
                writer.write_all(b"\"")?;
                if version == SmtVersion::V2_0 {
                    // SMT-LIB 2.0: a double quote and a backslash are escaped by a backslash
                    for chunk in content
                        .as_slice()
                        .split_inclusive(|c| *c == b'"' || *c == b'\\')
                    {
                        let (last, rest) = chunk.split_last().expect("split chunks are not empty");
                        writer.write_all(rest)?;
                        // escape quotes and backslashes
                        // for sanity, always escape backslashes, even if not strictly needed
                        // e.g. in \q, the backslash does not technically need to be escaped
                        if *last == b'"' || *last == b'\\' {
                            writer.write_all(b"\\")?;
                        }
                        writer.write_all(&[*last])?;
                    }
                } else {
                    // SMT-LIB 2.5+: a double quote is escaped by another double quote
                    for chunk in content.as_slice().split_inclusive(|c| *c == b'"') {
                        writer.write_all(chunk)?;
                        if chunk.last() == Some(&b'"') {
                            writer.write_all(b"\"")?;
                        }
                    }
                }
                writer.write_all(b"\"")?;
            }
            SmtToken::Keyword(keyword) => {
                writer.write_all(b":")?;
                writer.write_all(keyword.as_slice())?;
            }
            SmtToken::Symbol(symbol) => {
                // a simple symbol that is a reserved word in the version
                // would be read as the reserved word, quote it to keep the symbol
                if symbol.is_quoted()
                    || SmtReserved::from_bytes(symbol.as_slice(), version).is_some()
                {
                    writer.write_all(b"|")?;
                    writer.write_all(symbol.as_slice())?;
                    writer.write_all(b"|")?;
                } else {
                    writer.write_all(symbol.as_slice())?;
                }
            }
            SmtToken::Reserved(reserved) => {
                if !reserved.is_in_version(version) {
                    // the reserved word is not in the version
                    // there is no way to write it
                    return Err(SmtWriteError::new(SmtWriteErrorKind::NotInVersion(
                        *reserved,
                    )));
                }
                writer.write_all(reserved.as_str().as_bytes())?;
            }
            SmtToken::Whitespace(whitespace) => writer.write_all(whitespace.as_slice())?,
            SmtToken::Comment(comment) => {
                writer.write_all(b";")?;
                writer.write_all(comment.as_slice())?;
            }
            SmtToken::EndOfFile => {}
        }
        Ok(())
    }
}

/// Owned syntax token.
#[derive(Debug, Clone)]
pub enum SmtTokenBuf {
    ParenOpen,
    ParenClose,
    Numeral(SmtNumeralBuf),
    Decimal(SmtDecimalBuf),
    Hexadecimal(SmtHexDigitsBuf),
    Binary(SmtBinDigitsBuf),
    String(SmtStringContentBuf),
    Keyword(SmtKeywordBuf),
    Symbol(SmtSymbolBuf),
    Reserved(SmtReserved),
    Whitespace(SmtWhitespaceBuf),
    Comment(SmtCommentBuf),
    EndOfFile,
}

impl SmtTokenBuf {
    pub fn view(&self) -> SmtToken<'_> {
        match self {
            Self::ParenOpen => SmtToken::ParenOpen,
            Self::ParenClose => SmtToken::ParenClose,
            Self::Numeral(value) => SmtToken::Numeral(value.view()),
            Self::Decimal(value) => SmtToken::Decimal(value.view()),
            Self::Hexadecimal(value) => SmtToken::Hexadecimal(value.view()),
            Self::Binary(value) => SmtToken::Binary(value.view()),
            Self::String(value) => SmtToken::String(value.view()),
            Self::Keyword(value) => SmtToken::Keyword(value.view()),
            Self::Symbol(value) => SmtToken::Symbol(value.view()),
            Self::Reserved(reserved) => SmtToken::Reserved(*reserved),
            Self::Whitespace(value) => SmtToken::Whitespace(value.view()),
            Self::Comment(value) => SmtToken::Comment(value.view()),
            Self::EndOfFile => SmtToken::EndOfFile,
        }
    }
}

impl SmtToken<'_> {
    pub fn into_owned(self) -> SmtTokenBuf {
        match self {
            Self::ParenOpen => SmtTokenBuf::ParenOpen,
            Self::ParenClose => SmtTokenBuf::ParenClose,
            Self::Numeral(value) => SmtTokenBuf::Numeral(value.into_owned()),
            Self::Decimal(value) => SmtTokenBuf::Decimal(value.into_owned()),
            Self::Hexadecimal(value) => SmtTokenBuf::Hexadecimal(value.into_owned()),
            Self::Binary(value) => SmtTokenBuf::Binary(value.into_owned()),
            Self::String(value) => SmtTokenBuf::String(value.into_owned()),
            Self::Keyword(value) => SmtTokenBuf::Keyword(value.into_owned()),
            Self::Symbol(value) => SmtTokenBuf::Symbol(value.into_owned()),
            Self::Reserved(reserved) => SmtTokenBuf::Reserved(reserved),
            Self::Whitespace(value) => SmtTokenBuf::Whitespace(value.into_owned()),
            Self::Comment(value) => SmtTokenBuf::Comment(value.into_owned()),
            Self::EndOfFile => SmtTokenBuf::EndOfFile,
        }
    }
}

/// What a token in [`SmtTokensBuf`] is, its bytes aside.
#[derive(Debug, Clone, Copy)]
enum TokenKind {
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
    Reserved(SmtReserved),
    Whitespace,
    Comment,
    EndOfFile,
}

/// A token in [`SmtTokensBuf`]: its kind and where its bytes are in the text.
#[derive(Debug, Clone, Copy)]
struct TokenHandle {
    kind: TokenKind,
    start: usize,
    end: usize,
}

impl TokenHandle {
    /// Pushes the bytes of the token into `text`.
    fn create_by_push(text: &mut Vec<u8>, token: SmtToken) -> TokenHandle {
        let (kind, bytes): (TokenKind, &[u8]) = match token {
            SmtToken::ParenOpen => (TokenKind::ParenOpen, &[]),
            SmtToken::ParenClose => (TokenKind::ParenClose, &[]),
            SmtToken::Numeral(value) => (TokenKind::Numeral, value.as_slice()),
            SmtToken::Decimal(value) => (TokenKind::Decimal, value.as_slice()),
            SmtToken::Hexadecimal(value) => (TokenKind::Hexadecimal, value.as_slice()),
            SmtToken::Binary(value) => (TokenKind::Binary, value.as_slice()),
            SmtToken::String(value) => (TokenKind::String, value.as_slice()),
            SmtToken::Keyword(value) => (TokenKind::Keyword, value.as_slice()),
            SmtToken::Symbol(value) if value.is_quoted() => {
                (TokenKind::QuotedSymbol, value.as_slice())
            }
            SmtToken::Symbol(value) => (TokenKind::UnquotedSymbol, value.as_slice()),
            SmtToken::Reserved(reserved) => (TokenKind::Reserved(reserved), &[]),
            SmtToken::Whitespace(value) => (TokenKind::Whitespace, value.as_slice()),
            SmtToken::Comment(value) => (TokenKind::Comment, value.as_slice()),
            SmtToken::EndOfFile => (TokenKind::EndOfFile, &[]),
        };
        let start = text.len();
        text.extend_from_slice(bytes);
        TokenHandle {
            kind,
            start,
            end: text.len(),
        }
    }

    /// Views the token.
    #[inline]
    fn view(self, text: &[u8]) -> SmtToken<'_> {
        // the bytes were pushed from a view of the same kind, so they are allowed
        let bytes = &text[self.start..self.end];
        match self.kind {
            TokenKind::ParenOpen => SmtToken::ParenOpen,
            TokenKind::ParenClose => SmtToken::ParenClose,
            TokenKind::Numeral => SmtToken::Numeral(SmtNumeral::new_unchecked(bytes)),
            TokenKind::Decimal => SmtToken::Decimal(SmtDecimal::new_unchecked(bytes)),
            TokenKind::Hexadecimal => SmtToken::Hexadecimal(SmtHexDigits::new_unchecked(bytes)),
            TokenKind::Binary => SmtToken::Binary(SmtBinDigits::new_unchecked(bytes)),
            TokenKind::String => SmtToken::String(SmtStringContent::new_unchecked(bytes)),
            TokenKind::Keyword => SmtToken::Keyword(SmtKeyword::new_unchecked(bytes)),
            TokenKind::UnquotedSymbol => SmtToken::Symbol(SmtSymbol::new_unchecked(false, bytes)),
            TokenKind::QuotedSymbol => SmtToken::Symbol(SmtSymbol::new_unchecked(true, bytes)),
            TokenKind::Reserved(reserved) => SmtToken::Reserved(reserved),
            TokenKind::Whitespace => SmtToken::Whitespace(SmtWhitespace::new_unchecked(bytes)),
            TokenKind::Comment => SmtToken::Comment(SmtComment::new_unchecked(bytes)),
            TokenKind::EndOfFile => SmtToken::EndOfFile,
        }
    }
}

/// Dynamic array of owned tokens.
#[derive(Clone)]
pub struct SmtTokensBuf {
    text: Vec<u8>,
    handles: Vec<TokenHandle>,
}

impl SmtTokensBuf {
    pub fn new() -> Self {
        Self {
            text: Vec::new(),
            handles: Vec::new(),
        }
    }

    /// Copies the token after the others.
    pub fn push(&mut self, token: SmtToken) {
        let token = TokenHandle::create_by_push(&mut self.text, token);
        self.handles.push(token);
    }

    pub fn clear(&mut self) {
        self.text.clear();
        self.handles.clear();
    }

    pub fn len(&self) -> usize {
        self.handles.len()
    }

    pub fn is_empty(&self) -> bool {
        self.handles.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<SmtToken<'_>> {
        Some(self.handles.get(index)?.view(&self.text))
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = SmtToken<'_>> {
        let text = self.text.as_slice();
        self.handles.iter().map(move |handle| handle.view(text))
    }
}

impl Default for SmtTokensBuf {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for SmtTokensBuf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Cursor refused to switch to a requested version.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SmtVersionRefused;

impl fmt::Display for SmtVersionRefused {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("version switch refused")
    }
}

impl Error for SmtVersionRefused {}

/// Sequential producer of tokens.
///
/// The cursor can choose the type of tokens to produce, which allows a
/// non-generic consumer to access more information from the token. However, the
/// tokens must implement [`Copy`], be viewable as syntax tokens using
/// [`SmtCursor::syntax`], and should be implemented as small views for good
/// performance.
///
/// To allow version-switching and discarding after `(exit)` in SMT-LIB scripts,
/// the version currently in force must be provided by the cursor using
/// [`SmtCursor::version`], and the cursor can be requested to switch to another
/// version by [`SmtCursor::set_version`] or forced to start discarding tokens
/// until EOF by [`SmtCursor::discard_rest`].
pub trait SmtCursor {
    /// User type of the token.
    ///
    /// The producer must implement [`SmtCursor::syntax`] to view
    /// the user token type as a library type.
    type Token: Copy;

    /// Lookahead window, set to `()` if not implementing [`SmtCursor::attempt`].
    type Lookahead: SmtLookahead<Self::Token>;

    /// Views the user token as a syntax token under the version in force.
    fn syntax<'t>(&self, token: &'t Self::Token) -> SmtToken<'t>;

    /// Consumes the next token (if any).
    fn next(&mut self) -> Option<Self::Token>;

    /// Returns the next token (if any) without consuming it.
    ///
    /// Peeking must return [`Option::Some`] containing the next token that
    /// would be consumed if there is some such token waiting.
    ///
    /// The caller must not forget to consume the token later if it should be
    /// taken.
    fn peek(&self) -> Option<Self::Token>;

    /// Returns whether the producer has no tokens left to consume.
    ///
    /// This must be true exactly if [`SmtCursor::peek`] or
    /// [`SmtCursor::next`] would produce [`Option::None`].
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
    /// Use standard [`SmtCursor::next`] processing unless
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

    /// SMT-LIB version that applies to the tokens currently consumed.
    ///
    /// The version is guaranteed not to change during a call
    /// to the consumer except as a result of the consumer calling
    /// [`SmtCursor::set_version`] and the producer accepting.
    fn version(&self) -> SmtVersion;

    /// Sets the version that applies from now on.
    ///
    /// If the producer returns [`Result::Ok`], it has switched
    /// to the new version, and will return it in subsequent
    /// calls of [`SmtCursor::version`]. The version change
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

/// Lookahead window for [`SmtCursor::attempt`].
pub trait SmtLookahead<T> {
    /// Looks at the next token and advances the window.
    fn next(&mut self) -> Option<T>;

    /// Views the user token as a syntax token.
    fn syntax<'t>(&self, token: &'t T) -> SmtToken<'t>;
}

impl<T> SmtLookahead<T> for () {
    fn next(&mut self) -> Option<T> {
        None
    }

    /// Views the user token as a syntax token.
    fn syntax<'t>(&self, _token: &'t T) -> SmtToken<'t> {
        panic!("unit lookahead cannot view user token as it produces no tokens")
    }
}

pub(crate) struct SingleTokenCursor<'a, Z: SmtCursor> {
    cursor: &'a Z,
    token: Option<Z::Token>,
}

impl<'a, Z: SmtCursor> SingleTokenCursor<'a, Z> {
    pub(crate) fn new(cursor: &'a Z, token: Z::Token) -> Self {
        Self {
            cursor,
            token: Some(token),
        }
    }
}

impl<'a, Z: SmtCursor> SmtCursor for SingleTokenCursor<'a, Z> {
    type Token = Z::Token;
    type Lookahead = ();

    fn syntax<'t>(&self, token: &'t Self::Token) -> SmtToken<'t> {
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
        // single-token cursor does not support switching versions
        Err(SmtVersionRefused)
    }

    fn discard_rest(&mut self) {
        panic!("single-token cursor cannot discard the rest of the input")
    }
}

/// Cursor over a dynamic array of syntax tokens.
///
/// The cursor is consumed under a given version: it accepts a request
/// for that version and refuses a switch to any other. If the consumer
/// requests discarding, currently present tokens are discarded up to
/// before the first EOF.
/// If no EOF is currently present, the cursor switches to a discarding mode
/// and no new tokens are pushed until a pushed EOF token resets
/// the discarding mode. EOF tokens are never discarded themselves.
#[derive(Debug, Clone)]
pub struct SmtTokensCursor<'a> {
    tokens: VecDeque<SmtToken<'a>>,
    /// Whether the tokens are discarded until an end-of-file token is pushed.
    discarding: bool,
    version: SmtVersion,
}

impl<'a> SmtTokensCursor<'a> {
    /// Constructs an empty cursor.
    pub fn new(version: SmtVersion) -> Self {
        Self {
            tokens: VecDeque::new(),
            discarding: false,
            version,
        }
    }

    /// Pushes a new token to the end of the cursor.
    ///
    /// If the cursor is currently discarding, any token
    /// other than EOF is silently dropped, so the cursor
    /// remains empty.
    #[inline]
    pub fn push(&mut self, token: SmtToken<'a>) {
        if self.discarding {
            if matches!(token, SmtToken::EndOfFile) {
                // the end-of-file token ends discarding
                // and it is not discarded
                self.discarding = false;
            } else {
                // discard the token
                return;
            }
        }
        self.tokens.push_back(token);
    }

    /// Removes all tokens and resets discarding mode.
    pub fn clear(&mut self) {
        self.tokens.clear();
        self.discarding = false;
    }
}

impl<'a> SmtCursor for SmtTokensCursor<'a> {
    type Token = SmtToken<'a>;
    type Lookahead = ();

    #[inline]
    fn syntax<'t>(&self, token: &'t SmtToken<'a>) -> SmtToken<'t> {
        *token
    }

    #[allow(clippy::should_implement_trait)]
    #[inline]
    fn next(&mut self) -> Option<SmtToken<'a>> {
        self.tokens.pop_front()
    }

    #[inline]
    fn peek(&self) -> Option<SmtToken<'a>> {
        self.tokens.front().copied()
    }

    #[inline]
    fn is_empty(&self) -> bool {
        self.tokens.is_empty()
    }

    #[inline]
    fn consume_all(&mut self) {
        self.tokens.clear();
    }

    fn version(&self) -> SmtVersion {
        self.version
    }

    fn set_version(&mut self, version: SmtVersion) -> Result<(), SmtVersionRefused> {
        // the tokens were put in already classified under the cursor's
        // version, so they cannot be read under any other
        if version == self.version {
            Ok(())
        } else {
            Err(SmtVersionRefused)
        }
    }

    fn discard_rest(&mut self) {
        // drop the tokens before the next end-of-file token, which stays there
        while let Some(token) = self.tokens.front() {
            if matches!(token, SmtToken::EndOfFile) {
                // stop discarding, keep EOF
                return;
            }
            self.tokens.pop_front();
        }
        // no EOF encountered, switch to discarding mode
        self.discarding = true;
    }
}

/// Appends tokens representing the value to a cursor.
pub trait SmtAppendTokens {
    /// Puts the tokens of the value after those in the cursor.
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>);
}

impl SmtAppendTokens for SmtToken<'_> {
    #[inline]
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        tokens.push(*self);
    }
}

impl SmtAppendTokens for SmtTokenBuf {
    #[inline]
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        tokens.push(self.view());
    }
}

impl SmtAppendTokens for SmtTokensBuf {
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        for token in self.iter() {
            tokens.push(token);
        }
    }
}

impl<T: SmtAppendTokens> SmtAppendTokens for [T] {
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        for value in self {
            value.append_tokens(tokens);
        }
    }
}

impl<T: SmtAppendTokens, const N: usize> SmtAppendTokens for [T; N] {
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        self.as_slice().append_tokens(tokens);
    }
}

impl<T: SmtAppendTokens> SmtAppendTokens for Vec<T> {
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        self.as_slice().append_tokens(tokens);
    }
}

impl SmtAppendTokens for SmtReserved {
    #[inline]
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        tokens.push(SmtToken::Reserved(*self));
    }
}

/// Defines the appending of a plain value, viewed or owned, as the token of
/// its variant.
macro_rules! plain_append_tokens {
    ($view:ident, $buf:ident, $variant:ident) => {
        impl SmtAppendTokens for $view<'_> {
            #[inline]
            fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
                tokens.push(SmtToken::$variant(*self));
            }
        }

        impl SmtAppendTokens for $buf {
            #[inline]
            fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
                tokens.push(SmtToken::$variant(self.view()));
            }
        }
    };
}

plain_append_tokens!(SmtNumeral, SmtNumeralBuf, Numeral);
plain_append_tokens!(SmtDecimal, SmtDecimalBuf, Decimal);
plain_append_tokens!(SmtHexDigits, SmtHexDigitsBuf, Hexadecimal);
plain_append_tokens!(SmtBinDigits, SmtBinDigitsBuf, Binary);
plain_append_tokens!(SmtStringContent, SmtStringContentBuf, String);
plain_append_tokens!(SmtKeyword, SmtKeywordBuf, Keyword);
plain_append_tokens!(SmtSymbol, SmtSymbolBuf, Symbol);
plain_append_tokens!(SmtWhitespace, SmtWhitespaceBuf, Whitespace);
plain_append_tokens!(SmtComment, SmtCommentBuf, Comment);

/// Consumes tokens sequentially.
///
/// [`SmtConsumeFrom`] defines the actual consumption function from a given
/// cursor.
pub trait SmtConsume {
    /// Result returned by the consumer on success.
    type Result;
    /// Error returned by the consumer on failure.
    type Error;
    /// Whether the consumer consumes whitespace and comments.
    ///
    /// If true, the consumer operates over concrete tokens: it can reconstruct
    /// the byte stream precisely thanks to the whitespace and comments. The
    /// caller must hand over the whitespace and comment tokens present between
    /// true syntactic tokens (unless the consumer specifically allows them to
    /// be omitted, as e.g. [`SmtWriter`](crate::SmtWriter) does).
    ///
    /// If false, the consumer operates over abstract tokens: it is not
    /// interested in whitespace and comments, and the caller must not hand them
    /// over for consumption.
    const IS_CONCRETE: bool;
}

/// Consumes tokens sequentially from the given cursor.
///
/// This is a subtrait of [`SmtConsume`], which defines the cursor result and
/// error types and whether the consumer is concrete. If the consumer does not
/// use cursor-specific data such as token locations from
/// [`SmtLexerCursor`](crate::lexer::SmtLexerCursor), [`SmtConsumeFrom`] can be
/// implemented generically over all cursors.
pub trait SmtConsumeFrom<Z: SmtCursor>: SmtConsume {
    /// Consumes the tokens handed over in the cursor, in order.
    ///
    /// The caller must ensure that the cursor contains at least one token. The
    /// consumer must ensure that at least one token is consumed before return,
    /// no matter the result (even when returning an error).
    ///
    /// If the consumer returns [`ControlFlow::Continue`], the consumer is not
    /// finished yet and is ready to consume more tokens. Tokens that remain
    /// unconsumed in the cursor must be handed over again before any new ones.
    /// The consumer must not return [`ControlFlow::Continue`] when an EOF token
    /// is encountered.
    ///
    /// If the consumer returns [`ControlFlow::Break`], it has finished consuming
    /// the current value, is returning a result, and is ready to start
    /// consuming a new value.
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
impl<Z: SmtCursor, T: SmtConsumeFrom<Z> + ?Sized> SmtConsumeFrom<Z> for &mut T {
    #[inline]
    fn consume(&mut self, cursor: &mut Z) -> Result<ControlFlow<Self::Result>, Self::Error> {
        (**self).consume(cursor)
    }
}

impl SmtTokensCursor<'_> {
    /// Empties the cursor for tokens of another lifetime and the given version,
    /// keeping its allocation.
    pub(crate) fn recycle<'b>(self, version: SmtVersion) -> SmtTokensCursor<'b> {
        let mut tokens = self.tokens;
        tokens.clear();
        // an empty deque becomes a vector without moving or reallocating, and an
        // empty vector mapped and collected keeps its allocation in the new type
        let tokens: Vec<SmtToken<'b>> = Vec::from(tokens)
            .into_iter()
            .map(|_| SmtToken::EndOfFile)
            .collect();
        SmtTokensCursor {
            tokens: VecDeque::from(tokens),
            discarding: false,
            version,
        }
    }
}

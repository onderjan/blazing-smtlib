use std::{
    collections::VecDeque,
    error::Error,
    fmt,
    io::{self, Write},
    ops::ControlFlow,
};

use crate::{
    SmtBinDigits, SmtBinDigitsBuf, SmtComment, SmtCommentBuf, SmtDecimal, SmtDecimalBuf,
    SmtHexDigits, SmtHexDigitsBuf, SmtKeyword, SmtKeywordBuf, SmtLocation, SmtNumeral,
    SmtNumeralBuf, SmtSpan, SmtStringContent, SmtStringContentBuf, SmtSymbol, SmtSymbolBuf,
    SmtWhitespace, SmtWhitespaceBuf,
};

mod reserved;

pub use reserved::{SmtCommandNameReserved, SmtGeneralReserved, SmtReserved};

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

#[derive(Debug, Clone, Copy)]
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord)]
pub enum SmtVersion {
    V2_0,
    V2_5,
    V2_6,
    #[default]
    V2_7,
}

impl SmtVersion {
    /// The version that the decimal names, if any.
    pub fn from_decimal(decimal: &[u8]) -> Option<Self> {
        match decimal {
            b"2.0" => Some(SmtVersion::V2_0),
            b"2.5" => Some(SmtVersion::V2_5),
            b"2.6" => Some(SmtVersion::V2_6),
            b"2.7" => Some(SmtVersion::V2_7),
            _ => None,
        }
    }

    /// The decimal that names the version, as in `:smt-lib-version`.
    pub fn as_decimal(&self) -> SmtDecimal<'static> {
        let decimal: &'static [u8] = match self {
            SmtVersion::V2_0 => b"2.0",
            SmtVersion::V2_5 => b"2.5",
            SmtVersion::V2_6 => b"2.6",
            SmtVersion::V2_7 => b"2.7",
        };
        SmtDecimal::new_unchecked(decimal)
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
                if let Some(reserved) = SmtReserved::from_bytes(content, version) {
                    SmtSyntaxToken::Reserved(reserved)
                } else {
                    SmtSyntaxToken::Symbol(SmtSymbol::new_unchecked(false, content))
                }
            }
            SmtTokenCategory::QuotedSymbol => {
                SmtSyntaxToken::Symbol(SmtSymbol::new_unchecked(true, content))
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
            SmtSyntaxToken::ParenOpen => writer.write_all(b"(")?,
            SmtSyntaxToken::ParenClose => writer.write_all(b")")?,
            SmtSyntaxToken::Numeral(numeral) => writer.write_all(numeral.as_slice())?,
            SmtSyntaxToken::Decimal(decimal) => writer.write_all(decimal.as_slice())?,
            SmtSyntaxToken::Hexadecimal(digits) => {
                writer.write_all(b"#x")?;
                writer.write_all(digits.as_slice())?;
            }
            SmtSyntaxToken::Binary(digits) => {
                writer.write_all(b"#b")?;
                writer.write_all(digits.as_slice())?;
            }
            SmtSyntaxToken::String(content) => {
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
            SmtSyntaxToken::Keyword(keyword) => {
                writer.write_all(b":")?;
                writer.write_all(keyword.as_slice())?;
            }
            SmtSyntaxToken::Symbol(symbol) => {
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
            SmtSyntaxToken::Reserved(reserved) => {
                if !reserved.is_in_version(version) {
                    // the reserved word is not in the version
                    // there is no way to write it
                    return Err(SmtWriteError(SmtWriteErrorCause::NotInVersion(*reserved)));
                }
                writer.write_all(reserved.as_str().as_bytes())?;
            }
            SmtSyntaxToken::Whitespace(whitespace) => writer.write_all(whitespace.as_slice())?,
            SmtSyntaxToken::Comment(comment) => {
                writer.write_all(b";")?;
                writer.write_all(comment.as_slice())?;
            }
            SmtSyntaxToken::EndOfFile => {}
        }
        Ok(())
    }
}

/// An owned token, from which [`SmtSyntaxToken`] is viewed.
#[derive(Debug, Clone)]
pub enum SmtSyntaxTokenBuf {
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

impl SmtSyntaxTokenBuf {
    pub fn view(&self) -> SmtSyntaxToken<'_> {
        match self {
            Self::ParenOpen => SmtSyntaxToken::ParenOpen,
            Self::ParenClose => SmtSyntaxToken::ParenClose,
            Self::Numeral(value) => SmtSyntaxToken::Numeral(value.view()),
            Self::Decimal(value) => SmtSyntaxToken::Decimal(value.view()),
            Self::Hexadecimal(value) => SmtSyntaxToken::Hexadecimal(value.view()),
            Self::Binary(value) => SmtSyntaxToken::Binary(value.view()),
            Self::String(value) => SmtSyntaxToken::String(value.view()),
            Self::Keyword(value) => SmtSyntaxToken::Keyword(value.view()),
            Self::Symbol(value) => SmtSyntaxToken::Symbol(value.view()),
            Self::Reserved(reserved) => SmtSyntaxToken::Reserved(*reserved),
            Self::Whitespace(value) => SmtSyntaxToken::Whitespace(value.view()),
            Self::Comment(value) => SmtSyntaxToken::Comment(value.view()),
            Self::EndOfFile => SmtSyntaxToken::EndOfFile,
        }
    }
}

impl SmtSyntaxToken<'_> {
    pub fn into_owned(self) -> SmtSyntaxTokenBuf {
        match self {
            Self::ParenOpen => SmtSyntaxTokenBuf::ParenOpen,
            Self::ParenClose => SmtSyntaxTokenBuf::ParenClose,
            Self::Numeral(value) => SmtSyntaxTokenBuf::Numeral(value.into_owned()),
            Self::Decimal(value) => SmtSyntaxTokenBuf::Decimal(value.into_owned()),
            Self::Hexadecimal(value) => SmtSyntaxTokenBuf::Hexadecimal(value.into_owned()),
            Self::Binary(value) => SmtSyntaxTokenBuf::Binary(value.into_owned()),
            Self::String(value) => SmtSyntaxTokenBuf::String(value.into_owned()),
            Self::Keyword(value) => SmtSyntaxTokenBuf::Keyword(value.into_owned()),
            Self::Symbol(value) => SmtSyntaxTokenBuf::Symbol(value.into_owned()),
            Self::Reserved(reserved) => SmtSyntaxTokenBuf::Reserved(reserved),
            Self::Whitespace(value) => SmtSyntaxTokenBuf::Whitespace(value.into_owned()),
            Self::Comment(value) => SmtSyntaxTokenBuf::Comment(value.into_owned()),
            Self::EndOfFile => SmtSyntaxTokenBuf::EndOfFile,
        }
    }
}

/// What a token of [`SmtTokensBuf`] is, its bytes aside.
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

/// A token of [`SmtTokensBuf`]: its kind and where its bytes are in the text.
#[derive(Debug, Clone, Copy)]
struct TokenHandle {
    kind: TokenKind,
    start: usize,
    end: usize,
}

impl TokenHandle {
    /// Pushes the bytes of the token into `text`.
    fn create_by_push(text: &mut Vec<u8>, token: SmtSyntaxToken) -> TokenHandle {
        let (kind, bytes): (TokenKind, &[u8]) = match token {
            SmtSyntaxToken::ParenOpen => (TokenKind::ParenOpen, &[]),
            SmtSyntaxToken::ParenClose => (TokenKind::ParenClose, &[]),
            SmtSyntaxToken::Numeral(value) => (TokenKind::Numeral, value.as_slice()),
            SmtSyntaxToken::Decimal(value) => (TokenKind::Decimal, value.as_slice()),
            SmtSyntaxToken::Hexadecimal(value) => (TokenKind::Hexadecimal, value.as_slice()),
            SmtSyntaxToken::Binary(value) => (TokenKind::Binary, value.as_slice()),
            SmtSyntaxToken::String(value) => (TokenKind::String, value.as_slice()),
            SmtSyntaxToken::Keyword(value) => (TokenKind::Keyword, value.as_slice()),
            SmtSyntaxToken::Symbol(value) if value.is_quoted() => {
                (TokenKind::QuotedSymbol, value.as_slice())
            }
            SmtSyntaxToken::Symbol(value) => (TokenKind::UnquotedSymbol, value.as_slice()),
            SmtSyntaxToken::Reserved(reserved) => (TokenKind::Reserved(reserved), &[]),
            SmtSyntaxToken::Whitespace(value) => (TokenKind::Whitespace, value.as_slice()),
            SmtSyntaxToken::Comment(value) => (TokenKind::Comment, value.as_slice()),
            SmtSyntaxToken::EndOfFile => (TokenKind::EndOfFile, &[]),
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
    fn view(self, text: &[u8]) -> SmtSyntaxToken<'_> {
        // the bytes were pushed from a view of the same kind, so they are allowed
        let bytes = &text[self.start..self.end];
        match self.kind {
            TokenKind::ParenOpen => SmtSyntaxToken::ParenOpen,
            TokenKind::ParenClose => SmtSyntaxToken::ParenClose,
            TokenKind::Numeral => SmtSyntaxToken::Numeral(SmtNumeral::new_unchecked(bytes)),
            TokenKind::Decimal => SmtSyntaxToken::Decimal(SmtDecimal::new_unchecked(bytes)),
            TokenKind::Hexadecimal => {
                SmtSyntaxToken::Hexadecimal(SmtHexDigits::new_unchecked(bytes))
            }
            TokenKind::Binary => SmtSyntaxToken::Binary(SmtBinDigits::new_unchecked(bytes)),
            TokenKind::String => SmtSyntaxToken::String(SmtStringContent::new_unchecked(bytes)),
            TokenKind::Keyword => SmtSyntaxToken::Keyword(SmtKeyword::new_unchecked(bytes)),
            TokenKind::UnquotedSymbol => {
                SmtSyntaxToken::Symbol(SmtSymbol::new_unchecked(false, bytes))
            }
            TokenKind::QuotedSymbol => {
                SmtSyntaxToken::Symbol(SmtSymbol::new_unchecked(true, bytes))
            }
            TokenKind::Reserved(reserved) => SmtSyntaxToken::Reserved(reserved),
            TokenKind::Whitespace => {
                SmtSyntaxToken::Whitespace(SmtWhitespace::new_unchecked(bytes))
            }
            TokenKind::Comment => SmtSyntaxToken::Comment(SmtComment::new_unchecked(bytes)),
            TokenKind::EndOfFile => SmtSyntaxToken::EndOfFile,
        }
    }
}

/// A dynamic array of owned tokens.
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
    pub fn push(&mut self, token: SmtSyntaxToken) {
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

    pub fn get(&self, index: usize) -> Option<SmtSyntaxToken<'_>> {
        Some(self.handles.get(index)?.view(&self.text))
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = SmtSyntaxToken<'_>> {
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

/// Determines why writing a token has failed.
#[derive(Debug)]
pub enum SmtWriteErrorCause {
    /// Writing to the writer failed.
    Io(io::Error),
    /// The reserved word is not reserved in the version, so no text in it is the token.
    NotInVersion(SmtReserved),
}

/// An error that ended writing a token.
#[derive(Debug)]
pub struct SmtWriteError(SmtWriteErrorCause);

impl SmtWriteError {
    /// Determines why writing has failed.
    pub fn cause(&self) -> &SmtWriteErrorCause {
        &self.0
    }

    /// Convert into the enumeration that determines why writing has failed.
    pub fn into_cause(self) -> SmtWriteErrorCause {
        self.0
    }
}

impl From<io::Error> for SmtWriteError {
    fn from(err: io::Error) -> Self {
        Self(SmtWriteErrorCause::Io(err))
    }
}

impl fmt::Display for SmtWriteErrorCause {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(err) => write!(f, "I/O: {err}"),
            Self::NotInVersion(reserved) => {
                write!(
                    f,
                    "`{}` is not reserved in written version",
                    reserved.as_str()
                )
            }
        }
    }
}

impl fmt::Display for SmtWriteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Error for SmtWriteError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.0 {
            SmtWriteErrorCause::Io(err) => err.source(),
            SmtWriteErrorCause::NotInVersion(_) => None,
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SmtVersionRefused;

impl fmt::Display for SmtVersionRefused {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("version switch refused")
    }
}

impl Error for SmtVersionRefused {}

/// A sequential producer of tokens.
pub trait SmtCursor {
    /// The user type of the token.
    ///
    /// The producer must implement [`SmtCursor::syntax`] to view
    /// the user token type as a library type.
    type Token: Copy;

    /// Lookahead window, set to `()` if not implementing [`SmtCursor::attempt`].
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

    /// The SMT-LIB version that applies for currently consumed tokens.
    ///
    /// The version is guaranteed not to change during a call
    /// to the consumer except as a result of the consumer calling
    /// [`SmtCursor::set_version`] and the producer accepting.
    fn version(&self) -> SmtVersion;

    /// Sets the SMT-LIB version that should apply from now on.
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

/// A lookahead window for [SmtCursor::attempt].
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

impl<'a> SmtCursor for SmtBatchCursor<'a> {
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

pub(crate) struct SingleTokenCursor<'a, Z: SmtCursor> {
    cursor: &'a Z,
    token: Option<Z::Token>,
}

impl<'a, Z: SmtCursor> SingleTokenCursor<'a, Z> {
    pub fn new(cursor: &'a Z, token: Z::Token) -> Self {
        Self {
            cursor,
            token: Some(token),
        }
    }
}

impl<'a, Z: SmtCursor> SmtCursor for SingleTokenCursor<'a, Z> {
    type Token = Z::Token;
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
        // single-token cursor does not support switching versions
        Err(SmtVersionRefused)
    }

    fn discard_rest(&mut self) {
        panic!("single-token cursor cannot discard the rest of the input")
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

/// A cursor over a dynamic array of tokens.
///
/// The cursor is consumed under a given version and refuses
/// version switch requests. If the consumer requests discarding,
/// currently present tokens are discarded up to before the first EOF.
/// If no EOF is currently present, the cursor switches to a discarding mode
/// and no new tokens are pushed until a pushed EOF token resets
/// the discarding mode. EOF tokens are never discarded themselves.
#[derive(Debug, Clone)]
pub struct SmtTokensCursor<'a> {
    tokens: VecDeque<SmtSyntaxToken<'a>>,
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
    pub fn push(&mut self, token: SmtSyntaxToken<'a>) {
        if self.discarding {
            if matches!(token, SmtSyntaxToken::EndOfFile) {
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
    type Token = SmtSyntaxToken<'a>;
    type Lookahead = ();

    #[inline]
    fn syntax<'t>(&self, token: &'t SmtSyntaxToken<'a>) -> SmtSyntaxToken<'t> {
        *token
    }

    #[allow(clippy::should_implement_trait)]
    #[inline]
    fn next(&mut self) -> Option<SmtSyntaxToken<'a>> {
        self.tokens.pop_front()
    }

    #[inline]
    fn peek(&self) -> Option<SmtSyntaxToken<'a>> {
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

    fn set_version(&mut self, _version: SmtVersion) -> Result<(), SmtVersionRefused> {
        // the tokens were put in already classified, so they cannot be read anew
        Err(SmtVersionRefused)
    }

    fn discard_rest(&mut self) {
        // drop the tokens before the next end-of-file token, which stays there
        while let Some(token) = self.tokens.front() {
            if matches!(token, SmtSyntaxToken::EndOfFile) {
                // stop discarding, keep EOF
                return;
            }
            self.tokens.pop_front();
        }
        // no EOF encountered, switch to discarding mode
        self.discarding = true;
    }
}

/// A value whose tokens can be put into a cursor.
pub trait SmtAppendTokens {
    /// Puts the tokens of the value after those in the cursor.
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>);
}

impl SmtAppendTokens for SmtSyntaxToken<'_> {
    #[inline]
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        tokens.push(*self);
    }
}

impl SmtAppendTokens for SmtSyntaxTokenBuf {
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

impl SmtAppendTokens for SmtReserved {
    #[inline]
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        tokens.push(SmtSyntaxToken::Reserved(*self));
    }
}

/// Defines the appending of a plain value, viewed or owned, as the token of
/// its variant.
macro_rules! plain_append_tokens {
    ($view:ident, $buf:ident, $variant:ident) => {
        impl SmtAppendTokens for $view<'_> {
            #[inline]
            fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
                tokens.push(SmtSyntaxToken::$variant(*self));
            }
        }

        impl SmtAppendTokens for $buf {
            #[inline]
            fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
                tokens.push(SmtSyntaxToken::$variant(self.view()));
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
pub trait SmtConsumeFrom<Z: SmtCursor>: SmtConsume {
    /// Consumes the tokens handed over in the cursor, in order.
    ///
    /// The caller must ensure that the cursor contains at least one token.
    /// The consumer must ensure that at least one token is consumed before
    /// return, no matter the result (even when returning an error).
    ///
    /// If the consumer returns [`ControlFlow::Continue`], the consumer is
    /// not finished yet and is ready to consume more tokens. Tokens that
    /// remain unconsumed in the cursor must be handed over again before
    /// any new ones. The consumer must not return [`ControlFlow::Continue`]
    /// when an EOF token is encountered.
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
impl<Z: SmtCursor, T: SmtConsumeFrom<Z> + ?Sized> SmtConsumeFrom<Z> for &mut T {
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

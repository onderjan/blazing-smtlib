use std::{error::Error, fmt, io};

use crate::span::{SmtLocation, SmtSpan};

/// Why the input is lexically malformed.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtLexicalErrorKind {
    UnexpectedByte,
    /// The item was expected here.
    Expected(SmtLexicalExpected),
    UnclosedString,
    ForbiddenByteInString,
    /// A colon is not followed by a keyword name.
    EmptyKeyword,
    BackslashInQuotedSymbol,
    ForbiddenByteInQuotedSymbol,
    UnclosedQuotedSymbol,
    NumeralLeadingZero,
    MissingDelimiter,
    UnexpectedTrailingToken,
}

/// Character class expected by the lexer.
///
/// This is used in [SmtLexicalErrorKind::Expected].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtLexicalExpected {
    /// Digit of the fractional part of a decimal.
    FractionDigit,
    /// Hexadecimal digit after `#x`.
    HexadecimalDigit,
    /// Binary digit after `#b`.
    BinaryDigit,
    /// Base of a number after `#` (`x` or `b`).
    Base,
}

/// Error that forced lexing to stop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtLexerError<E> {
    kind: SmtLexerErrorKind<E>,
    span: SmtSpan,
    continues_from: Option<SmtLocation>,
}

/// Why lexing failed (lexical or consumer error).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtLexerErrorKind<E> {
    /// The input is lexically malformed.
    Lexical(SmtLexicalErrorKind),
    /// The token consumer returned an error.
    Consumer(E),
}

impl<E> SmtLexerError<E> {
    pub(super) fn new(
        kind: SmtLexerErrorKind<E>,
        span: SmtSpan,
        continues_from: Option<SmtLocation>,
    ) -> Self {
        Self {
            kind,
            span,
            continues_from,
        }
    }

    /// Returns an error with the same cause and continuation location set as requested.
    pub(super) fn continuing_from(mut self, location: SmtLocation) -> Self {
        self.continues_from = Some(location);
        self
    }

    /// Kind of the error.
    pub fn kind(&self) -> &SmtLexerErrorKind<E> {
        &self.kind
    }

    /// Converts into the kind of the error.
    pub fn into_kind(self) -> SmtLexerErrorKind<E> {
        self.kind
    }

    /// Span where the error occurred.
    pub fn span(&self) -> SmtSpan {
        self.span
    }

    /// Most useful location for deciphering the error.
    ///
    /// Guaranteed to be within the span.
    pub fn location(&self) -> SmtLocation {
        match &self.kind {
            SmtLexerErrorKind::Lexical(kind) => kind.location_in(self.span),
            SmtLexerErrorKind::Consumer(_) => self.span.start(),
        }
    }

    /// Where the rest of the input is to be fed from if the lexer continues (EXPERIMENTAL).
    ///
    /// If present, the lexer is recovering: it expects the input from this
    /// location on, and the end of the input once none is left.
    /// If absent, the lexer does not continue this input: either it stops
    /// at its first error, or the input has ended.
    ///
    /// Lexer recovery is implemented but experimental
    /// since the exact semantics have not yet been set in stone.
    /// It can change or be removed in any version and should not be used.
    #[doc(hidden)]
    pub fn continues_from(&self) -> Option<SmtLocation> {
        self.continues_from
    }
}

impl SmtLexicalErrorKind {
    /// The most useful location for deciphering the error of this kind given the span.
    ///
    /// The location is within the span.
    pub(crate) fn location_in(self, span: SmtSpan) -> SmtLocation {
        let location = match self {
            // the span ends after the offending byte, which is not a line feed:
            // a line feed is allowed in both literals and delimits a token
            SmtLexicalErrorKind::ForbiddenByteInString
            | SmtLexicalErrorKind::BackslashInQuotedSymbol
            | SmtLexicalErrorKind::ForbiddenByteInQuotedSymbol
            | SmtLexicalErrorKind::MissingDelimiter => {
                let end = span.end();
                SmtLocation::new_unchecked(end.offset() - 1, end.line(), end.column() - 1)
            }
            _ => span.start(),
        };
        debug_assert!(
            location == span.start() || (span.start() < location && location < span.end()),
            "error location {location:?} of {self:?} is not within its span {span:?}"
        );
        location
    }
}

impl fmt::Display for SmtLexicalErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnexpectedByte => f.write_str("unexpected character"),
            Self::Expected(expected) => expected.fmt(f),
            Self::UnclosedString => f.write_str("unclosed string literal"),
            Self::ForbiddenByteInString => f.write_str("forbidden character in string literal"),
            Self::EmptyKeyword => f.write_str("colon without keyword name"),
            Self::BackslashInQuotedSymbol => f.write_str("backslash in quoted symbol"),
            Self::ForbiddenByteInQuotedSymbol => {
                f.write_str("forbidden character in quoted symbol")
            }
            Self::UnclosedQuotedSymbol => f.write_str("unclosed quoted symbol"),
            Self::NumeralLeadingZero => f.write_str("numeral with leading zero"),
            Self::MissingDelimiter => f.write_str("missing delimiter after token"),
            Self::UnexpectedTrailingToken => f.write_str("unexpected trailing token"),
        }
    }
}

impl fmt::Display for SmtLexicalExpected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::FractionDigit => "expected fractional digit",
            Self::HexadecimalDigit => "expected hexadecimal digit",
            Self::BinaryDigit => "expected binary digit",
            Self::Base => "expected base (`x` or `b`) after `#`",
        })
    }
}

impl<E: fmt::Display> fmt::Display for SmtLexerErrorKind<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lexical(kind) => kind.fmt(f),
            Self::Consumer(err) => err.fmt(f),
        }
    }
}

impl<E: fmt::Display> fmt::Display for SmtLexerError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let location = self.location();
        write!(
            f,
            "{} at line {}, column {}",
            self.kind,
            location.line() + 1,
            location.column() + 1
        )
    }
}

impl<E: Error + 'static> Error for SmtLexerError<E> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            SmtLexerErrorKind::Lexical(_) => None,
            SmtLexerErrorKind::Consumer(err) => err.source(),
        }
    }
}

/// Error that forced lexing from a buffered reader or a file to stop.
#[derive(Debug)]
pub struct SmtLexerReadError<E> {
    kind: SmtLexerReadErrorKind<E>,
    span: SmtSpan,
}

/// Why lexing from a buffered reader or a file failed (I/O, lexical, or consumer error).
#[derive(Debug)]
pub enum SmtLexerReadErrorKind<E> {
    /// Reading from the file or the buffered reader failed.
    Io(io::Error),
    /// The input is lexically malformed.
    Lexical(SmtLexicalErrorKind),
    /// The token consumer returned an error.
    Consumer(E),
}

impl<E> SmtLexerReadError<E> {
    pub(super) fn new(kind: SmtLexerReadErrorKind<E>, span: SmtSpan) -> Self {
        Self { kind, span }
    }

    /// Kind of the error.
    pub fn kind(&self) -> &SmtLexerReadErrorKind<E> {
        &self.kind
    }

    /// Converts into the kind of the error.
    pub fn into_kind(self) -> SmtLexerReadErrorKind<E> {
        self.kind
    }

    /// Span where the error occurred.
    ///
    /// For I/O errors, the span is empty, at the position where reading failed.
    pub fn span(&self) -> SmtSpan {
        self.span
    }

    /// Most useful location for deciphering the error.
    ///
    /// Guaranteed to be within the span.
    pub fn location(&self) -> SmtLocation {
        match &self.kind {
            SmtLexerReadErrorKind::Lexical(kind) => kind.location_in(self.span),
            SmtLexerReadErrorKind::Io(_) | SmtLexerReadErrorKind::Consumer(_) => self.span.start(),
        }
    }
}

impl<E> From<SmtLexerError<E>> for SmtLexerReadError<E> {
    fn from(err: SmtLexerError<E>) -> Self {
        let span = err.span();
        let kind = match err.into_kind() {
            SmtLexerErrorKind::Lexical(kind) => SmtLexerReadErrorKind::Lexical(kind),
            SmtLexerErrorKind::Consumer(err) => SmtLexerReadErrorKind::Consumer(err),
        };
        Self::new(kind, span)
    }
}

impl<E: fmt::Display> fmt::Display for SmtLexerReadErrorKind<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(err) => write!(f, "I/O: {err}"),
            Self::Lexical(kind) => kind.fmt(f),
            Self::Consumer(err) => err.fmt(f),
        }
    }
}

impl<E: fmt::Display> fmt::Display for SmtLexerReadError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let location = self.location();
        write!(
            f,
            "{} at line {}, column {}",
            self.kind,
            location.line() + 1,
            location.column() + 1
        )
    }
}

impl<E: Error + 'static> Error for SmtLexerReadError<E> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            SmtLexerReadErrorKind::Io(err) => err.source(),
            SmtLexerReadErrorKind::Lexical(_) => None,
            SmtLexerReadErrorKind::Consumer(err) => err.source(),
        }
    }
}

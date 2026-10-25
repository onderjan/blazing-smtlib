use std::{error::Error, fmt, io};

use crate::span::{SmtLocation, SmtSpan};

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

/// What the lexer expected, in [`SmtLexicalErrorKind::Expected`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtLexicalExpected {
    /// A digit of the fractional part of a decimal.
    FractionDigit,
    /// A hexadecimal digit after `#x`.
    HexadecimalDigit,
    /// A binary digit after `#b`.
    BinaryDigit,
    /// The base of a number after `#`: `x` or `b`.
    Base,
}

/// Error that caused lexing to stop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtLexerError<E> {
    cause: SmtLexerErrorCause<E>,
    span: SmtSpan,
    continues_from: Option<SmtLocation>,
}

/// The reason why a lexer call failed: a lexical error or a consumer error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtLexerErrorCause<E> {
    /// The input is lexically malformed.
    Lexical(SmtLexicalErrorKind),
    /// The token consumer returned an error.
    Consumer(E),
}

impl<E> SmtLexerError<E> {
    pub(super) fn new(
        cause: SmtLexerErrorCause<E>,
        span: SmtSpan,
        continues_from: Option<SmtLocation>,
    ) -> Self {
        Self {
            cause,
            span,
            continues_from,
        }
    }

    /// Returns an error with the same cause and continuation location set as requested.
    pub(super) fn continuing_from(mut self, location: SmtLocation) -> Self {
        self.continues_from = Some(location);
        self
    }

    /// The reason why the lexer call failed: a lexical error or a consumer error.
    pub fn cause(&self) -> &SmtLexerErrorCause<E> {
        &self.cause
    }

    /// Converts into the reason why the lexer call failed.
    pub fn into_cause(self) -> SmtLexerErrorCause<E> {
        self.cause
    }

    /// Location where the error occurred.
    pub fn span(&self) -> SmtSpan {
        self.span
    }

    /// The most useful location for deciphering the error.
    ///
    /// Guaranteed to be within the span.
    pub fn location(&self) -> SmtLocation {
        match &self.cause {
            SmtLexerErrorCause::Lexical(kind) => kind.location_in(self.span),
            SmtLexerErrorCause::Consumer(_) => self.span.start(),
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

impl<E: fmt::Display> fmt::Display for SmtLexerErrorCause<E> {
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
            self.cause,
            location.line() + 1,
            location.column() + 1
        )
    }
}

impl<E: Error + 'static> Error for SmtLexerError<E> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.cause {
            SmtLexerErrorCause::Lexical(_) => None,
            SmtLexerErrorCause::Consumer(err) => err.source(),
        }
    }
}

/// Error that ended lexing the input from a buffered reader or a file.
#[derive(Debug)]
pub struct SmtLexerReadError<E> {
    cause: SmtLexerReadErrorCause<E>,
    span: SmtSpan,
}

/// The reason why lexing from a buffered reader or a file failed: an I/O
/// error, a lexical error or a consumer error.
#[derive(Debug)]
pub enum SmtLexerReadErrorCause<E> {
    /// Reading from the file or the buffered reader failed.
    Io(io::Error),
    /// The input is lexically malformed.
    Lexical(SmtLexicalErrorKind),
    /// The token consumer returned an error.
    Consumer(E),
}

impl<E> SmtLexerReadError<E> {
    pub(super) fn new(cause: SmtLexerReadErrorCause<E>, span: SmtSpan) -> Self {
        Self { cause, span }
    }

    /// The reason why lexing failed.
    pub fn cause(&self) -> &SmtLexerReadErrorCause<E> {
        &self.cause
    }

    /// Converts into the reason why lexing failed.
    pub fn into_cause(self) -> SmtLexerReadErrorCause<E> {
        self.cause
    }

    /// Span where the error occurred.
    ///
    /// For I/O errors, the span is empty, at the position where reading failed.
    pub fn span(&self) -> SmtSpan {
        self.span
    }

    /// The most useful location for deciphering the error.
    ///
    /// Guaranteed to be within the span.
    pub fn location(&self) -> SmtLocation {
        match &self.cause {
            SmtLexerReadErrorCause::Lexical(kind) => kind.location_in(self.span),
            SmtLexerReadErrorCause::Io(_) | SmtLexerReadErrorCause::Consumer(_) => {
                self.span.start()
            }
        }
    }
}

impl<E> From<SmtLexerError<E>> for SmtLexerReadError<E> {
    fn from(err: SmtLexerError<E>) -> Self {
        let span = err.span();
        let cause = match err.into_cause() {
            SmtLexerErrorCause::Lexical(kind) => SmtLexerReadErrorCause::Lexical(kind),
            SmtLexerErrorCause::Consumer(err) => SmtLexerReadErrorCause::Consumer(err),
        };
        Self::new(cause, span)
    }
}

impl<E: fmt::Display> fmt::Display for SmtLexerReadErrorCause<E> {
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
            self.cause,
            location.line() + 1,
            location.column() + 1
        )
    }
}

impl<E: Error + 'static> Error for SmtLexerReadError<E> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.cause {
            SmtLexerReadErrorCause::Io(err) => err.source(),
            SmtLexerReadErrorCause::Lexical(_) => None,
            SmtLexerReadErrorCause::Consumer(err) => err.source(),
        }
    }
}

use std::{error::Error, fmt};

use crate::span::{SmtLocation, SmtSpan};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtLexicalErrorKind {
    UnexpectedCharacter,
    /// The item was expected here.
    Expected(SmtLexicalExpected),
    UnclosedStringLiteral,
    ForbiddenCharInString,
    /// A colon is not followed by a keyword name.
    EmptyKeyword,
    BackslashInQuotedSymbol,
    ForbiddenCharInQuotedSymbol,
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
pub struct SmtLexError<E> {
    cause: SmtLexErrorCause<E>,
    span: SmtSpan,
    continues_from: Option<SmtLocation>,
}

/// The reason why a lexer call failed: a lexical error or a consumer error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtLexErrorCause<E> {
    /// The input is lexically malformed.
    Lexical(SmtLexicalErrorKind),
    /// The token consumer returned an error.
    Consumer(E),
}

impl<E> SmtLexError<E> {
    pub(super) fn new(
        cause: SmtLexErrorCause<E>,
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
    pub fn cause(&self) -> &SmtLexErrorCause<E> {
        &self.cause
    }

    /// Converts into the reason why the lexer call failed.
    pub fn into_cause(self) -> SmtLexErrorCause<E> {
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
            SmtLexErrorCause::Lexical(kind) => kind.location_in(self.span),
            SmtLexErrorCause::Consumer(_) => self.span.start(),
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
            SmtLexicalErrorKind::ForbiddenCharInString
            | SmtLexicalErrorKind::BackslashInQuotedSymbol
            | SmtLexicalErrorKind::ForbiddenCharInQuotedSymbol
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
            Self::UnexpectedCharacter => f.write_str("unexpected character"),
            Self::Expected(expected) => expected.fmt(f),
            Self::UnclosedStringLiteral => f.write_str("unclosed string literal"),
            Self::ForbiddenCharInString => f.write_str("forbidden character in string literal"),
            Self::EmptyKeyword => f.write_str("colon without keyword name"),
            Self::BackslashInQuotedSymbol => f.write_str("backslash in quoted symbol"),
            Self::ForbiddenCharInQuotedSymbol => {
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

impl<E: fmt::Display> fmt::Display for SmtLexErrorCause<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lexical(kind) => kind.fmt(f),
            Self::Consumer(err) => err.fmt(f),
        }
    }
}

impl<E: fmt::Display> fmt::Display for SmtLexError<E> {
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

impl<E: Error + 'static> Error for SmtLexError<E> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.cause {
            SmtLexErrorCause::Lexical(_) => None,
            SmtLexErrorCause::Consumer(err) => err.source(),
        }
    }
}

use crate::{SmtLocation, SmtSpan};

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

use crate::{SmtLocation, SmtSpan};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtLexicalErrorKind {
    UnexpectedCharacter,
    FractionDigitExpected,
    HexadecimalDigitExpected,
    BinaryDigitExpected,
    BaseSelectionExpected,
    UnclosedStringLiteral,
    ForbiddenCharInString,
    ForbiddenKeywordName,
    BackslashInQuotedSymbol,
    ForbiddenCharInQuotedSymbol,
    UnclosedQuotedSymbol,
    NumeralLeadingZero,
    MissingDelimiter,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtLexicalError {
    kind: SmtLexicalErrorKind,
    span: SmtSpan,
}

/// Error that caused lexing to stop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtLexError<E> {
    cause: SmtLexErrorCause<E>,
    continues_from: Option<SmtLocation>,
}

/// The reason why a lexer call failed: a lexical error or a consumer error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtLexErrorCause<E> {
    /// The input is lexically malformed.
    Lexical(SmtLexicalError),
    /// The token consumer returned an error.
    Consumer(E),
}

impl<E> SmtLexError<E> {
    pub(super) fn new(cause: SmtLexErrorCause<E>, continues_from: Option<SmtLocation>) -> Self {
        Self {
            cause,
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

    /// The location the rest of the input is to be fed from (if the lexer continues).
    ///
    /// If present, the lexer is recovering: it expects the input from this
    /// location on, and the end of the input once none is left.
    /// If absent, the lexer does not continue this input: either it stops
    /// at its first error, or the input has ended.
    pub fn continues_from(&self) -> Option<SmtLocation> {
        self.continues_from
    }
}

impl SmtLexicalError {
    pub(super) fn new(kind: SmtLexicalErrorKind, span: SmtSpan) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &SmtLexicalErrorKind {
        &self.kind
    }

    pub fn span(&self) -> SmtSpan {
        self.span
    }

    pub fn into_kind(self) -> SmtLexicalErrorKind {
        self.kind
    }
}

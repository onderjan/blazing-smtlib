use crate::SmtSpan;

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtLexError<E> {
    Lexical(SmtLexicalError),
    Consumer(E),
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

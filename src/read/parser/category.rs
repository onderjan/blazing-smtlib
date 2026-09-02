use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSpan, SmtSpecialConstant,
    read::parser::ParserError,
    token::{Token, TokenKind, TokenType},
};

mod attribute;
mod combinator;
mod ident;
mod qualified_ident;
mod s_expr;
mod sort;
mod term;
mod token;

pub use {
    attribute::{ClosedAttributeParser, ClosedMultipleAttributeParser},
    combinator::{
        ClosedMultipleParser, ClosedParser, OpenedParser, PairParser, ParenMultipleParser,
        ParenParser,
    },
    ident::IdentParser,
    qualified_ident::QualifiedIdentParser,
    s_expr::SExprParser,
    sort::SortParser,
    term::TermParser,
    token::{CloseParenParser, KeywordParser, OpenParenParser, StringParser, SymbolParser},
};

pub trait CategoryParser<H: SmtHandler>: Default {
    type Result;

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>>;

    /// Restart the parser to default state.
    ///
    /// The default implementation can be overridden for a performance benefit
    /// to avoid dropping and reconstructing the parser.
    fn restart(&mut self) {
        *self = Self::default();
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CategoryParserErrorKind {
    ExpectedToken(&'static [TokenType]),
    EmptyIdentIndices,
    EmptySortApplication,
    EmptyTermApplication,
    EmptyLetBindings,
    EmptyAnnotation,
    ExpectedIndexOrCloseParen,
    ExpectedOperator,
    ExpectedSExpr,
    ExpectedIdent,
    ExpectedSort,
    ExpectedSortInner,
    ExpectedTerm,
    ExpectedAttribute,
    ExpectedCommand,
    ExpectedCommandName,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CategoryParserError {
    kind: CategoryParserErrorKind,
    span: SmtSpan,
}

impl CategoryParserError {
    pub(crate) fn new(kind: CategoryParserErrorKind, span: SmtSpan) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &CategoryParserErrorKind {
        &self.kind
    }

    pub fn span(&self) -> SmtSpan {
        self.span
    }

    pub fn into_kind(self) -> CategoryParserErrorKind {
        self.kind
    }
}

fn parse_special_constant(kind: TokenKind) -> Result<SmtSpecialConstant, TokenKind> {
    let constant = match kind {
        TokenKind::Numeral(value) => SmtSpecialConstant::Numeral(value.into_owned()),
        TokenKind::Decimal(decimal) => SmtSpecialConstant::Decimal(decimal.into_owned()),
        TokenKind::Hexadecimal(value) => SmtSpecialConstant::Hexadecimal(value.into_owned()),
        TokenKind::Binary(value) => SmtSpecialConstant::Binary(value.into_owned()),
        TokenKind::String(string) => SmtSpecialConstant::String(string.into_owned()),
        kind => return Err(kind),
    };
    Ok(constant)
}

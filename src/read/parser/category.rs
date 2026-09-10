use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSpecialConstant,
    read::parser::{ParserError, ParserResources},
    token::{Token, TokenKind, TokenType},
};

mod attribute;
mod combinator;
mod ident;
mod pattern;
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
    token::{
        CloseParenParser, KeywordParser, NumeralParser, OpenParenParser, StringParser, SymbolParser,
    },
};

pub(crate) use combinator::ParenMaximumParser;

pub type SortedVarParser<H> = ParenParser<H, PairParser<H, SymbolParser, SortParser<H>>>;

pub type ParenSortedVarsParser<H> = ParenMultipleParser<H, SortedVarParser<H>>;

pub trait CategoryParser<H: SmtHandler>: Default {
    type Result;

    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H::Resources>,
        token: &Token,
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
pub enum CategoryErrorKind {
    ExpectedToken(&'static [TokenType]),
    EmptyIdentIndices,
    EmptySortApplication,
    EmptyTermApplication,
    EmptyLetBindings,
    EmptyAnnotation,
    EmptyQuantifierBindings,
    EmptyLambdaBindings,
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
    ExpectedDatatype,
    ExpectedDatatypeKind,
    ExpectedFunctionBody,
    EmptyFunctionSignatures,
    EmptyDatatypeIntroductions,
    EmptyDatatypeParameters,
    EmptyDatatypeConstructors,
    EmptyPatternArguments,
    EmptyMatchCases,
    EmptyGetValueTerms,
}

#[inline]
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

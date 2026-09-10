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

pub trait CategoryParser<H: SmtHandler> {
    type Result;

    /// Parses a single token, progressing the parser.
    ///
    /// If a non-error result is returned, it either signals that the
    /// parser is finished ([`ControlFlow::Break`] with the result value),
    /// or that it is not finished yet ([`ControlFlow::Continue`]).
    ///
    /// All standard parsers implementing [`CategoryParser`] are self-resetting:
    /// after returning [`ControlFlow::Break`], they are back in their initial state.
    ///
    /// The `resources` are shared resources of standard category parsers.
    /// To keep resources valid, each [`CategoryParser`] must progress
    /// until completion once started, i.e. if [`CategoryParser::progress()`]
    /// returns `Ok(Continue(()))`, the subsequent outer progress call
    /// must call [`CategoryParser::progress()`] on the same parser, and
    /// is forbidden from progressing any other parsers.
    /// Failure to heed this contract may lead to silently wrong parsing
    /// or panics, but never unsafe behaviour.
    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources,
        token: &Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>>;

    /// Restarts the parser to its default state.
    fn restart(&mut self);
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

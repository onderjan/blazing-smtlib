use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSpan, SmtSpecialConstant,
    read::parser::ParserError,
    token::{Token, TokenKind, TokenType},
};

mod attribute;
mod ident;
mod qualified_ident;
mod s_expr;
mod sort;
mod term;
mod token;

pub use {
    attribute::ClosedAttributeParser,
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
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserError<H>>;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CategoryParserErrorKind {
    ExpectedToken(&'static [TokenType]),
    EmptyIdentIndices,
    EmptySortApplication,
    EmptyTermApplication,
    EmptyLetBindings,
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

pub enum PairParser<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> {
    First(P1),
    Second(P1::Result, P2),
}

impl<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> PairParser<H, P1, P2> {
    pub fn new() -> Self {
        Self::First(P1::default())
    }
}

impl<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> Default
    for PairParser<H, P1, P2>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> CategoryParser<H>
    for PairParser<H, P1, P2>
{
    type Result = (P1::Result, P2::Result);

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserError<H>> {
        let result = match self {
            PairParser::First(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => Self::First(parser),
                ControlFlow::Break(first) => Self::Second(first, P2::default()),
            },
            PairParser::Second(first, parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => Self::Second(first, parser),
                ControlFlow::Break(second) => return Ok(ControlFlow::Break((first, second))),
            },
        };
        Ok(ControlFlow::Continue(result))
    }
}

pub enum ClosedParser<H: SmtHandler, P: CategoryParser<H>> {
    Inner(P),
    BeforeClose(P::Result),
}

impl<H: SmtHandler, P: CategoryParser<H>> ClosedParser<H, P> {
    pub fn new() -> Self {
        Self::Inner(P::default())
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> Default for ClosedParser<H, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for ClosedParser<H, P> {
    type Result = P::Result;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserError<H>> {
        let span = token.span();
        let result = match self {
            Self::Inner(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => Self::Inner(parser),
                ControlFlow::Break(result) => Self::BeforeClose(result),
            },
            Self::BeforeClose(result) => {
                if matches!(token.kind(), TokenKind::ParenClose) {
                    return Ok(ControlFlow::Break(result));
                } else {
                    let kind = CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose]);
                    return Err(CategoryParserError::new(kind, span).into());
                }
            }
        };
        Ok(ControlFlow::Continue(result))
    }
}

pub enum OpenClosedParser<H: SmtHandler, P: CategoryParser<H>> {
    BeforeOpen,
    AfterOpen(ClosedParser<H, P>),
}

impl<H: SmtHandler, P: CategoryParser<H>> OpenClosedParser<H, P> {
    pub fn new() -> Self {
        Self::BeforeOpen
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> Default for OpenClosedParser<H, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for OpenClosedParser<H, P> {
    type Result = P::Result;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserError<H>> {
        let span = token.span();
        let result = match self {
            OpenClosedParser::BeforeOpen => {
                if matches!(token.kind(), TokenKind::ParenOpen) {
                    Self::AfterOpen(ClosedParser::default())
                } else {
                    return Err(ParserError::category_error(
                        CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen]),
                        span,
                    ));
                }
            }
            OpenClosedParser::AfterOpen(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => Self::AfterOpen(parser),
                ControlFlow::Break(result) => return Ok(ControlFlow::Break(result)),
            },
        };
        Ok(ControlFlow::Continue(result))
    }
}

pub enum MultipleParser<H: SmtHandler, P: CategoryParser<H>> {
    BeforeOpen,
    Normal {
        results: Vec<P::Result>,
        parser: Option<P>,
    },
}

impl<H: SmtHandler, P: CategoryParser<H>> MultipleParser<H, P> {
    pub fn new() -> Self {
        Self::BeforeOpen
    }

    pub fn after_open_paren() -> Self {
        Self::Normal {
            results: Vec::new(),
            parser: None,
        }
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> Default for MultipleParser<H, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for MultipleParser<H, P> {
    type Result = Vec<P::Result>;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Vec<P::Result>, Self>, ParserError<H>> {
        let span = token.span();
        match self {
            MultipleParser::BeforeOpen => {
                if matches!(token.kind(), TokenKind::ParenOpen) {
                    Ok(ControlFlow::Continue(Self::Normal {
                        results: Vec::new(),
                        parser: None,
                    }))
                } else {
                    Err(ParserError::category_error(
                        CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen]),
                        span,
                    ))
                }
            }
            MultipleParser::Normal {
                mut results,
                parser,
            } => {
                let parser = match parser {
                    Some(parser) => parser,
                    None => {
                        // close parenthesis ends processing
                        if matches!(token.kind(), TokenKind::ParenClose) {
                            return Ok(ControlFlow::Break(results));
                        } else {
                            P::default()
                        }
                    }
                };

                match parser.progress(handler, token)? {
                    ControlFlow::Continue(parser) => Ok(ControlFlow::Continue(Self::Normal {
                        results,
                        parser: Some(parser),
                    })),
                    ControlFlow::Break(result) => {
                        results.push(result);
                        Ok(ControlFlow::Continue(Self::Normal {
                            results,
                            parser: None,
                        }))
                    }
                }
            }
        }
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

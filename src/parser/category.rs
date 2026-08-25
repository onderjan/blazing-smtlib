use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSymbol,
    parser::{ParserError, ParserOrHandlerError},
    token::Token,
};

pub mod attribute;
pub mod ident;
pub mod sort;
pub mod term;

pub trait CategoryParser<H: SmtHandler>
where
    Self: std::marker::Sized,
{
    type Result;

    fn init() -> Self;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserOrHandlerError<H>>;
}

pub enum PairParser<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> {
    First(P1),
    Second(P1::Result, P2),
}

impl<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> CategoryParser<H>
    for PairParser<H, P1, P2>
{
    type Result = (P1::Result, P2::Result);

    fn init() -> Self {
        Self::First(P1::init())
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserOrHandlerError<H>> {
        let result = match self {
            PairParser::First(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => Self::First(parser),
                ControlFlow::Break(first) => Self::Second(first, P2::init()),
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

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for ClosedParser<H, P> {
    type Result = P::Result;

    fn init() -> Self {
        Self::Inner(P::init())
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserOrHandlerError<H>> {
        let result = match self {
            Self::Inner(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => Self::Inner(parser),
                ControlFlow::Break(result) => Self::BeforeClose(result),
            },
            Self::BeforeClose(result) => {
                if matches!(token, Token::ParenClose) {
                    return Ok(ControlFlow::Break(result));
                } else {
                    return Err(ParserError::ExpectedToken(Token::ParenClose).into());
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

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for OpenClosedParser<H, P> {
    type Result = P::Result;

    fn init() -> Self {
        Self::BeforeOpen
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserOrHandlerError<H>> {
        let result = match self {
            OpenClosedParser::BeforeOpen => {
                if matches!(token, Token::ParenOpen) {
                    Self::AfterOpen(ClosedParser::init())
                } else {
                    return Err(ParserError::ExpectedToken(Token::ParenOpen).into());
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

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for MultipleParser<H, P> {
    type Result = Vec<P::Result>;

    fn init() -> Self {
        Self::BeforeOpen
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Vec<P::Result>, Self>, ParserOrHandlerError<H>> {
        match self {
            MultipleParser::BeforeOpen => {
                if matches!(token, Token::ParenOpen) {
                    Ok(ControlFlow::Continue(Self::Normal {
                        results: Vec::new(),
                        parser: None,
                    }))
                } else {
                    Err(ParserError::ExpectedToken(Token::ParenOpen).into())
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
                        if matches!(token, Token::ParenClose) {
                            return Ok(ControlFlow::Break(results));
                        } else {
                            P::init()
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

/*
impl<H: SmtHandler, P: CategoryParser<H>> MultipleParser<H, P> {
    pub fn after_open_paren() -> Self {
        Self::Normal {
            results: Vec::new(),
            parser: None,
        }
    }
}*/

pub struct SymbolParser;

impl<H: SmtHandler> CategoryParser<H> for SymbolParser {
    type Result = SmtSymbol;

    fn init() -> Self {
        Self
    }

    fn progress(
        self,
        _handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserOrHandlerError<H>> {
        if let Token::Symbol(symbol) = token {
            Ok(ControlFlow::Break(symbol))
        } else {
            Err(ParserError::ExpectedSymbol.into())
        }
    }
}

pub struct CloseParenParser;

impl<H: SmtHandler> CategoryParser<H> for CloseParenParser {
    type Result = ();

    fn init() -> Self {
        Self
    }

    fn progress(
        self,
        _handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>> {
        if matches!(token, Token::ParenClose) {
            Ok(ControlFlow::Break(()))
        } else {
            Err(ParserError::ExpectedSymbol.into())
        }
    }
}

fn expect_close_parenthesis<H: SmtHandler>(token: Token) -> Result<(), ParserOrHandlerError<H>> {
    if matches!(token, Token::ParenClose) {
        Ok(())
    } else {
        Err(ParserError::ExpectedToken(Token::ParenClose).into())
    }
}

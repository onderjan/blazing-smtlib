use std::ops::ControlFlow;

use crate::{
    SmtHandler,
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

use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIdent, SmtSort,
    parser::{
        ParserError, ParserOrHandlerError,
        category::{CategoryParser, ident::IdentParser},
    },
    token::{Reserved, Token},
};

pub enum SortParser {
    Start,
    Open,
    Ident(IdentParser),
}

impl<H: SmtHandler> CategoryParser<H> for SortParser {
    type Result = H::Sort;

    fn init() -> Self {
        Self::Start
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Sort, Self>, ParserOrHandlerError<H>> {
        let sort = match self {
            SortParser::Start => match token {
                Token::Symbol(name) => {
                    // the sort consists just of a non-indexed ident
                    let ident = SmtIdent {
                        name,
                        indices: Vec::new(),
                    };
                    SmtSort::Ident(ident)
                }
                Token::ParenOpen => return Ok(ControlFlow::Continue(Self::Open)),
                _ => return Err(ParserError::ExpectedSort.into()),
            },
            SortParser::Open => match token {
                Token::Reserved(Reserved::Underscore) => {
                    return Ok(ControlFlow::Continue(SortParser::Ident(
                        IdentParser::after_underscore(),
                    )));
                }
                _ => {
                    // TODO: should parse sort ident here
                    return Err(ParserError::ExpectedSortInner.into());
                }
            },

            SortParser::Ident(state) => match state.progress(handler, token)? {
                ControlFlow::Continue(state) => {
                    return Ok(ControlFlow::Continue(SortParser::Ident(state)));
                }
                ControlFlow::Break(ident) => SmtSort::Ident(ident),
            },
        };

        let sort = handler
            .handle_sort(sort)
            .map_err(ParserOrHandlerError::HandlerError)?;
        Ok(ControlFlow::Break(sort))
    }
}

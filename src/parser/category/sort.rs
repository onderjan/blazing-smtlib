use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSort,
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
        match self {
            SortParser::Start => match token {
                Token::Symbol(_symbol) => {
                    todo!("Indexed sort");
                }
                Token::ParenOpen => Ok(ControlFlow::Continue(Self::Open)),
                _ => Err(ParserError::ExpectedSort.into()),
            },
            SortParser::Open => match token {
                Token::Reserved(Reserved::Underscore) => Ok(ControlFlow::Continue(
                    SortParser::Ident(IdentParser::after_underscore()),
                )),
                _ => Err(ParserError::ExpectedSortInner.into()),
            },

            SortParser::Ident(state) => match state.progress(handler, token)? {
                ControlFlow::Continue(state) => Ok(ControlFlow::Continue(SortParser::Ident(state))),
                ControlFlow::Break(ident) => {
                    let sort = SmtSort::Ident(ident);
                    let sort = handler
                        .handle_sort(sort)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    Ok(ControlFlow::Break(sort))
                }
            },
        }
    }
}

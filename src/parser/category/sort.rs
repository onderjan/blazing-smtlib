use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSort,
    parser::{ParserError, ParserOrHandlerError, category::index::IndexedIdentParserState},
    token::{Reserved, Token},
};

pub enum SortParser<H: SmtHandler> {
    Start,
    IndexedIdent(IndexedIdentParserState<H>),
}

impl<H: SmtHandler> SortParser<H> {
    pub fn new() -> Self {
        Self::Start
    }

    pub fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Sort, Self>, ParserOrHandlerError<H>> {
        match self {
            SortParser::Start => match token {
                Token::Symbol(symbol) => {
                    let _symbol = handler
                        .handle_symbol(symbol.as_str())
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    todo!("Indexed sort");
                }
                Token::Reserved(Reserved::Underscore) => Ok(ControlFlow::Continue(
                    SortParser::IndexedIdent(IndexedIdentParserState::AwaitingSymbol),
                )),
                _ => Err(ParserError::ExpectedSortInner.into()),
            },
            SortParser::IndexedIdent(state) => match state.progress(handler, token)? {
                ControlFlow::Continue(state) => {
                    Ok(ControlFlow::Continue(SortParser::IndexedIdent(state)))
                }
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

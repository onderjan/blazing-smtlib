use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSort,
    parser::{
        ParserError, ParserOrHandlerError, ParserState, category::index::IndexedIdentParserState,
    },
    token::{Reserved, Token},
};

/*
pub fn parse_sort<H: SmtHandler>(
    handler: &mut H,
    callback: CommandCallback<H, H::Sort>,
    token: Token,
) -> Result<ParserState<H>, ParserOrHandlerError<H>> {
    match token {
        Token::Symbol(symbol) => {
            let ident = handler
                .handle_ident(symbol.as_str(), Vec::new())
                .map_err(ParserOrHandlerError::HandlerError)?;
            let sort = SmtSort::Ident(ident);
            let sort = handler
                .handle_sort(sort)
                .map_err(ParserOrHandlerError::HandlerError)?;

            Ok(progress_state(
                callback(handler, sort).map_err(ParserOrHandlerError::HandlerError)?,
            ))
        }
        Token::ParenOpen => Ok(ParserState::Sort(CategoryParserState::new(
            callback,
            SortParserState::Deciding,
        ))),
        _ => Err(ParserError::ExpectedSort.into()),
    }
}

pub enum SortParserState<H: SmtHandler> {
    Deciding,
    IndexedIdent(IndexedIdentParserState<H>),
}

impl<H: SmtHandler> CategoryParser<H> for SortParserState<H> {
    type Category = H::Sort;

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Sort, ()>, ParserOrHandlerError<H>> {
        match self {
            SortParserState::Deciding => match token {
                Token::Symbol(symbol) => {
                    let _symbol = handler
                        .handle_symbol(symbol.as_str())
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    todo!("Indexed sort");
                }
                Token::Reserved(Reserved::Underscore) => {
                    *self = SortParserState::IndexedIdent(IndexedIdentParserState::AwaitingSymbol);
                    Ok(ControlFlow::Continue(()))
                }
                _ => Err(ParserError::ExpectedSortInner.into()),
            },
            SortParserState::IndexedIdent(state) => match state.progress(handler, token)? {
                ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
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
*/

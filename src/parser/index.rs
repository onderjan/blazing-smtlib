use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIndex, String8,
    parser::{ParserError, ParserOrHandlerError},
    token::Token,
};

pub enum IndexedIdentParserState<H: SmtHandler> {
    AwaitingSymbol,
    ProcessingIndices {
        symbol: String8,
        indices: Vec<H::Index>,
    },
}

impl<H: SmtHandler> IndexedIdentParserState<H> {
    pub fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Ident>, ParserOrHandlerError<H>> {
        match self {
            IndexedIdentParserState::AwaitingSymbol => {
                let Token::Symbol(symbol) = token else {
                    return Err(ParserError::ExpectedSymbol.into());
                };
                *self = IndexedIdentParserState::ProcessingIndices {
                    symbol,
                    indices: Vec::new(),
                };
                Ok(ControlFlow::Continue(()))
            }
            IndexedIdentParserState::ProcessingIndices { symbol, indices } => match token {
                Token::ParenOpen => {
                    todo!("Multiply-indexed token");
                }
                Token::ParenClose => {
                    let mut final_indices = Vec::new();
                    std::mem::swap(indices, &mut final_indices);
                    let ident = handler
                        .handle_ident(symbol.as_str(), final_indices)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    Ok(ControlFlow::Break(ident))
                }
                Token::Numeral(value) => {
                    // numeral index
                    let index = handler
                        .handle_index(SmtIndex::Numeral(value.as_str()))
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    indices.push(index);
                    Ok(ControlFlow::Continue(()))
                }
                Token::Symbol(symbol) => {
                    // symbol index
                    let index = handler
                        .handle_index(SmtIndex::Symbol(symbol.as_str()))
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    indices.push(index);
                    Ok(ControlFlow::Continue(()))
                }
                _ => Err(ParserError::ExpectedIndexOrCloseParen.into()),
            },
        }
    }
}

use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIndex, String8,
    parser::{ParserError, ParserOrHandlerError, category::CategoryParser},
    token::Token,
};

pub enum IndexedIdentParserState<H: SmtHandler> {
    AwaitingSymbol,
    ProcessingIndices {
        symbol: String8,
        indices: Vec<H::Index>,
    },
}

impl<H: SmtHandler> CategoryParser<H> for IndexedIdentParserState<H> {
    type Result = H::Ident;

    fn init() -> Self {
        Self::AwaitingSymbol
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Ident, Self>, ParserOrHandlerError<H>> {
        match self {
            IndexedIdentParserState::AwaitingSymbol => {
                let Token::Symbol(symbol) = token else {
                    return Err(ParserError::ExpectedSymbol.into());
                };
                Ok(ControlFlow::Continue(
                    IndexedIdentParserState::ProcessingIndices {
                        symbol,
                        indices: Vec::new(),
                    },
                ))
            }
            IndexedIdentParserState::ProcessingIndices {
                symbol,
                mut indices,
            } => match token {
                Token::ParenOpen => {
                    todo!("Multiply-indexed token");
                }
                Token::ParenClose => {
                    let ident = handler
                        .handle_ident(symbol.as_str(), indices)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    Ok(ControlFlow::Break(ident))
                }
                Token::Numeral(value) => {
                    // numeral index
                    let index = handler
                        .handle_index(SmtIndex::Numeral(value.as_str()))
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    indices.push(index);
                    Ok(ControlFlow::Continue(Self::ProcessingIndices {
                        symbol,
                        indices,
                    }))
                }
                Token::Symbol(symbol) => {
                    // symbol index
                    let index = handler
                        .handle_index(SmtIndex::Symbol(symbol.as_str()))
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    indices.push(index);
                    Ok(ControlFlow::Continue(Self::ProcessingIndices {
                        symbol,
                        indices,
                    }))
                }
                _ => Err(ParserError::ExpectedIndexOrCloseParen.into()),
            },
        }
    }
}

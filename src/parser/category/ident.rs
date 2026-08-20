use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIndex, String8,
    parser::{ParserError, ParserOrHandlerError, category::CategoryParser},
    token::{Reserved, Token},
};

pub enum IdentParser<H: SmtHandler> {
    Start,
    Open,
    AfterUnderscore,
    Indices {
        symbol: String8,
        indices: Vec<H::Index>,
    },
}

impl<H: SmtHandler> CategoryParser<H> for IdentParser<H> {
    type Result = H::Ident;

    fn init() -> Self {
        Self::Start
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Ident, Self>, ParserOrHandlerError<H>> {
        match self {
            IdentParser::Start => match token {
                Token::Symbol(symbol) => {
                    let symbol = handler
                        .handle_ident(symbol.as_str(), vec![])
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    Ok(ControlFlow::Break(symbol))
                }
                Token::ParenOpen => Ok(ControlFlow::Continue(Self::Open)),
                _ => Err(ParserError::ExpectedIdent.into()),
            },
            IdentParser::Open => {
                // this must be an underscore
                if matches!(token, Token::Reserved(Reserved::Underscore)) {
                    Ok(ControlFlow::Continue(Self::AfterUnderscore))
                } else {
                    Err(ParserError::ExpectedToken(Token::Reserved(Reserved::Underscore)).into())
                }
            }
            IdentParser::AfterUnderscore => {
                if let Token::Symbol(symbol) = token {
                    Ok(ControlFlow::Continue(IdentParser::Indices {
                        symbol,
                        indices: Vec::new(),
                    }))
                } else {
                    Err(ParserError::ExpectedSymbol.into())
                }
            }
            IdentParser::Indices {
                symbol,
                mut indices,
            } => match token {
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
                    Ok(ControlFlow::Continue(Self::Indices { symbol, indices }))
                }
                Token::Symbol(symbol) => {
                    // symbol index
                    let index = handler
                        .handle_index(SmtIndex::Symbol(symbol.as_str()))
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    indices.push(index);
                    Ok(ControlFlow::Continue(Self::Indices { symbol, indices }))
                }
                _ => Err(ParserError::ExpectedIndexOrCloseParen.into()),
            },
        }
    }
}

impl<H: SmtHandler> IdentParser<H> {
    pub fn after_underscore() -> Self {
        Self::AfterUnderscore
    }
}

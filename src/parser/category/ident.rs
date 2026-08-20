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
        name: String8,
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
                        .handle_ident(symbol, vec![])
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
                if let Token::Symbol(name) = token {
                    Ok(ControlFlow::Continue(IdentParser::Indices {
                        name,
                        indices: Vec::new(),
                    }))
                } else {
                    Err(ParserError::ExpectedSymbol.into())
                }
            }
            IdentParser::Indices { name, mut indices } => match token {
                Token::ParenClose => {
                    let ident = handler
                        .handle_ident(name, indices)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    Ok(ControlFlow::Break(ident))
                }
                Token::Numeral(index_value) => {
                    // numeral index
                    let index = handler
                        .handle_index(SmtIndex::Numeral(index_value))
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    indices.push(index);
                    Ok(ControlFlow::Continue(Self::Indices { name, indices }))
                }
                Token::Symbol(index_symbol) => {
                    // symbol index
                    let index = handler
                        .handle_index(SmtIndex::Symbol(index_symbol))
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    indices.push(index);
                    Ok(ControlFlow::Continue(Self::Indices { name, indices }))
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

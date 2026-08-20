use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIdent, SmtIndex, String8,
    parser::{ParserError, ParserOrHandlerError, category::CategoryParser},
    token::{Reserved, Token},
};

pub enum IdentParser {
    Start,
    Open,
    AfterUnderscore,
    Indices {
        name: String8,
        indices: Vec<SmtIndex>,
    },
}

impl<H: SmtHandler> CategoryParser<H> for IdentParser {
    type Result = SmtIdent;

    fn init() -> Self {
        Self::Start
    }

    fn progress(
        self,
        _handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<SmtIdent, Self>, ParserOrHandlerError<H>> {
        match self {
            IdentParser::Start => match token {
                Token::Symbol(name) => Ok(ControlFlow::Break(SmtIdent {
                    name,
                    indices: Vec::new(),
                })),
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
                    if indices.is_empty() {
                        return Err(ParserError::RequiredIndices.into());
                    }
                    Ok(ControlFlow::Break(SmtIdent { name, indices }))
                }
                Token::Numeral(index_value) => {
                    indices.push(SmtIndex::Numeral(index_value));
                    Ok(ControlFlow::Continue(Self::Indices { name, indices }))
                }
                Token::Symbol(index_symbol) => {
                    indices.push(SmtIndex::Symbol(index_symbol));
                    Ok(ControlFlow::Continue(Self::Indices { name, indices }))
                }
                _ => Err(ParserError::ExpectedIndexOrCloseParen.into()),
            },
        }
    }
}

impl IdentParser {
    pub fn after_open_paren() -> Self {
        Self::Open
    }

    pub fn after_underscore() -> Self {
        Self::AfterUnderscore
    }
}

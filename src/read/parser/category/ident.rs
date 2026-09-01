use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIdent, SmtIndex, SmtSymbol,
    read::parser::{
        CategoryParserError, ParserError,
        category::{CategoryParser, CategoryParserErrorKind},
    },
    token::{Reserved, Token, TokenKind, TokenType},
};

pub enum IdentParser {
    Start,
    Open,
    AfterUnderscore,
    Indices {
        name: SmtSymbol,
        indices: Vec<SmtIndex>,
    },
}

impl IdentParser {
    pub fn new() -> Self {
        Self::Start
    }

    pub fn after_open_paren() -> Self {
        Self::Open
    }

    pub fn after_underscore() -> Self {
        Self::AfterUnderscore
    }
}

impl Default for IdentParser {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for IdentParser {
    type Result = SmtIdent;

    fn progress(
        self,
        _handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<SmtIdent, Self>, ParserError<H>> {
        let span = token.span();
        match self {
            IdentParser::Start => match token.kind() {
                TokenKind::Symbol(name) => {
                    Ok(ControlFlow::Break(SmtIdent::new_simple(name.into_owned())))
                }
                TokenKind::ParenOpen => Ok(ControlFlow::Continue(Self::Open)),
                _ => {
                    let kind = CategoryParserErrorKind::ExpectedIdent;
                    Err(CategoryParserError::new(kind, span).into())
                }
            },
            IdentParser::Open => {
                // this must be an underscore
                if matches!(token.kind(), TokenKind::Reserved(Reserved::Underscore)) {
                    Ok(ControlFlow::Continue(Self::AfterUnderscore))
                } else {
                    let kind = CategoryParserErrorKind::ExpectedToken(&[TokenType::Reserved(
                        Reserved::Underscore,
                    )]);
                    Err(CategoryParserError::new(kind, span).into())
                }
            }
            IdentParser::AfterUnderscore => {
                if let TokenKind::Symbol(name) = token.kind() {
                    Ok(ControlFlow::Continue(IdentParser::Indices {
                        name: name.into_owned(),
                        indices: Vec::new(),
                    }))
                } else {
                    let kind = CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol]);
                    Err(CategoryParserError::new(kind, span).into())
                }
            }
            IdentParser::Indices { name, mut indices } => match token.kind() {
                TokenKind::ParenClose => {
                    if indices.is_empty() {
                        let kind = CategoryParserErrorKind::EmptyIdentIndices;
                        return Err(CategoryParserError::new(kind, span).into());
                    }
                    Ok(ControlFlow::Break(SmtIdent { name, indices }))
                }
                TokenKind::Numeral(index_value) => {
                    indices.push(SmtIndex::Numeral(index_value.into_owned()));
                    Ok(ControlFlow::Continue(Self::Indices { name, indices }))
                }
                TokenKind::Symbol(index_symbol) => {
                    indices.push(SmtIndex::Symbol(index_symbol.into_owned()));
                    Ok(ControlFlow::Continue(Self::Indices { name, indices }))
                }
                _ => {
                    let kind = CategoryParserErrorKind::ExpectedIndexOrCloseParen;
                    Err(CategoryParserError::new(kind, span).into())
                }
            },
        }
    }
}

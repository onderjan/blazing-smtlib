use std::ops::ControlFlow;

use crate::{
    SmtAttributeValue, SmtHandler, SmtSpecialConstant, String8,
    parser::{ParserError, ParserOrHandlerError},
    token::Token,
};

/*
pub fn parse_attribute<H: SmtHandler>(
    handler: &mut H,
    token: Token,
) -> Result<<H>, ParserOrHandlerError<H>> {
    let Token::Keyword(keyword) = token else {
        return Err(ParserOrHandlerError::ParserError(
            ParserError::ExpectedKeyword,
        ));
    };

    // TODO: name-value attributes
    let attribute = handler
        .handle_attribute(keyword.as_str(), None)
        .map_err(ParserOrHandlerError::HandlerError)?;
    Ok(progress_state(
        callback(handler, attribute).map_err(ParserOrHandlerError::HandlerError)?,
    ))
}*/

pub enum AttributeParser<H: SmtHandler> {
    Key,
    Value(String8),
    ValueSExprs(String8, Vec<H::Attribute>),
}

pub struct AttributeParserResult<H: SmtHandler> {
    pub attribute: H::Attribute,
    pub returned_token: Option<Token>,
}

impl<H: SmtHandler> AttributeParser<H> {
    pub fn new() -> Self {
        Self::Key
    }

    pub fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<AttributeParserResult<H>, ()>, ParserOrHandlerError<H>> {
        match self {
            AttributeParser::Key => {
                let Token::Keyword(keyword) = token else {
                    return Err(ParserError::ExpectedKeyword.into());
                };
                *self = AttributeParser::Value(keyword);
                Ok(ControlFlow::Continue(()))
            }

            AttributeParser::Value(keyword) => {
                let value = match token {
                    Token::Numeral(value) => {
                        SmtAttributeValue::SpecialConstant(SmtSpecialConstant::Numeral(value))
                    }
                    Token::Decimal {
                        numerator,
                        denominator,
                    } => SmtAttributeValue::SpecialConstant(SmtSpecialConstant::Decimal {
                        numerator,
                        denominator,
                    }),
                    Token::Hexadecimal(value) => {
                        SmtAttributeValue::SpecialConstant(SmtSpecialConstant::Hexadecimal(value))
                    }
                    Token::Binary(value) => {
                        SmtAttributeValue::SpecialConstant(SmtSpecialConstant::Binary(value))
                    }
                    Token::String(string) => {
                        SmtAttributeValue::SpecialConstant(SmtSpecialConstant::String(string))
                    }
                    Token::Symbol(symbol) => SmtAttributeValue::Symbol(symbol),
                    Token::ParenOpen => {
                        todo!("Attribute value SExpr")
                    }
                    _ => {
                        // just an attribute name, return token after handling
                        let attribute = handler
                            .handle_attribute(keyword.as_str(), None)
                            .map_err(ParserOrHandlerError::HandlerError)?;
                        return Ok(ControlFlow::Break(AttributeParserResult {
                            attribute,
                            returned_token: Some(token),
                        }));
                    }
                };

                let attribute = handler
                    .handle_attribute(keyword.as_str(), Some(value))
                    .map_err(ParserOrHandlerError::HandlerError)?;

                Ok(ControlFlow::Break(AttributeParserResult {
                    attribute,
                    returned_token: None,
                }))
            }
            AttributeParser::ValueSExprs(string8, items) => {
                todo!("Parse attribute value SExprs")
            }
        }
    }
}

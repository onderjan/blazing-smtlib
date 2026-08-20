use std::ops::ControlFlow;

use crate::{
    SmtAttributeValue, SmtHandler, SmtSpecialConstant, String8,
    parser::{ParserError, ParserOrHandlerError, category::CategoryParser},
    token::Token,
};

pub enum AttributeParser<H: SmtHandler> {
    Key,
    Value(String8),
    ValueSExprs(String8, Vec<H::Attribute>),
}

pub struct AttributeParserResult<H: SmtHandler> {
    pub attribute: H::Attribute,
    pub returned_token: Option<Token>,
}

impl<H: SmtHandler> CategoryParser<H> for AttributeParser<H> {
    type Result = AttributeParserResult<H>;

    fn init() -> Self {
        Self::Key
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<AttributeParserResult<H>, Self>, ParserOrHandlerError<H>> {
        match self {
            AttributeParser::Key => {
                let Token::Keyword(keyword) = token else {
                    return Err(ParserError::ExpectedKeyword.into());
                };
                Ok(ControlFlow::Continue(AttributeParser::Value(keyword)))
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

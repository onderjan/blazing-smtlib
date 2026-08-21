use std::ops::ControlFlow;

use crate::{
    SmtAttributeValue, SmtHandler, SmtSpecialConstant, String8,
    parser::{
        ParserError, ParserOrHandlerError,
        category::{CategoryParser, expect_close_parenthesis},
    },
    token::Token,
};

pub enum ClosedAttributeParser<H: SmtHandler> {
    Start,
    Key(String8),
    BeforeClose(H::Attribute),
}

impl<H: SmtHandler> CategoryParser<H> for ClosedAttributeParser<H> {
    type Result = H::Attribute;

    fn init() -> Self {
        Self::Start
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Attribute, Self>, ParserOrHandlerError<H>> {
        match self {
            ClosedAttributeParser::Start => {
                let Token::Keyword(keyword) = token else {
                    return Err(ParserError::ExpectedKeyword.into());
                };
                Ok(ControlFlow::Continue(ClosedAttributeParser::Key(keyword)))
            }

            ClosedAttributeParser::Key(keyword) => {
                let value = match token {
                    Token::Numeral(value) => {
                        SmtAttributeValue::SpecialConstant(SmtSpecialConstant::Numeral(value))
                    }
                    Token::Decimal {
                        whole_part,
                        fractional_part,
                    } => SmtAttributeValue::SpecialConstant(SmtSpecialConstant::Decimal {
                        whole_part,
                        fractional_part,
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
                    Token::ParenClose => {
                        // just an attribute name, return token after handling
                        let attribute = handler
                            .handle_attribute(keyword, None)
                            .map_err(ParserOrHandlerError::HandlerError)?;
                        return Ok(ControlFlow::Break(attribute));
                    }
                    _ => return Err(ParserError::ExpectedAttribute.into()),
                };

                let attribute = handler
                    .handle_attribute(keyword, Some(value))
                    .map_err(ParserOrHandlerError::HandlerError)?;

                Ok(ControlFlow::Continue(Self::BeforeClose(attribute)))
            }
            ClosedAttributeParser::BeforeClose(attribute) => {
                expect_close_parenthesis(token)?;
                Ok(ControlFlow::Break(attribute))
            }
        }
    }
}

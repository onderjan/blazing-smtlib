use std::ops::ControlFlow;

use crate::{
    SmtAttributeValue, SmtHandler, SmtKeyword, SmtSpecialConstant,
    read::parser::{
        ParserError, ParserOrHandlerError,
        category::{CategoryParser, expect_close_parenthesis},
    },
    token::{Token, TokenKind},
};

pub enum ClosedAttributeParser<H: SmtHandler> {
    Start,
    Key(SmtKeyword),
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
                let TokenKind::Keyword(keyword) = token.into_kind() else {
                    return Err(ParserError::ExpectedKeyword.into());
                };
                Ok(ControlFlow::Continue(ClosedAttributeParser::Key(keyword)))
            }

            ClosedAttributeParser::Key(keyword) => {
                let value = match token.into_kind() {
                    TokenKind::Numeral(value) => {
                        SmtAttributeValue::SpecialConstant(SmtSpecialConstant::Numeral(value))
                    }
                    TokenKind::Decimal(decimal) => {
                        SmtAttributeValue::SpecialConstant(SmtSpecialConstant::Decimal(decimal))
                    }
                    TokenKind::Hexadecimal(value) => {
                        SmtAttributeValue::SpecialConstant(SmtSpecialConstant::Hexadecimal(value))
                    }
                    TokenKind::Binary(value) => {
                        SmtAttributeValue::SpecialConstant(SmtSpecialConstant::Binary(value))
                    }
                    TokenKind::String(string) => {
                        SmtAttributeValue::SpecialConstant(SmtSpecialConstant::String(string))
                    }
                    TokenKind::Symbol(symbol) => SmtAttributeValue::Symbol(symbol),
                    TokenKind::ParenOpen => {
                        todo!("Attribute value SExpr")
                    }
                    TokenKind::ParenClose => {
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

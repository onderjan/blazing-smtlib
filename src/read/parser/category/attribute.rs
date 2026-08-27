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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::read::parser::category::tests::{Printing, assert_error, parse_all, run};

    type P = ClosedAttributeParser<Printing>;

    #[test]
    fn attribute_without_value() {
        assert_eq!(parse_all::<P>(b":produce-models)"), ":produce-models");
    }

    #[test]
    fn attribute_with_value() {
        assert_eq!(parse_all::<P>(b":status sat)"), ":status sat");
        assert_eq!(parse_all::<P>(b":timeout 1000)"), ":timeout 1000");
        assert_eq!(parse_all::<P>(b":ratio 0.5)"), ":ratio 0.5");
        assert_eq!(parse_all::<P>(b":mask #xff)"), ":mask #xff");
        assert_eq!(parse_all::<P>(b":bits #b01)"), ":bits #b01");
        assert_eq!(parse_all::<P>(b":source \"me\")"), ":source \"me\"");
        assert_eq!(parse_all::<P>(b":name |a b|)"), ":name a b");
    }

    #[test]
    fn stops_after_closing_paren() {
        let (attribute, left) = run::<P>(b":status sat) x").expect("valid");
        assert_eq!(attribute, ":status sat");
        assert_eq!(left, 1);
    }

    #[test]
    fn errors() {
        let err = assert_error::<P>(b"status sat)", 0, 6);
        assert!(matches!(err, ParserError::ExpectedKeyword), "{err:?}");

        let err = assert_error::<P>(b"", 0, 0);
        assert!(matches!(err, ParserError::ExpectedKeyword), "{err:?}");

        // a keyword is not a valid value
        let err = assert_error::<P>(b":a :b)", 3, 5);
        assert!(matches!(err, ParserError::ExpectedAttribute), "{err:?}");

        // only one value
        let err = assert_error::<P>(b":a 1 2)", 5, 6);
        assert!(
            matches!(err, ParserError::ExpectedToken(TokenKind::ParenClose)),
            "{err:?}"
        );

        // EOF after the value
        let err = assert_error::<P>(b":a 1", 4, 4);
        assert!(
            matches!(err, ParserError::ExpectedToken(TokenKind::ParenClose)),
            "{err:?}"
        );
    }
}

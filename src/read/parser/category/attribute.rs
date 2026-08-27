use std::ops::ControlFlow;

use crate::{
    SmtAttributeValue, SmtHandler, SmtKeyword, SmtSpecialConstant,
    parser::category::CategoryParserErrorKind,
    read::parser::{
        CategoryParserError, ParserError,
        category::{CategoryParser, expect_close_parenthesis},
    },
    token::{Token, TokenKind, TokenType},
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
    ) -> Result<ControlFlow<H::Attribute, Self>, ParserError<H>> {
        let token_span = token.span();
        match self {
            ClosedAttributeParser::Start => {
                let TokenKind::Keyword(keyword) = token.into_kind() else {
                    let kind = CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword]);
                    return Err(CategoryParserError::new(kind, token_span).into());
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
                        return match handler.handle_attribute(keyword, None) {
                            Ok(attribute) => Ok(ControlFlow::Break(attribute)),
                            Err(err) => Err(ParserError::handler_error(err, token_span)),
                        };
                    }
                    _ => {
                        let kind = CategoryParserErrorKind::ExpectedAttribute;
                        return Err(CategoryParserError::new(kind, token_span).into());
                    }
                };

                match handler.handle_attribute(keyword, Some(value)) {
                    Ok(attribute) => Ok(ControlFlow::Continue(Self::BeforeClose(attribute))),
                    Err(err) => Err(ParserError::handler_error(err, token_span)),
                }
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
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword])
            ),
            "{err:?}"
        );

        let err = assert_error::<P>(b"", 0, 0);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword])
            ),
            "{err:?}"
        );

        // a keyword is not a valid value
        let err = assert_error::<P>(b":a :b)", 3, 5);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedAttribute),
            "{err:?}"
        );

        // only one value
        let err = assert_error::<P>(b":a 1 2)", 5, 6);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );

        // EOF after the value
        let err = assert_error::<P>(b":a 1", 4, 4);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
    }
}

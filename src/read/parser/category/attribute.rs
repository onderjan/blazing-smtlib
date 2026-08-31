use std::ops::ControlFlow;

use crate::{
    SmtAttributeValue, SmtHandler, SmtKeyword,
    read::parser::{
        CategoryParserError, MultipleParser, ParserError,
        category::{CategoryParser, expect_close_paren},
        category::{CategoryParserErrorKind, handle_err, parse_special_constant},
        s_expr::SExprParser,
    },
    token::{Token, TokenKind, TokenType},
};

pub enum ClosedAttributeParser<H: SmtHandler> {
    Start,
    Name(SmtKeyword),
    SExprsValue(SmtKeyword, MultipleParser<H, SExprParser<H>>),
    BeforeClose(H::Attribute),
}

impl<H: SmtHandler> ClosedAttributeParser<H> {
    pub fn new() -> Self {
        Self::Start
    }
}

impl<H: SmtHandler> Default for ClosedAttributeParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for ClosedAttributeParser<H> {
    type Result = H::Attribute;

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
                Ok(ControlFlow::Continue(ClosedAttributeParser::Name(keyword)))
            }
            ClosedAttributeParser::Name(name) => {
                let value = match token.into_kind() {
                    TokenKind::Symbol(symbol) => SmtAttributeValue::Symbol(symbol),
                    TokenKind::ParenOpen => {
                        // starts a list of sexprs ending with closing parenthesis
                        let parser = MultipleParser::after_open_paren();
                        return Ok(ControlFlow::Continue(ClosedAttributeParser::SExprsValue(
                            name, parser,
                        )));
                    }
                    TokenKind::ParenClose => {
                        // just an attribute name, return after handling
                        return Ok(ControlFlow::Break(handle_err(
                            handler.handle_attribute(name, None),
                            token_span,
                        )?));
                    }
                    kind => {
                        if let Ok(special_constant) = parse_special_constant(kind) {
                            SmtAttributeValue::SpecialConstant(special_constant)
                        } else {
                            let kind = CategoryParserErrorKind::ExpectedAttribute;
                            return Err(CategoryParserError::new(kind, token_span).into());
                        }
                    }
                };

                match handler.handle_attribute(name, Some(value)) {
                    Ok(attribute) => Ok(ControlFlow::Continue(Self::BeforeClose(attribute))),
                    Err(err) => Err(ParserError::handler_error(err, token_span)),
                }
            }
            ClosedAttributeParser::SExprsValue(name, parser) => {
                match parser.progress(handler, token)? {
                    ControlFlow::Continue(parser) => Ok(ControlFlow::Continue(
                        ClosedAttributeParser::SExprsValue(name, parser),
                    )),
                    ControlFlow::Break(s_exprs) => {
                        // the s-expr closing parenthesis was consumed
                        // but the attribute closing parenthesis still waits to be consumed
                        let value = SmtAttributeValue::SExprs(s_exprs);
                        let attribute =
                            handle_err(handler.handle_attribute(name, Some(value)), token_span)?;
                        Ok(ControlFlow::Continue(ClosedAttributeParser::BeforeClose(
                            attribute,
                        )))
                    }
                }
            }
            ClosedAttributeParser::BeforeClose(attribute) => {
                expect_close_paren(token)?;
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

    #[test]
    fn attribute_with_s_expr_list_value() {
        assert_eq!(parse_all::<P>(b":pattern ((f x)))"), ":pattern ((f x))");
        // the empty list is a valid value
        assert_eq!(parse_all::<P>(b":a ())"), ":a ()");
        // every atom kind, including reserved words, is a valid element
        assert_eq!(
            parse_all::<P>(b":a (1 0.5 #xff #b01 \"s\" sym :kw let _ ()))"),
            ":a (1 0.5 #xff #b01 \"s\" sym :kw let _ ())"
        );
        assert_eq!(
            parse_all::<P>(b":a ((nested (deeper ())) atom))"),
            ":a ((nested (deeper ())) atom)"
        );
    }

    #[test]
    fn s_expr_list_value_stops_after_closing_paren() {
        let (attribute, left) = run::<P>(b":a (x)) y").expect("valid");
        assert_eq!(attribute, ":a (x)");
        assert_eq!(left, 1);
    }

    #[test]
    fn s_expr_list_value_errors() {
        // EOF inside the value list
        let err = assert_error::<P>(b":a (1", 5, 5);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedSExpr),
            "{err:?}"
        );

        // EOF after the value list, before the enclosing closing parenthesis
        let err = assert_error::<P>(b":a ()", 5, 5);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );

        // a second value after the list
        let err = assert_error::<P>(b":a () x)", 6, 7);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
    }
}

use std::ops::ControlFlow;

use crate::{
    SmtAttributeValue, SmtHandler, SmtKeyword,
    read::parser::{
        CategoryParserError, CloseParenParser, MultipleParser, ParserError,
        category::{
            CategoryParser, CategoryParserErrorKind, parse_special_constant, s_expr::SExprParser,
        },
        handle_err,
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
                let TokenKind::Keyword(keyword) = token.kind() else {
                    let kind = CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword]);
                    return Err(CategoryParserError::new(kind, token_span).into());
                };
                Ok(ControlFlow::Continue(ClosedAttributeParser::Name(
                    keyword.into_owned(),
                )))
            }
            ClosedAttributeParser::Name(name) => {
                let value = match token.kind() {
                    TokenKind::Symbol(symbol) => SmtAttributeValue::Symbol(symbol.into_owned()),
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
                CloseParenParser::expect(token)?;
                Ok(ControlFlow::Break(attribute))
            }
        }
    }
}

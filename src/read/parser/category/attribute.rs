use std::ops::ControlFlow;

use crate::{
    SmtAttributeValue, SmtHandler, SmtKeyword,
    read::parser::{
        CategoryParserError, CloseParenParser, ClosedMultipleParser, KeywordParser, ParserError,
        category::{
            CategoryParser, CategoryParserErrorKind, parse_special_constant, s_expr::SExprParser,
        },
        handle_err,
    },
    token::{Token, TokenKind},
};

/// A parser that reads an SMT-LIB attribute followed by a closing parenthesis.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct ClosedAttributeParser<H: SmtHandler> {
    /// Current state.
    state: State,
    /// An attribute that is only waiting for a closing parenthesis.
    ///
    /// An emplaced attribute overrides the state.
    attribute: Option<H::Attribute>,

    closed_s_exprs_parser: ClosedMultipleParser<H, SExprParser<H>>,
}

/// Attribute-parsing state.
enum State {
    /// Waiting for the keyword that will name the attribute.
    Start,
    /// Waiting for a value or a closing parenthesis.
    AfterName(SmtKeyword),
    /// Parsing S-expressions that will end with a closing parenthesis.
    InsideSExpr(SmtKeyword),
}

impl<H: SmtHandler> ClosedAttributeParser<H> {
    pub fn new() -> Self {
        Self {
            state: State::Start,
            attribute: None,
            closed_s_exprs_parser: ClosedMultipleParser::new(),
        }
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
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Attribute>, ParserError<H::Error>> {
        if let Some(attribute) = self.attribute.take() {
            // we already have an attribute, just expect closing parenthesis
            CloseParenParser::expect(token)?;
            return Ok(ControlFlow::Break(attribute));
        }

        let span = token.span();
        let mut state = State::Start;
        std::mem::swap(&mut state, &mut self.state);

        match state {
            State::Start => {
                // parse the keyword that forms the attribute name and continue
                let name = KeywordParser::expect(token)?;
                self.state = State::AfterName(name);
            }
            State::AfterName(name) => {
                let value = match token.kind() {
                    TokenKind::Symbol(symbol) => SmtAttributeValue::Symbol(symbol.into_owned()),
                    TokenKind::ParenOpen => {
                        // start a list of sexprs ending with closing parenthesis
                        self.state = State::InsideSExpr(name);
                        return Ok(ControlFlow::Continue(()));
                    }
                    TokenKind::ParenClose => {
                        // just an attribute name
                        // since we already have a closing parenthesis here, we need to immediately break
                        let result = handle_err(handler.handle_attribute(name, None), span)?;
                        // no additional reset steps necessary, as the state has already been replaced
                        // by Start and the SExpr parser is untouched
                        return Ok(ControlFlow::Break(result));
                    }
                    kind => {
                        if let Ok(special_constant) = parse_special_constant(kind) {
                            SmtAttributeValue::SpecialConstant(special_constant)
                        } else {
                            let kind = CategoryParserErrorKind::ExpectedAttribute;
                            return Err(CategoryParserError::new(kind, span).into());
                        }
                    }
                };

                // the attribute closing parenthesis was not consumed yet, we must keep the attribute for now
                let result = handle_err(handler.handle_attribute(name, Some(value)), span)?;
                // no additional reset steps necessary, as the state has already been replaced
                // by Start and the SExpr parser is untouched
                self.attribute = Some(result);
            }
            State::InsideSExpr(name) => {
                match self.closed_s_exprs_parser.progress(handler, token)? {
                    ControlFlow::Continue(()) => {
                        // put the state back
                        self.state = State::InsideSExpr(name);
                    }
                    ControlFlow::Break(s_exprs) => {
                        // the s-expr closing parenthesis was consumed,
                        // the attribute closing parenthesis was not consumed yet
                        // we must keep the attribute for now
                        let value = SmtAttributeValue::SExprs(s_exprs);
                        let attribute =
                            handle_err(handler.handle_attribute(name, Some(value)), span)?;
                        // no additional reset steps necessary, as the state has already been replaced
                        // by Start and the SExpr parser is untouched
                        self.attribute = Some(attribute);
                    }
                }
            }
        }

        Ok(ControlFlow::Continue(()))
    }
}

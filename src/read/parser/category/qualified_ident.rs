use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtQualifiedIdent,
    read::parser::{
        ClosedParser, PairParser, ParserError,
        category::{
            CategoryParser, CategoryParserError, CategoryParserErrorKind, ident::IdentParser,
            sort::SortParser,
        },
    },
    token::{Reserved, Token, TokenKind, TokenType},
};

#[derive(Clone, Copy)]
enum State {
    Start,
    /// After "(".
    Open,
    /// After "(_".
    UnqualifiedIndexed,
    /// After "(as": reads ident, then sort.
    Qualified,
}

/// A parser that reads an SMT-LIB qualified identifier.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct QualifiedIdentParser<H: SmtHandler> {
    state: State,

    ident_parser: IdentParser,
    qualified_parser: PairParser<H, IdentParser, ClosedParser<H, SortParser<H>>>,
}

impl<H: SmtHandler> QualifiedIdentParser<H> {
    pub fn new() -> Self {
        Self::new_with(State::Start)
    }

    pub fn after_open_paren() -> Self {
        Self::new_with(State::Open)
    }

    pub fn after_underscore() -> Self {
        // the ident parser must be after underscore as well
        let mut result = Self::new_with(State::UnqualifiedIndexed);
        result.ident_parser = IdentParser::after_underscore();
        result
    }

    pub fn after_as() -> Self {
        Self::new_with(State::Qualified)
    }

    fn new_with(state: State) -> Self {
        Self {
            state,
            ident_parser: IdentParser::new(),
            qualified_parser: PairParser::new(),
        }
    }
}

impl<H: SmtHandler> Default for QualifiedIdentParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for QualifiedIdentParser<H> {
    type Result = SmtQualifiedIdent<H>;

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<SmtQualifiedIdent<H>>, ParserError<H>> {
        let span = token.span();
        match self.state {
            State::Start => match token.kind() {
                TokenKind::Symbol(name) => {
                    // we are in a start state, no need to reset anything

                    // return a simple ident
                    return Ok(ControlFlow::Break(SmtQualifiedIdent::new_simple(
                        name.into_owned(),
                    )));
                }
                TokenKind::ParenOpen => self.state = State::Open,
                _ => {
                    let kind = CategoryParserErrorKind::ExpectedIdent;
                    return Err(CategoryParserError::new(kind, span).into());
                }
            },
            State::Open => {
                match token.kind() {
                    TokenKind::Reserved(Reserved::Underscore) => {
                        // unqualified indexed ident
                        // move the ident parser after underscore
                        self.ident_parser = IdentParser::after_underscore();
                        self.state = State::UnqualifiedIndexed;
                    }
                    TokenKind::Reserved(Reserved::As) => {
                        // qualified ident, parse identifier next
                        self.ident_parser = IdentParser::new();
                        self.state = State::Qualified;
                    }
                    _ => {
                        let kind = CategoryParserErrorKind::ExpectedToken(&[
                            TokenType::Reserved(Reserved::Underscore),
                            TokenType::Reserved(Reserved::As),
                        ]);
                        return Err(CategoryParserError::new(kind, span).into());
                    }
                }
            }
            State::UnqualifiedIndexed => {
                if let ControlFlow::Break(ident) = self.ident_parser.progress(handler, token)? {
                    // the closing parenthesis was already consumed by the IdentParser

                    // we only need to reset the state:
                    // the ident parser was reset, the qualified parser is untouched
                    self.state = State::Start;

                    // return an unqualified but indexed ident
                    return Ok(ControlFlow::Break(SmtQualifiedIdent::new_unqualified(
                        ident,
                    )));
                }
            }

            State::Qualified => {
                if let ControlFlow::Break((ident, sort)) =
                    self.qualified_parser.progress(handler, token)?
                {
                    // we only need to reset the state:
                    // the ident parser is untouched, the qualified parser was reset
                    self.state = State::Start;

                    // return an unqualified but indexed ident
                    return Ok(ControlFlow::Break(SmtQualifiedIdent::new_qualified(
                        ident, sort,
                    )));
                }
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

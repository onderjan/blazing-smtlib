use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIdent, SmtIndex, SmtSymbol,
    read::parser::{
        ParserError,
        category::{CategoryErrorKind, CategoryParser},
    },
    token::{Reserved, Token, TokenKind, TokenType},
};

/// A parser that reads an SMT-LIB identifier.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct IdentParser {
    state: State,
    name: Option<SmtSymbol>,
    indices: Vec<SmtIndex>,
}

/// Identifier-parsing state.
#[derive(Clone, Copy)]
enum State {
    /// Waiting for a token.
    Start,
    /// After "(", expecting underscore.
    Open,
    /// Reading name and indices.
    AfterUnderscore,
}

impl IdentParser {
    pub fn new() -> Self {
        Self {
            state: State::Start,
            name: None,
            indices: Vec::new(),
        }
    }

    pub fn move_after_open_paren(&mut self) {
        self.state = State::Open;
    }

    pub fn move_after_underscore(&mut self) {
        self.state = State::AfterUnderscore;
    }

    pub fn restart(&mut self) {
        self.state = State::Start;
        self.name = None;
        self.indices.clear();
    }
}

impl Default for IdentParser {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for IdentParser {
    type Result = SmtIdent;

    #[inline]
    fn restart(&mut self) {
        // call the inherent implementation
        // it exists to avoid needing to specify <H>
        self.restart();
    }

    #[inline]
    fn progress(
        &mut self,
        _handler: &mut H,
        token: &Token,
    ) -> Result<ControlFlow<SmtIdent, ()>, ParserError<H::Error>> {
        let span = token.span();

        match self.state {
            State::Start => match token.kind() {
                TokenKind::Symbol(name) => {
                    return Ok(ControlFlow::Break(SmtIdent::new_simple(name.into_owned())));
                }
                TokenKind::ParenOpen => {
                    self.state = State::Open;
                }
                _ => {
                    let kind = CategoryErrorKind::ExpectedIdent;
                    return Err(ParserError::category_error(kind, span));
                }
            },
            State::Open => {
                // this must be an underscore
                if matches!(token.kind(), TokenKind::Reserved(Reserved::Underscore)) {
                    self.state = State::AfterUnderscore;
                } else {
                    let kind = CategoryErrorKind::ExpectedToken(&[TokenType::Reserved(
                        Reserved::Underscore,
                    )]);
                    return Err(ParserError::category_error(kind, span));
                }
            }
            State::AfterUnderscore => {
                let name = match self.name.take() {
                    None => {
                        // we need to read the name
                        if let TokenKind::Symbol(name) = token.kind() {
                            Some(name.into_owned())
                        } else {
                            let kind = CategoryErrorKind::ExpectedToken(&[TokenType::Symbol]);
                            return Err(ParserError::category_error(kind, span));
                        }
                    }
                    Some(name) => {
                        // we have already read the name, so we will be reading an index
                        // and ending with closing parenthesis
                        match token.kind() {
                            TokenKind::ParenClose => {
                                if self.indices.is_empty() {
                                    let kind = CategoryErrorKind::EmptyIdentIndices;
                                    return Err(ParserError::category_error(kind, span));
                                }
                                let indices = self.indices.drain(..).collect();
                                // reset to the starting state: both our name and indices are now empty
                                self.state = State::Start;
                                return Ok(ControlFlow::Break(SmtIdent { name, indices }));
                            }
                            TokenKind::Numeral(index_value) => {
                                self.indices
                                    .push(SmtIndex::Numeral(index_value.into_owned()));
                            }
                            TokenKind::Symbol(index_symbol) => {
                                self.indices
                                    .push(SmtIndex::Symbol(index_symbol.into_owned()));
                            }
                            _ => {
                                let kind = CategoryErrorKind::ExpectedIndexOrCloseParen;
                                return Err(ParserError::category_error(kind, span));
                            }
                        }
                        // put the name back
                        Some(name)
                    }
                };
                self.name = name;
            }
        }

        Ok(ControlFlow::Continue(()))
    }
}

use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIdent, SmtIndex, SmtSymbol,
    read::parser::{
        ParserError, ParserResources,
        category::{CategoryErrorKind, CategoryParser},
    },
    token::{Reserved, Token, TokenKind, TokenType},
};

/// A parser that reads an SMT-LIB identifier.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct IdentParser {
    _priv: (),
}

impl IdentParser {
    pub fn new() -> Self {
        Self { _priv: () }
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
    fn progress(
        &mut self,
        _handler: &mut H,
        resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<ControlFlow<SmtIdent, ()>, ParserError<H::Error>> {
        // progress the slot
        resources.ident_slot.progress(token)
    }
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

pub(crate) struct IdentSlot {
    state: State,
    name: Option<SmtSymbol>,
    indices: Vec<SmtIndex>,
}

impl IdentSlot {
    pub(crate) fn new() -> Self {
        Self {
            state: State::Start,
            name: None,
            indices: Vec::new(),
        }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        matches!(self.state, State::Start) && self.name.is_none() && self.indices.is_empty()
    }

    pub(crate) fn clear(&mut self) {
        self.state = State::Start;
        self.name = None;
        self.indices.clear();
    }

    pub(crate) fn move_after_open_paren(&mut self) {
        debug_assert!(
            self.is_pristine(),
            "must be pristine to move after open paren"
        );
        self.state = State::Open;
    }

    pub(crate) fn move_after_underscore(&mut self) {
        debug_assert!(
            self.is_pristine(),
            "must be pristine to move after underscore"
        );
        self.state = State::AfterUnderscore;
    }

    #[inline]
    pub(crate) fn progress<E>(
        &mut self,
        token: &Token,
    ) -> Result<ControlFlow<SmtIdent, ()>, ParserError<E>> {
        let span = token.span();

        match self.state {
            State::Start => {
                debug_assert!(self.is_pristine(), "must be pristine when starting");
                match token.kind() {
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
                }
            }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckStandardSyntax, read::parser::category::tests::parse_all_with};

    fn index_texts(ident: &SmtIdent) -> Vec<String> {
        ident
            .indices
            .iter()
            .map(|index| match index {
                SmtIndex::Numeral(n) => String::from_utf8(n.as_slice().to_vec()).unwrap(),
                SmtIndex::Symbol(s) => {
                    format!("'{}", String::from_utf8(s.as_slice().to_vec()).unwrap())
                }
            })
            .collect()
    }

    #[test]
    fn continuations_after_open_paren_and_underscore() {
        // the callers that already consumed `(` or `( _` enter the slot in the
        // corresponding state, so the parser accepts the rest of the indexed
        // identifier and leaves the slot pristine
        let mut resources = ParserResources::new();
        resources.ident_slot.move_after_open_paren();
        let ident = parse_all_with(IdentParser::new(), &mut resources, b"_ f 1)");
        assert_eq!(ident.name.as_slice(), b"f");
        assert_eq!(index_texts(&ident), ["1"]);
        assert!(resources.are_pristine());

        let mut resources = ParserResources::new();
        resources.ident_slot.move_after_underscore();
        let ident = parse_all_with(IdentParser::new(), &mut resources, b"f 1)");
        assert_eq!(ident.name.as_slice(), b"f");
        assert_eq!(index_texts(&ident), ["1"]);
        assert!(resources.are_pristine());
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "must be pristine")]
    fn entering_a_busy_slot_is_rejected() {
        // an entry point may only be used on a pristine slot
        let mut resources = ParserResources::<CheckStandardSyntax>::new();
        resources.ident_slot.move_after_underscore();
        resources.ident_slot.move_after_open_paren();
    }
}

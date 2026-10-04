use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIdent, SmtSymbolView,
    read::parser::{
        Arena, IdentHandle, IndexHandle, SmtParse, SmtParseError, SmtParseState,
        SmtSyntaxErrorKind, TextHandle, parse_by_token,
    },
    token::{
        SmtBatchCursor, SmtGeneralReserved, SmtReserved, SmtSyntaxToken, SmtToken, SmtVersion,
    },
};

/// A parser that reads an SMT-LIB identifier.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct SmtIdentParser {
    _priv: (),
}

impl SmtIdentParser {
    pub fn new() -> Self {
        Self { _priv: () }
    }
}

impl Default for SmtIdentParser {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> SmtParse<H> for SmtIdentParser {
    type Result = SmtIdent;

    #[inline]
    fn parse(
        &mut self,
        _handler: &mut H,
        resources: &mut SmtParseState<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<SmtIdent, ()>, SmtParseError<H::Error>> {
        // progress the slot over the arena, returning an owned identifier
        let SmtParseState {
            ident_slot, arena, ..
        } = resources;
        parse_by_token(cursor, |version, token| {
            match ident_slot.progress(arena, version, token)? {
                ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
                ControlFlow::Break(ident) => Ok(ControlFlow::Break(
                    arena.hand_over_ident(ident, |ident| ident.into_owned()),
                )),
            }
        })
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
    /// The name, stored in the arena text while the indices are read.
    name: Option<TextHandle>,
    /// Where the indices of the currently-read identifier start in the arena.
    arena_indices_start: usize,
}

impl IdentSlot {
    pub(crate) fn new() -> Self {
        Self {
            state: State::Start,
            name: None,
            arena_indices_start: 0,
        }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        matches!(self.state, State::Start) && self.name.is_none()
    }

    pub(crate) fn clear(&mut self) {
        self.state = State::Start;
        self.name = None;
    }

    pub(crate) fn move_after_open_paren(&mut self) {
        debug_assert!(
            self.is_pristine(),
            "must be pristine to move after open paren"
        );
        self.state = State::Open;
    }

    /// Moves after the name of an indexed identifier, "(_ name": the name goes to the
    /// arena and the indices follow.
    pub(crate) fn move_after_indexed_name<H: SmtHandler + ?Sized>(
        &mut self,
        arena: &mut Arena<H>,
        name: SmtSymbolView,
    ) {
        debug_assert!(
            self.is_pristine(),
            "must be pristine to move after an indexed name"
        );
        self.state = State::AfterUnderscore;
        self.name = Some(self.push_name(arena, name));
    }

    /// Puts the name of an indexed identifier into the arena text; its indices will
    /// follow in the arena from here.
    fn push_name<H: SmtHandler + ?Sized>(
        &mut self,
        arena: &mut Arena<H>,
        name: SmtSymbolView,
    ) -> TextHandle {
        self.arena_indices_start = arena.indices.len();
        arena.push_text(name.as_slice())
    }

    pub(crate) fn move_after_underscore(&mut self) {
        debug_assert!(
            self.is_pristine(),
            "must be pristine to move after underscore"
        );
        self.state = State::AfterUnderscore;
    }

    #[inline]
    pub(crate) fn progress<H: SmtHandler + ?Sized, E>(
        &mut self,
        arena: &mut Arena<H>,
        version: SmtVersion,
        token: SmtToken,
    ) -> Result<ControlFlow<IdentHandle, ()>, SmtParseError<E>> {
        let span = token.span();

        match self.state {
            State::Start => {
                debug_assert!(self.is_pristine(), "must be pristine when starting");
                match token.syntax(version) {
                    SmtSyntaxToken::Symbol(name) => {
                        // a simple identifier
                        return Ok(ControlFlow::Break(arena.push_nonindexed_ident(name)));
                    }
                    SmtSyntaxToken::ParenOpen => {
                        self.state = State::Open;
                    }
                    _ => {
                        let kind = SmtSyntaxErrorKind::ExpectedIdent;
                        return Err(SmtParseError::category_error(kind, span));
                    }
                }
            }
            State::Open => {
                // this must be an underscore
                if matches!(
                    token.syntax(version),
                    SmtSyntaxToken::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore))
                ) {
                    self.state = State::AfterUnderscore;
                } else {
                    return Err(SmtParseError::category_error(
                        SmtSyntaxErrorKind::ExpectedUnderscore,
                        span,
                    ));
                }
            }
            State::AfterUnderscore => {
                let name = match self.name.take() {
                    None => {
                        // we need to read the name, its indices will follow in the arena
                        if let SmtSyntaxToken::Symbol(name) = token.syntax(version) {
                            Some(self.push_name(arena, name))
                        } else {
                            return Err(SmtParseError::category_error(
                                SmtSyntaxErrorKind::ExpectedSymbol,
                                span,
                            ));
                        }
                    }
                    Some(name) => {
                        // we have already read the name, so we will be reading an index
                        // and ending with closing parenthesis
                        match token.syntax(version) {
                            SmtSyntaxToken::ParenClose => {
                                let indices_start = self.arena_indices_start;
                                if arena.indices.len() == indices_start {
                                    let kind = SmtSyntaxErrorKind::EmptyIdentIndices;
                                    return Err(SmtParseError::category_error(kind, span));
                                }
                                // reset to the starting state
                                // we already took the name
                                // the identifier is in the arena
                                self.state = State::Start;
                                return Ok(ControlFlow::Break(IdentHandle {
                                    name,
                                    indices_start,
                                }));
                            }
                            SmtSyntaxToken::Numeral(index_value) => {
                                let index = arena.push_text(index_value.as_slice());
                                arena.indices.push(IndexHandle::Numeral(index));
                            }
                            // symbol index is only allowed since SMT-LIB 2.5,
                            // otherwise the fallback is taken
                            SmtSyntaxToken::Symbol(index_symbol) if version >= SmtVersion::V2_5 => {
                                let index = arena.push_text(index_symbol.as_slice());
                                arena.indices.push(IndexHandle::Symbol(index));
                            }
                            _ => {
                                return Err(SmtParseError::category_error(
                                    SmtSyntaxErrorKind::ExpectedIndexOrCloseParen,
                                    span,
                                ));
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
    use crate::{SmtIndex, SmtSyntaxChecker, read::parser::category::tests::parse_all_with};

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
        let mut resources = SmtParseState::new();
        resources.ident_slot.move_after_open_paren();
        let ident = parse_all_with(SmtIdentParser::new(), &mut resources, b"_ f 1)");
        assert_eq!(ident.name.as_slice(), b"f");
        assert_eq!(index_texts(&ident), ["1"]);
        assert!(resources.are_pristine());

        let mut resources = SmtParseState::new();
        resources.ident_slot.move_after_underscore();
        let ident = parse_all_with(SmtIdentParser::new(), &mut resources, b"f 1)");
        assert_eq!(ident.name.as_slice(), b"f");
        assert_eq!(index_texts(&ident), ["1"]);
        assert!(resources.are_pristine());
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "must be pristine")]
    fn entering_a_busy_slot_is_rejected() {
        // an entry point may only be used on a pristine slot
        let mut resources = SmtParseState::<SmtSyntaxChecker>::new();
        resources.ident_slot.move_after_underscore();
        resources.ident_slot.move_after_open_paren();
    }
}

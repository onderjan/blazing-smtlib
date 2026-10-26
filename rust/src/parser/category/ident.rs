use std::{fmt, ops::ControlFlow};

use crate::{
    SmtHandler, SmtVersion,
    grammar::SmtIdentBuf,
    lexicon::SmtSymbol,
    parser::{
        Arena, IdentHandle, IndexHandle, SmtNonEmptyList, SmtParse, SmtParseError, SmtParseState,
        SmtSyntaxErrorKind, SmtSyntaxExpected, SymbolHandle, expected, parse_by_token,
    },
    token::{SmtCursor, SmtGeneralReserved, SmtReserved, SmtToken},
};

/// Parses an identifier.
pub struct SmtIdentParser {
    _priv: (),
}

impl fmt::Debug for SmtIdentParser {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SmtIdentParser").finish_non_exhaustive()
    }
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
    type Result = SmtIdentBuf;

    #[inline]
    fn parse<Z: SmtCursor>(
        &mut self,
        _handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<SmtIdentBuf, ()>, SmtParseError<H::Error>> {
        // progress the slot over the arena, returning an owned identifier
        let SmtParseState {
            ident_slot, arena, ..
        } = parse_state;
        parse_by_token(cursor, |cursor, token| {
            match ident_slot.progress(arena, cursor, token)? {
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
    name: Option<SymbolHandle>,
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
        name: SmtSymbol,
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
        name: SmtSymbol,
    ) -> SymbolHandle {
        self.arena_indices_start = arena.indices.len();
        arena.push_symbol(name)
    }

    pub(crate) fn move_after_underscore(&mut self) {
        debug_assert!(
            self.is_pristine(),
            "must be pristine to move after underscore"
        );
        self.state = State::AfterUnderscore;
    }

    #[inline]
    pub(crate) fn progress<H: SmtHandler + ?Sized, Z: SmtCursor, E>(
        &mut self,
        arena: &mut Arena<H>,
        cursor: &Z,
        token: Z::Token,
    ) -> Result<ControlFlow<IdentHandle, ()>, SmtParseError<E>> {
        match self.state {
            State::Start => {
                debug_assert!(self.is_pristine(), "must be pristine when starting");
                match cursor.syntax(&token) {
                    SmtToken::Symbol(name) => {
                        // a simple identifier
                        return Ok(ControlFlow::Break(arena.push_nonindexed_ident(name)));
                    }
                    SmtToken::ParenOpen => {
                        self.state = State::Open;
                    }
                    _ => {
                        let kind = SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Ident]);
                        return Err(SmtParseError::syntax(kind));
                    }
                }
            }
            State::Open => {
                // this must be an underscore
                if matches!(
                    cursor.syntax(&token),
                    SmtToken::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore))
                ) {
                    self.state = State::AfterUnderscore;
                } else {
                    return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Expected(&[
                        expected::UNDERSCORE,
                    ])));
                }
            }
            State::AfterUnderscore => {
                let name = match self.name.take() {
                    None => {
                        // we need to read the name, its indices will follow in the arena
                        if let SmtToken::Symbol(name) = cursor.syntax(&token) {
                            Some(self.push_name(arena, name))
                        } else {
                            return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Expected(&[
                                SmtSyntaxExpected::Symbol,
                            ])));
                        }
                    }
                    Some(name) => {
                        // we have already read the name, so we will be reading an index
                        // and ending with closing parenthesis
                        match cursor.syntax(&token) {
                            SmtToken::ParenClose => {
                                let indices_start = self.arena_indices_start;
                                if arena.indices.len() == indices_start {
                                    let kind =
                                        SmtSyntaxErrorKind::Empty(SmtNonEmptyList::IdentIndices);
                                    return Err(SmtParseError::syntax(kind));
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
                            SmtToken::Numeral(index_value) => {
                                let index = arena.push_text(index_value.as_slice());
                                arena.indices.push(IndexHandle::Numeral(index));
                            }
                            // symbol index is only allowed since SMT-LIB 2.5,
                            // otherwise the fallback is taken
                            SmtToken::Symbol(index_symbol)
                                if cursor.version() >= SmtVersion::V2_5 =>
                            {
                                let index = arena.push_symbol(index_symbol);
                                arena.indices.push(IndexHandle::Symbol(index));
                            }
                            _ => {
                                return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Expected(
                                    &[SmtSyntaxExpected::Index, expected::PAREN_CLOSE],
                                )));
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
    use crate::{SmtSyntaxChecker, grammar::SmtIndex, parser::category::tests::parse_all_with};

    fn index_texts(ident: &SmtIdentBuf) -> Vec<String> {
        ident
            .indices
            .view()
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
        let mut parse_state = SmtParseState::new();
        parse_state.ident_slot.move_after_open_paren();
        let ident = parse_all_with(SmtIdentParser::new(), &mut parse_state, b"_ f 1)");
        assert_eq!(ident.name.as_slice(), b"f");
        assert_eq!(index_texts(&ident), ["1"]);
        assert!(parse_state.is_pristine());

        let mut parse_state = SmtParseState::new();
        parse_state.ident_slot.move_after_underscore();
        let ident = parse_all_with(SmtIdentParser::new(), &mut parse_state, b"f 1)");
        assert_eq!(ident.name.as_slice(), b"f");
        assert_eq!(index_texts(&ident), ["1"]);
        assert!(parse_state.is_pristine());
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "must be pristine")]
    fn entering_a_busy_slot_is_rejected() {
        // an entry point may only be used on a pristine slot
        let mut parse_state = SmtParseState::<SmtSyntaxChecker>::new();
        parse_state.ident_slot.move_after_underscore();
        parse_state.ident_slot.move_after_open_paren();
    }
}

use std::ops::ControlFlow;

use crate::{
    SmtHandler,
    read::parser::{
        Arena, IdentHandle, IdentSlot, Parser, ParserError, ParserResources, SyntaxErrorKind,
        handle_err, parse_by_token,
    },
    token::{SmtGeneralReserved, SmtReserved, SmtSyntaxToken, SmtToken, SmtVersion, TokenCursor},
};

/// A parser that reads an SMT-LIB sort.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct SortParser<H: SmtHandler> {
    _priv: std::marker::PhantomData<H>,
}

impl<H: SmtHandler> SortParser<H> {
    pub fn new() -> Self {
        Self {
            _priv: std::marker::PhantomData,
        }
    }
}

impl<H: SmtHandler> Default for SortParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> Parser<H> for SortParser<H> {
    type Result = H::Sort;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut TokenCursor,
    ) -> Result<ControlFlow<H::Sort>, ParserError<H::Error>> {
        // progress the slot, giving it the ident slot it delegates to
        let ParserResources {
            ident_slot,
            sort_slot,
            arena,
            ..
        } = resources;
        parse_by_token(cursor, |version, token| {
            sort_slot.progress(handler, arena, ident_slot, version, token)
        })
    }
}

/// Current sort parser state.
enum State {
    /// Waiting for the sort to start.
    Start,
    /// After reading "(".
    Open,
    /// The sort consists of only an identifier.
    ///
    /// Parsing delegates to the identifier parser.
    IdentOnly,
    /// The sort starts with an identifier.
    ///
    /// Parsing delegates to the identifier parser.
    /// After that, the sort will be pushed as a new level.
    StartingIdent,
}

/// A parsed-sort level.
///
/// Sorts here are waiting for a next applied sort
/// or a closing parenthesis.
struct Level {
    /// The identifier, stored in the arena.
    ident: IdentHandle,
    /// The applied sorts are stored in the arena starting at this position.
    arena_applied_start: usize,
}

pub(crate) struct SortSlot<H: SmtHandler + ?Sized> {
    state: State,
    levels: Vec<Level>,
    _priv: std::marker::PhantomData<H>,
}

impl<H: SmtHandler + ?Sized> SortSlot<H> {
    pub(crate) fn new() -> Self {
        Self {
            state: State::Start,
            levels: Vec::new(),
            _priv: std::marker::PhantomData,
        }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        matches!(self.state, State::Start) && self.levels.is_empty()
    }

    pub(crate) fn clear(&mut self) {
        self.state = State::Start;
        self.levels.clear();
    }

    #[inline]
    pub(crate) fn progress(
        &mut self,
        handler: &mut H,
        arena: &mut Arena<H>,
        ident_slot: &mut IdentSlot,
        version: SmtVersion,
        token: SmtToken,
    ) -> Result<ControlFlow<H::Sort>, ParserError<H::Error>> {
        let span = token.span();
        let flow = match self.state {
            State::Start => {
                // the start state is also reached between applied sorts, so only
                // an empty level stack means the category is being entered
                if self.levels.is_empty() {
                    debug_assert!(self.is_pristine(), "must be pristine when starting");
                }
                match token.syntax(version) {
                    SmtSyntaxToken::Symbol(name) => {
                        // the sort consists just of a single-symbol ident
                        let name = arena.push_text(name.as_slice());
                        let ident = IdentHandle {
                            name,
                            indices_start: arena.indices.len(),
                        };
                        ControlFlow::Break((ident, arena.sorts.len()))
                    }
                    SmtSyntaxToken::ParenOpen => {
                        // move the state to open
                        self.state = State::Open;
                        ControlFlow::Continue(())
                    }
                    SmtSyntaxToken::ParenClose => {
                        match self.levels.pop() {
                            Some(last_level) => {
                                // close the last level
                                // if the sort committed to having applications,
                                // there must be at least one of them
                                if arena.sorts.len() == last_level.arena_applied_start {
                                    return Err(ParserError::category_error(
                                        SyntaxErrorKind::EmptySortApplication,
                                        span,
                                    ));
                                }
                                ControlFlow::Break((
                                    last_level.ident,
                                    last_level.arena_applied_start,
                                ))
                            }
                            None => {
                                // we just received ")"
                                return Err(ParserError::category_error(
                                    SyntaxErrorKind::ExpectedSort,
                                    span,
                                ));
                            }
                        }
                    }
                    _ => {
                        return Err(ParserError::category_error(
                            SyntaxErrorKind::ExpectedSort,
                            span,
                        ));
                    }
                }
            }
            State::Open => {
                // decide how to continue
                let state = match token.syntax(version) {
                    SmtSyntaxToken::Reserved(SmtReserved::General(
                        SmtGeneralReserved::Underscore,
                    )) => {
                        // this is a sort consisting just of an indexed identifier
                        // move the ident slot after underscore
                        ident_slot.move_after_underscore();
                        State::IdentOnly
                    }
                    SmtSyntaxToken::Symbol(name) => {
                        // non-indexed ident starting sort
                        let name = arena.push_text(name.as_slice());
                        let ident = IdentHandle {
                            name,
                            indices_start: arena.indices.len(),
                        };
                        self.levels.push(Level {
                            ident,
                            arena_applied_start: arena.sorts.len(),
                        });
                        State::Start
                    }
                    SmtSyntaxToken::ParenOpen => {
                        // indexed ident starting sort
                        // move the ident slot after opening parenthesis
                        ident_slot.move_after_open_paren();
                        State::StartingIdent
                    }
                    _ => {
                        return Err(ParserError::category_error(
                            SyntaxErrorKind::ExpectedSortInner,
                            span,
                        ));
                    }
                };
                self.state = state;
                ControlFlow::Continue(())
            }
            State::IdentOnly => ident_slot
                .progress(arena, version, token)?
                .map_break(|ident| (ident, arena.sorts.len())),
            State::StartingIdent => {
                match ident_slot.progress(arena, version, token)? {
                    ControlFlow::Continue(()) => ControlFlow::Continue(()),
                    ControlFlow::Break(ident) => {
                        // add a new level and start parsing the new sort
                        self.levels.push(Level {
                            ident,
                            arena_applied_start: arena.sorts.len(),
                        });
                        self.state = State::Start;
                        ControlFlow::Continue(())
                    }
                }
            }
        };

        let ControlFlow::Break((ident, arena_applied_start)) = flow else {
            return Ok(ControlFlow::Continue(()));
        };

        // we have parsed a sort, reset the state and hand the sort over
        self.state = State::Start;
        let sort = arena.hand_over_sort(ident, arena_applied_start, |sort| {
            handle_err(handler.handle_sort(sort), span)
        })?;

        if !self.levels.is_empty() {
            // we need to append to the applied sorts
            // this will implicitly belong to the last level
            arena.sorts.push(sort);
            Ok(ControlFlow::Continue(()))
        } else {
            // this is the root level, we are done
            Ok(ControlFlow::Break(sort))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckStandardSyntax, read::parser::category::tests::parse_all_with};

    #[test]
    fn slots_are_pristine_after_every_sort() {
        // nested applied sorts and indexed identifiers use the sort and
        // ident slots; both must be back in their initial state afterwards
        for input in [
            &b"Bool"[..],
            b"(_ BitVec 8)",
            b"(Array (_ BitVec 8) Int)",
            b"((_ Tuple 2) (_ BitVec 8) (Set Int))",
        ] {
            let mut resources = ParserResources::new();
            parse_all_with(
                SortParser::<CheckStandardSyntax>::new(),
                &mut resources,
                input,
            );
            assert!(resources.are_pristine(), "after {input:?}");
        }
    }
}

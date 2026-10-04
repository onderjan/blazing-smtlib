use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtQualifiedIdent, SmtSymbolView,
    read::parser::{
        Arena, CloseParenParser, IdentHandle, IdentSlot, Parser, ParserResources,
        QualifiedIdentHandle, SmtParseError, SmtSyntaxErrorKind, SortSlot, parse_by_token,
    },
    token::{
        SmtBatchCursor, SmtGeneralReserved, SmtReserved, SmtSyntaxToken, SmtToken, SmtVersion,
    },
};

/// A parser that reads an SMT-LIB qualified identifier.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct QualifiedIdentParser<H: SmtHandler> {
    _priv: std::marker::PhantomData<H>,
}

impl<H: SmtHandler> QualifiedIdentParser<H> {
    pub fn new() -> Self {
        Self {
            _priv: std::marker::PhantomData,
        }
    }
}

impl<H: SmtHandler> Default for QualifiedIdentParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> Parser<H> for QualifiedIdentParser<H> {
    type Result = SmtQualifiedIdent<H>;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<SmtQualifiedIdent<H>>, SmtParseError<H::Error>> {
        // progress the slot, giving it the ident and sort slots it delegates to
        let ParserResources {
            ident_slot,
            sort_slot,
            qualified_ident_slot,
            arena,
            ..
        } = resources;
        parse_by_token(cursor, |version, token| {
            match qualified_ident_slot
                .progress(handler, arena, sort_slot, ident_slot, version, token)?
            {
                ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
                ControlFlow::Break(qualified_ident) => Ok(ControlFlow::Break(
                    arena.hand_over_qualified_ident(qualified_ident, |view| view.into_owned()),
                )),
            }
        })
    }
}

/// Qualified-identifier-parsing state.
///
/// This only matters if not storing anything yet.
#[derive(Clone, Copy)]
enum State {
    /// Waiting for a symbol or "(".
    Start,
    /// After "(".
    Open,
    /// After "(_": reading the indexed identifier.
    ///
    /// Parsing delegates to the identifier parser.
    UnqualifiedIndexed,
    /// After "(as": reading the identifier.
    ///
    /// Parsing delegates to the identifier parser.
    QualifiedIdent,
}

pub(crate) struct QualifiedIdentSlot<H: SmtHandler + ?Sized> {
    state: State,
    /// The identifier of "(as", stored while its sort is being parsed.
    ident: Option<IdentHandle>,
    /// The qualified identifier, stored while waiting for ")".
    qualified_ident: Option<QualifiedIdentHandle<H>>,
}

impl<H: SmtHandler + ?Sized> QualifiedIdentSlot<H> {
    pub(crate) fn new() -> Self {
        Self {
            state: State::Start,
            ident: None,
            qualified_ident: None,
        }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        matches!(self.state, State::Start) && self.ident.is_none() && self.qualified_ident.is_none()
    }

    pub(crate) fn clear(&mut self) {
        self.state = State::Start;
        self.ident = None;
        self.qualified_ident = None;
    }

    pub(crate) fn move_after_open_paren(&mut self) {
        debug_assert!(self.is_pristine(), "must be pristine when moving after (");
        self.state = State::Open;
    }

    pub(crate) fn move_after_underscore(&mut self, ident_slot: &mut IdentSlot) {
        debug_assert!(self.is_pristine(), "must be pristine when moving after (_");
        // the ident slot must be after underscore as well
        ident_slot.move_after_underscore();
        self.state = State::UnqualifiedIndexed;
    }

    /// Moves after "(_ name" of an unqualified indexed identifier: the name goes to
    /// the arena and the indices follow.
    pub(crate) fn move_after_indexed_name(
        &mut self,
        ident_slot: &mut IdentSlot,
        arena: &mut Arena<H>,
        name: SmtSymbolView,
    ) {
        debug_assert!(
            self.is_pristine(),
            "must be pristine when moving after (_ name"
        );
        ident_slot.move_after_indexed_name(arena, name);
        self.state = State::UnqualifiedIndexed;
    }

    pub(crate) fn move_after_as(&mut self) {
        debug_assert!(self.is_pristine(), "must be pristine when moving after (as");
        self.state = State::QualifiedIdent;
    }

    #[inline]
    pub(crate) fn progress(
        &mut self,
        handler: &mut H,
        arena: &mut Arena<H>,
        sort_slot: &mut SortSlot<H>,
        ident_slot: &mut IdentSlot,
        version: SmtVersion,
        token: SmtToken,
    ) -> Result<ControlFlow<QualifiedIdentHandle<H>>, SmtParseError<H::Error>> {
        // The sequential progress is as follows:
        // 1. Start, expecting one of:
        //    - a symbol, immediately break with a simple identifier
        //    - "(", move to (2).
        // 2. Open, "_" starts an unqualified indexed identifier (3),
        //    "as" starts a qualified identifier (4).
        // 3. UnqualifiedIndexed, parsing the unqualified indexed identifier.
        //    After it is parsed (which consumes the closing ")"),
        //    break with the unqualified identifier.
        // 4. QualifiedIdent, parsing the identifier of the qualified identifier.
        //    After it is parsed, move to (5) by storing it.
        // 5. The identifier has been stored, we are parsing its sort.
        //    After it is parsed, move to (6) by storing
        //    the identifier qualified by its sort.
        // 6. Qualified identifier has been stored,
        //    we are expecting a closing parenthesis before we break.
        //
        // The implementation tries to take stored identifiers first
        // so that nothing is taken and put back unnecessarily.

        let span = token.span();

        if let Some(qualified_ident) = self.qualified_ident.take() {
            // step 6: after the sort, waiting for ")"
            CloseParenParser::expect(token)?;
            // the slot is back in its initial state
            return Ok(ControlFlow::Break(qualified_ident));
        }

        if let Some(ident) = self.ident.take() {
            // step 5: after the identifier of "(as", parsing the sort
            match sort_slot.progress(handler, arena, ident_slot, version, token)? {
                ControlFlow::Continue(()) => self.ident = Some(ident),
                ControlFlow::Break(sort) => {
                    self.qualified_ident = Some(QualifiedIdentHandle {
                        ident,
                        sort: Some(sort),
                    })
                }
            }
            return Ok(ControlFlow::Continue(()));
        }

        match self.state {
            // step 1: expecting a symbol or an opening parenthesis
            State::Start => {
                debug_assert!(self.is_pristine(), "must be pristine when starting");
                match token.syntax(version) {
                    SmtSyntaxToken::Symbol(name) => {
                        // return a simple ident, the slot is in its initial state
                        return Ok(ControlFlow::Break(QualifiedIdentHandle::unqualified(
                            arena.push_nonindexed_ident(name),
                        )));
                    }
                    SmtSyntaxToken::ParenOpen => self.state = State::Open,
                    _ => {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::ExpectedIdent,
                            span,
                        ));
                    }
                }
            }
            // step 2: expecting an underscore or 'as'
            State::Open => match token.syntax(version) {
                SmtSyntaxToken::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore)) => {
                    // unqualified indexed ident
                    // move the ident slot after underscore
                    ident_slot.move_after_underscore();
                    self.state = State::UnqualifiedIndexed;
                }
                SmtSyntaxToken::Reserved(SmtReserved::General(SmtGeneralReserved::As)) => {
                    // qualified ident, parse identifier next
                    self.state = State::QualifiedIdent;
                }
                _ => {
                    return Err(SmtParseError::category_error(
                        SmtSyntaxErrorKind::ExpectedUnderscoreOrAs,
                        span,
                    ));
                }
            },
            // step 3: parsing an unqualified indexed identifier
            State::UnqualifiedIndexed => {
                if let ControlFlow::Break(ident) = ident_slot.progress(arena, version, token)? {
                    // the closing parenthesis was already consumed by the ident slot
                    // reset and return an unqualified but indexed ident
                    self.state = State::Start;
                    return Ok(ControlFlow::Break(QualifiedIdentHandle::unqualified(ident)));
                }
            }
            // step 4: parsing the identifier of a qualified identifier
            State::QualifiedIdent => {
                if let ControlFlow::Break(ident) = ident_slot.progress(arena, version, token)? {
                    // store the identifier
                    // this moves us to step 5 where its sort is parsed next
                    self.ident = Some(ident);
                    self.state = State::Start;
                }
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{SmtSyntaxChecker, read::parser::category::tests::parse_all_with};

    #[test]
    fn entry_points() {
        // the callers that already consumed `(`, `( _` or `( as` enter the
        // slot in the corresponding state, so the parser accepts the rest of
        // the qualified identifier and leaves the slots pristine
        let mut resources = ParserResources::new();
        resources.qualified_ident_slot.move_after_open_paren();
        let qi = parse_all_with(
            QualifiedIdentParser::<SmtSyntaxChecker>::new(),
            &mut resources,
            b"_ f 1)",
        );
        assert_eq!(qi.ident.name.as_slice(), b"f");
        assert_eq!(qi.ident.indices.len(), 1);
        assert!(qi.sort.is_none());
        assert!(resources.are_pristine());

        // regression: the entry point must put the ident slot after the
        // underscore as well, or `f` alone would finish the identifier
        let mut resources = ParserResources::new();
        let ParserResources {
            ident_slot,
            qualified_ident_slot,
            ..
        } = &mut resources;
        qualified_ident_slot.move_after_underscore(ident_slot);
        let qi = parse_all_with(
            QualifiedIdentParser::<SmtSyntaxChecker>::new(),
            &mut resources,
            b"f 1)",
        );
        assert_eq!(qi.ident.name.as_slice(), b"f");
        assert_eq!(qi.ident.indices.len(), 1);
        assert!(qi.sort.is_none());
        assert!(resources.are_pristine());

        let mut resources = ParserResources::new();
        resources.qualified_ident_slot.move_after_as();
        let qi = parse_all_with(
            QualifiedIdentParser::<SmtSyntaxChecker>::new(),
            &mut resources,
            b"x Bool)",
        );
        assert_eq!(qi.ident.name.as_slice(), b"x");
        assert!(qi.sort.is_some());
        assert!(resources.are_pristine());
    }

    #[test]
    fn slots_are_pristine_after_every_qualified_ident() {
        // every shape (simple, indexed, qualified with a simple, indexed,
        // or applied sort) must leave the qualified ident, ident, and sort
        // slots in their initial state
        for input in [
            &b"f"[..],
            b"(_ f 1 2)",
            b"(as f Bool)",
            b"(as (_ f 1) (_ BitVec 8))",
            b"(as nil (List Int))",
        ] {
            let mut resources = ParserResources::new();
            parse_all_with(
                QualifiedIdentParser::<SmtSyntaxChecker>::new(),
                &mut resources,
                input,
            );
            assert!(resources.are_pristine(), "after {input:?}");
        }
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "must be pristine")]
    fn entering_a_busy_slot_is_rejected() {
        // an entry point may only be used on a pristine slot
        let mut resources = ParserResources::<SmtSyntaxChecker>::new();
        resources.qualified_ident_slot.move_after_as();
        resources.qualified_ident_slot.move_after_open_paren();
    }
}

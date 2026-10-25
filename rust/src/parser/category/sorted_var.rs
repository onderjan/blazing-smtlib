use std::ops::ControlFlow;

use crate::{
    SmtHandler,
    lexicon::SmtSymbolBuf,
    parser::{
        Arena, IdentSlot, SmtCloseParenParser, SmtOpenParenParser, SmtParse, SmtParseError,
        SmtParseState, SmtSyntaxErrorKind, SmtSyntaxExpected, SortSlot, SymbolHandle,
        parse_by_token,
    },
    token::{SmtCursor, SmtSyntaxToken},
};

/// Parses a sorted variable: parentheses-enclosed pair of a symbol and a sort.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct SmtSortedVarParser<H: SmtHandler> {
    _priv: std::marker::PhantomData<H>,
}

impl<H: SmtHandler> SmtSortedVarParser<H> {
    pub fn new() -> Self {
        Self {
            _priv: std::marker::PhantomData,
        }
    }
}

impl<H: SmtHandler> Default for SmtSortedVarParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> SmtParse<H> for SmtSortedVarParser<H> {
    type Result = (SmtSymbolBuf, H::Sort);

    #[inline]
    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        // progress the slot, giving it the sort and ident slots it delegates to
        let SmtParseState {
            ident_slot,
            sort_slot,
            sorted_var_slot,
            arena,
            ..
        } = parse_state;
        parse_by_token(cursor, |cursor, token| {
            match sorted_var_slot.progress(handler, arena, sort_slot, ident_slot, cursor, token)? {
                ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
                ControlFlow::Break((name, sort)) => Ok(ControlFlow::Break(
                    arena.hand_over_sorted_var(name, sort, |name, sort| (name.into_owned(), sort)),
                )),
            }
        })
    }
}

/// A parsed sorted variable: the variable name and its sort.
/// A parsed sorted variable: the name in the arena text and its handled sort.
type SortedVarHandle<H> = (SymbolHandle, <H as SmtHandler>::Sort);

pub(crate) struct SortedVarSlot<H: SmtHandler + ?Sized> {
    /// Whether "(" has been read.
    ///
    /// This only matters if not storing anything yet.
    is_open: bool,
    /// The name, stored in the arena text while its sort is being parsed.
    name: Option<SymbolHandle>,
    /// The sorted variable, stored while waiting for ")".
    sorted_var: Option<SortedVarHandle<H>>,
}

impl<H: SmtHandler + ?Sized> SortedVarSlot<H> {
    pub(crate) fn new() -> Self {
        Self {
            is_open: false,
            name: None,
            sorted_var: None,
        }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        !self.is_open && self.name.is_none() && self.sorted_var.is_none()
    }

    pub(crate) fn clear(&mut self) {
        self.is_open = false;
        self.name = None;
        self.sorted_var = None;
    }

    #[inline]
    pub(crate) fn progress<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        arena: &mut Arena<H>,
        sort_slot: &mut SortSlot<H>,
        ident_slot: &mut IdentSlot,
        cursor: &Z,
        token: Z::Token,
    ) -> Result<ControlFlow<SortedVarHandle<H>>, SmtParseError<H::Error>> {
        // The sequential progress is as follows:
        // 1. Not open, expect an opening parenthesis.
        // 2. Open, expect a symbol serving as the name.
        // 3. Parsing the sort (name is stored).
        // 4. Expecting a closing parenthesis (sorted variable is stored).
        // The function handles this in reverse order
        // so that nothing is taken and put back unnecessarily.

        if let Some(sorted_var) = self.sorted_var.take() {
            // after the sort, waiting for ")"
            SmtCloseParenParser::expect(cursor, token)?;
            // the slot is back in its initial state
            return Ok(ControlFlow::Break(sorted_var));
        }

        if let Some(name) = self.name.take() {
            // after the name, parsing the sort
            match sort_slot.progress(handler, arena, ident_slot, cursor, token)? {
                ControlFlow::Continue(()) => self.name = Some(name),
                ControlFlow::Break(sort) => self.sorted_var = Some((name, sort)),
            }
            return Ok(ControlFlow::Continue(()));
        }

        if self.is_open {
            // after "(", waiting for the name, which goes to the arena text
            let SmtSyntaxToken::Symbol(name) = cursor.syntax(&token) else {
                return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Expected(&[
                    SmtSyntaxExpected::Symbol,
                ])));
            };
            self.name = Some(arena.push_symbol(name));
            self.is_open = false;
        } else {
            // waiting for "("
            debug_assert!(self.is_pristine(), "must be pristine when starting");
            SmtOpenParenParser::expect(cursor, token)?;
            self.is_open = true;
        }
        Ok(ControlFlow::Continue(()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{SmtSyntaxChecker, parser::category::tests::parse_all_with};

    #[test]
    fn slots_are_pristine_after_every_sorted_var() {
        // the sort of the variable uses the sort and ident slots;
        // all three must be back in their initial state afterwards
        for input in [
            &b"(x Int)"[..],
            b"(y (_ BitVec 8))",
            b"(z (Array Int (_ BitVec 8)))",
        ] {
            let mut parse_state = SmtParseState::new();
            let (name, _sort) = parse_all_with(
                SmtSortedVarParser::<SmtSyntaxChecker>::new(),
                &mut parse_state,
                input,
            );
            assert_eq!(name.as_slice().len(), 1, "after {input:?}");
            assert!(parse_state.is_pristine(), "after {input:?}");
        }
    }
}

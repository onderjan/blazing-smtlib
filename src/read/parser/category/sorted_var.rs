use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSymbol,
    read::parser::{
        Arena, CloseParenParser, IdentSlot, OpenParenParser, ParserError, ParserResources,
        SortSlot, TextHandle,
        category::{CategoryErrorKind, CategoryParser},
    },
    token::{Token, TokenKind, TokenType},
};

/// Parses a sorted variable: parentheses-enclosed pair of a symbol and a sort.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct SortedVarParser<H: SmtHandler> {
    _priv: std::marker::PhantomData<H>,
}

impl<H: SmtHandler> SortedVarParser<H> {
    pub fn new() -> Self {
        Self {
            _priv: std::marker::PhantomData,
        }
    }
}

impl<H: SmtHandler> Default for SortedVarParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for SortedVarParser<H> {
    type Result = (SmtSymbol, H::Sort);

    #[inline]
    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        // progress the slot, giving it the sort and ident slots it delegates to
        let ParserResources {
            ident_slot,
            sort_slot,
            sorted_var_slot,
            store,
            ..
        } = resources;
        match sorted_var_slot.progress(handler, store, sort_slot, ident_slot, token)? {
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break((name, sort)) => Ok(ControlFlow::Break(store.hand_over_sorted_var(
                name,
                sort,
                |name, sort| (name.into_owned(), sort),
            ))),
        }
    }
}

/// A parsed sorted variable: the variable name and its sort.
/// A parsed sorted variable: the name in the arena text and its handled sort.
type SortedVarHandle<H> = (TextHandle, <H as SmtHandler>::Sort);

pub(crate) struct SortedVarSlot<H: SmtHandler + ?Sized> {
    /// Whether "(" has been read.
    ///
    /// This only matters if not storing anything yet.
    is_open: bool,
    /// The name, stored in the arena text while its sort is being parsed.
    name: Option<TextHandle>,
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
    pub(crate) fn progress(
        &mut self,
        handler: &mut H,
        arena: &mut Arena<H>,
        sort_slot: &mut SortSlot<H>,
        ident_slot: &mut IdentSlot,
        token: &Token,
    ) -> Result<ControlFlow<SortedVarHandle<H>>, ParserError<H::Error>> {
        // The sequential progress is as follows:
        // 1. Not open, expect an opening parenthesis.
        // 2. Open, expect a symbol serving as the name.
        // 3. Parsing the sort (name is stored).
        // 4. Expecting a closing parenthesis (sorted variable is stored).
        // The function handles this in reverse order
        // so that nothing is taken and put back unnecessarily.

        if let Some(sorted_var) = self.sorted_var.take() {
            // after the sort, waiting for ")"
            CloseParenParser::expect(token)?;
            // the slot is back in its initial state
            return Ok(ControlFlow::Break(sorted_var));
        }

        if let Some(name) = self.name.take() {
            // after the name, parsing the sort
            match sort_slot.progress(handler, arena, ident_slot, token)? {
                ControlFlow::Continue(()) => self.name = Some(name),
                ControlFlow::Break(sort) => self.sorted_var = Some((name, sort)),
            }
            return Ok(ControlFlow::Continue(()));
        }

        if self.is_open {
            // after "(", waiting for the name, which goes to the arena text
            let TokenKind::Symbol(name) = token.kind() else {
                return Err(ParserError::category_error(
                    CategoryErrorKind::ExpectedToken(&[TokenType::Symbol]),
                    token.span(),
                ));
            };
            self.name = Some(arena.push_text(name.as_slice()));
            self.is_open = false;
        } else {
            // waiting for "("
            debug_assert!(self.is_pristine(), "must be pristine when starting");
            OpenParenParser::expect(token)?;
            self.is_open = true;
        }
        Ok(ControlFlow::Continue(()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckStandardSyntax, read::parser::category::tests::parse_all_with};

    #[test]
    fn slots_are_pristine_after_every_sorted_var() {
        // the sort of the variable uses the sort and ident slots;
        // all three must be back in their initial state afterwards
        for input in [
            &b"(x Int)"[..],
            b"(y (_ BitVec 8))",
            b"(z (Array Int (_ BitVec 8)))",
        ] {
            let mut resources = ParserResources::new();
            let (name, _sort) = parse_all_with(
                SortedVarParser::<CheckStandardSyntax>::new(),
                &mut resources,
                input,
            );
            assert_eq!(name.as_slice().len(), 1, "after {input:?}");
            assert!(resources.are_pristine(), "after {input:?}");
        }
    }
}

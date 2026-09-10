use std::ops::ControlFlow;

use crate::{
    SmtHandler,
    read::parser::{
        IdentSlot, ParserError, QualifiedIdentSlot, SExprSlot, SortSlot, SortedVarSlot,
        category::attribute::AttributeSlot,
    },
    token::{Token, TokenKind},
};

/// Contains non-duplicated parser resources.
///
/// Parsers that are constructed multiple times in locations
/// where their use does not overlap can have unnecessarily
/// duplicated resources (e.g. collections). This structure
/// is only constructed once for the root parser and
/// propagated to smaller parsers.
pub struct ParserResources<H: SmtHandler + ?Sized> {
    pub(crate) ident_slot: IdentSlot,
    pub(crate) qualified_ident_slot: QualifiedIdentSlot<H>,
    pub(crate) sort_slot: SortSlot<H>,
    pub(crate) sorted_var_slot: SortedVarSlot<H>,
    pub(crate) s_expr_slot: SExprSlot<H>,
    pub(crate) attribute_slot: AttributeSlot<H>,
}

impl<H: SmtHandler + ?Sized> ParserResources<H> {
    pub fn new() -> Self {
        Self {
            ident_slot: IdentSlot::new(),
            qualified_ident_slot: QualifiedIdentSlot::new(),
            sort_slot: SortSlot::new(),
            sorted_var_slot: SortedVarSlot::new(),
            s_expr_slot: SExprSlot::new(),
            attribute_slot: AttributeSlot::new(),
        }
    }

    pub(crate) fn are_pristine(&self) -> bool {
        self.ident_slot.is_pristine()
            && self.qualified_ident_slot.is_pristine()
            && self.sort_slot.is_pristine()
            && self.sorted_var_slot.is_pristine()
            && self.s_expr_slot.is_pristine()
            && self.attribute_slot.is_pristine()
    }

    pub(crate) fn clear(&mut self) {
        self.ident_slot.clear();
        self.qualified_ident_slot.clear();
        self.sort_slot.clear();
        self.sorted_var_slot.clear();
        self.s_expr_slot.clear();
        self.attribute_slot.clear();
    }
}

impl<H: SmtHandler + ?Sized> Default for ParserResources<H> {
    fn default() -> Self {
        Self::new()
    }
}

/// A resource that stores multiple elements closed by a parenthesis.
pub(crate) struct ClosedMultipleResource<T> {
    outside: bool,
    items: Vec<T>,
}

impl<T> ClosedMultipleResource<T> {
    pub(crate) fn new() -> Self {
        Self {
            outside: true,
            items: Vec::new(),
        }
    }

    pub(crate) fn progress<E>(
        &mut self,
        token: &Token,
        element: impl FnOnce(&Token) -> Result<ControlFlow<T>, ParserError<E>>,
    ) -> Result<ControlFlow<Vec<T>>, ParserError<E>> {
        if self.outside {
            // we are outside, a closing parenthesis ends processing
            if matches!(token.kind(), TokenKind::ParenClose) {
                return Ok(ControlFlow::Break(self.items.drain(..).collect()));
            }
            // we are no longer outside
            self.outside = false;
        }
        // we are inside, parse the element using the inner parser
        if let ControlFlow::Break(item) = element(token)? {
            // add element, we are back outside
            self.items.push(item);
            self.outside = true;
        }
        Ok(ControlFlow::Continue(()))
    }

    pub(crate) fn is_pristine(&self) -> bool {
        self.outside && self.items.is_empty()
    }

    pub(crate) fn clear(&mut self) {
        self.outside = true;
        self.items.clear();
    }
}

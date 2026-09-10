use crate::{
    SmtHandler,
    read::parser::{IdentSlot, SortSlot},
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
    pub(crate) sort_slot: SortSlot<H>,
}

impl<H: SmtHandler + ?Sized> ParserResources<H> {
    pub fn new() -> Self {
        Self {
            ident_slot: IdentSlot::new(),
            sort_slot: SortSlot::new(),
        }
    }

    pub(crate) fn are_pristine(&self) -> bool {
        self.ident_slot.is_pristine() && self.sort_slot.is_pristine()
    }

    pub(crate) fn clear(&mut self) {
        self.ident_slot.clear();
        self.sort_slot.clear();
    }
}

impl<H: SmtHandler + ?Sized> Default for ParserResources<H> {
    fn default() -> Self {
        Self::new()
    }
}

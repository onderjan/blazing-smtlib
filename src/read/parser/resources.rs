use crate::read::parser::IdentSlot;

/// Contains non-duplicated parser resources.
///
/// Parsers that are constructed multiple times in locations
/// where their use does not overlap can have unnecessarily
/// duplicated resources (e.g. collections). This structure
/// is only constructed once for the root parser and
/// propagated to smaller parsers.
pub struct ParserResources {
    pub(crate) ident_slot: IdentSlot,
}

impl ParserResources {
    pub fn new() -> Self {
        Self {
            ident_slot: IdentSlot::new(),
        }
    }

    pub(crate) fn are_pristine(&self) -> bool {
        self.ident_slot.is_pristine()
    }

    pub(crate) fn clear(&mut self) {
        self.ident_slot.clear();
    }
}

impl Default for ParserResources {
    fn default() -> Self {
        Self::new()
    }
}

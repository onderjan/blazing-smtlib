/// Contains non-duplicated parser resources.
///
/// Parsers that are constructed multiple times in locations
/// where their use does not overlap can have unnecessarily
/// duplicated resources (e.g. collections). This structure
/// is only constructed once for the root parser and
/// propagated to smaller parsers.
pub struct ParserResources {
    _priv: (),
}

impl ParserResources {
    pub fn new() -> Self {
        Self { _priv: () }
    }

    pub(crate) fn are_pristine(&self) -> bool {
        // TODO: add resources
        true
    }

    pub(crate) fn clear(&mut self) {
        // TODO: add resources
    }
}

impl Default for ParserResources {
    fn default() -> Self {
        Self::new()
    }
}

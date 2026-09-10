/// Contains non-duplicated parser resources.
///
/// Parsers that are constructed multiple times in locations
/// where their use does not overlap can have unnecessarily
/// duplicated resources (e.g. collections). This structure
/// is only constructed once for the root parser and
/// propagated to smaller parsers.
///
/// The resources are generic to allow the library user
/// to use additional resources in the custom parsers.
pub struct ParserResources<'a, C> {
    _priv: (),
    custom: &'a mut C,
}

impl<'a, C> ParserResources<'a, C> {
    pub fn new(custom: &'a mut C) -> Self {
        Self { _priv: (), custom }
    }

    pub fn custom(&self) -> &C {
        self.custom
    }

    pub fn custom_mut(&mut self) -> &mut C {
        self.custom
    }
}

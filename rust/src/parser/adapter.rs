use std::{fmt, ops::ControlFlow};

use crate::{
    SmtHandler,
    parser::{SmtParse, SmtParseError, SmtParseState},
    token::{SmtConsume, SmtConsumeFrom, SmtCursor},
};

/// Adapts a parser to the token consumer a lexer drives.
///
/// The adapter implements [`SmtConsume`]: it calls the parser,
/// providing it the handler and additional persistent resources.
pub struct SmtParseAdapter<'a, H: SmtHandler + ?Sized, P: SmtParse<H>> {
    handler: &'a mut H,
    parse_state: SmtParseState<H>,
    parser: P,
    version_set: bool,
}

impl<'a, H: SmtHandler + ?Sized, P: SmtParse<H>> fmt::Debug for SmtParseAdapter<'a, H, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SmtParseAdapter").finish_non_exhaustive()
    }
}

impl<'a, H: SmtHandler + ?Sized, P: SmtParse<H>> SmtParseAdapter<'a, H, P> {
    /// Creates an adapter of `parser` over `handler`, with fresh resources.
    pub fn new(handler: &'a mut H, parser: P) -> Self {
        Self {
            handler,
            parse_state: SmtParseState::new(),
            parser,
            version_set: false,
        }
    }

    /// Returns a reference to the adapted parser.
    pub fn parser(&self) -> &P {
        &self.parser
    }

    /// Returns a mutable reference to the adapted parser.
    pub fn parser_mut(&mut self) -> &mut P {
        &mut self.parser
    }

    /// Returns a reference to the handler.
    pub fn handler(&self) -> &H {
        self.handler
    }

    /// Returns a mutable reference to the handler.
    pub fn handler_mut(&mut self) -> &mut H {
        self.handler
    }

    /// Takes the parser back out of the adapter.
    pub fn into_parser(self) -> P {
        self.parser
    }
}

impl<H: SmtHandler + ?Sized, P: SmtParse<H>> SmtConsume for SmtParseAdapter<'_, H, P> {
    type Result = P::Result;
    type Error = SmtParseError<H::Error>;
    const IS_CONCRETE: bool = false;
}

impl<H: SmtHandler + ?Sized, P: SmtParse<H>, Z: SmtCursor> SmtConsumeFrom<Z>
    for SmtParseAdapter<'_, H, P>
{
    #[inline]
    fn consume(
        &mut self,
        cursor: &mut Z,
    ) -> Result<ControlFlow<P::Result>, SmtParseError<H::Error>> {
        // set the version before starting to consume
        if !self.version_set {
            self.handler.set_version(cursor.version());
            self.version_set = true;
        }

        // provide the handler and resources to the parser
        let result = self
            .parser
            .parse(self.handler, &mut self.parse_state, cursor)?;
        if result.is_break() {
            // set the version before starting to consume the next time
            self.version_set = false;
            debug_assert!(
                self.parse_state.is_pristine(),
                "resources should be pristine after the top-level parser finishes"
            );
        }
        Ok(result)
    }
}

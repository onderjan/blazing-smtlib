use std::ops::ControlFlow;

use crate::{
    SmtHandler,
    read::parser::{SmtParse, SmtParseError, SmtParseState},
    token::{SmtBatchCursor, SmtConsume},
};

/// Adapts a parser to the token consumer a lexer drives.
///
/// The adapter implements [`SmtConsume`]: it calls the parser,
/// providing it the handler and additional persistent resources.
pub struct SmtParseAdapter<'a, H: SmtHandler + ?Sized, P: SmtParse<H>> {
    handler: &'a mut H,
    resources: SmtParseState<H>,
    parser: P,
}

impl<'a, H: SmtHandler + ?Sized, P: SmtParse<H>> SmtParseAdapter<'a, H, P> {
    /// Creates an adapter of `parser` over `handler`, with fresh resources.
    pub fn new(handler: &'a mut H, parser: P) -> Self {
        Self {
            handler,
            resources: SmtParseState::new(),
            parser,
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

    /// Takes the parser back out of the adapter.
    pub fn into_parser(self) -> P {
        self.parser
    }
}

impl<H: SmtHandler + ?Sized, P: SmtParse<H>> SmtConsume for SmtParseAdapter<'_, H, P> {
    type Result = P::Result;
    type Error = SmtParseError<H::Error>;

    #[inline]
    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<P::Result>, SmtParseError<H::Error>> {
        // provide the handler and resources to the parser
        let result = self
            .parser
            .parse(self.handler, &mut self.resources, cursor)?;
        if result.is_break() {
            debug_assert!(
                self.resources.is_pristine(),
                "resources should be pristine after the top-level parser finishes"
            );
        }
        Ok(result)
    }
}

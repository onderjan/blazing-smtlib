use std::ops::ControlFlow;

use crate::{
    SmtHandler,
    parser::{SmtParse, SmtParseError, SmtParseState},
    token::{SmtConsume, SmtProduce},
};

/// Adapts a parser to the token consumer a lexer drives.
///
/// The adapter implements [`SmtConsume`]: it calls the parser,
/// providing it the handler and additional persistent resources.
pub struct SmtParseAdapter<'a, H: SmtHandler + ?Sized, P: SmtParse<H>> {
    handler: &'a mut H,
    parse_state: SmtParseState<H>,
    parser: P,
}

impl<'a, H: SmtHandler + ?Sized, P: SmtParse<H>> SmtParseAdapter<'a, H, P> {
    /// Creates an adapter of `parser` over `handler`, with fresh resources.
    pub fn new(handler: &'a mut H, parser: P) -> Self {
        Self {
            handler,
            parse_state: SmtParseState::new(),
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
    const IS_CONCRETE: bool = false;

    #[inline]
    fn consume<'a, C: SmtProduce<'a>>(
        &mut self,
        cursor: &mut C,
    ) -> Result<ControlFlow<P::Result>, SmtParseError<H::Error>> {
        // provide the handler and resources to the parser
        let result = self
            .parser
            .parse(self.handler, &mut self.parse_state, cursor)?;
        if result.is_break() {
            debug_assert!(
                self.parse_state.is_pristine(),
                "resources should be pristine after the top-level parser finishes"
            );
        }
        Ok(result)
    }
}

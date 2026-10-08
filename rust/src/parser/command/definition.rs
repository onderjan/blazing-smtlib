use std::ops::ControlFlow;

use crate::{
    SmtCommandHandler,
    parser::{SmtParse, SmtParseError, SmtParseState, handle_err},
    token::SmtBatchCursor,
};

/// A definition where a signature is followed by a body.
///
/// The handler must know the signature before starting the body.
///
/// The commands using a definition parser do not call the
/// handler after ending, as everything is handled by the parser.
pub(super) trait Definition<H: SmtCommandHandler> {
    type Signature: SmtParse<H> + Default;
    type Body: SmtParse<H> + Default;

    /// Start is invoked before the first definition body token.
    fn start(
        handler: &mut H,
        signature: <Self::Signature as SmtParse<H>>::Result,
    ) -> Result<(), H::Error>;

    /// End is invoked when the last definition body token is processed.
    fn end(handler: &mut H, body: <Self::Body as SmtParse<H>>::Result) -> Result<(), H::Error>;
}

enum DefinitionParserState {
    Signature,
    Body,
}

/// Parser of a definition that has a signature followed by a body.
///
/// The commands using this parser do not call the
/// handler after ending, as everything is handled by the parser.
pub(super) struct DefinitionParser<H: SmtCommandHandler, D: Definition<H>> {
    state: DefinitionParserState,
    signature_parser: D::Signature,
    body_parser: D::Body,
}

impl<H: SmtCommandHandler, D: Definition<H>> DefinitionParser<H, D> {
    pub fn new() -> Self {
        Self {
            state: DefinitionParserState::Signature,
            signature_parser: D::Signature::default(),
            body_parser: D::Body::default(),
        }
    }
}

impl<H: SmtCommandHandler, D: Definition<H>> Default for DefinitionParser<H, D> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtCommandHandler, D: Definition<H>> SmtParse<H> for DefinitionParser<H, D> {
    type Result = ();

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        if matches!(self.state, DefinitionParserState::Signature) {
            // parse the signature; it ends at the last consumed token
            match self.signature_parser.parse(handler, parse_state, cursor)? {
                ControlFlow::Continue(()) => return Ok(ControlFlow::Continue(())),
                ControlFlow::Break(signature) => {
                    // start the body in the handler and move to parsing the body
                    handle_err(D::start(handler, signature))?;
                    self.state = DefinitionParserState::Body;
                }
            }
        }
        // parse the body on the tokens left; it ends at the last consumed token
        match self.body_parser.parse(handler, parse_state, cursor)? {
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(body) => {
                // end the body in the handler, reset, and break
                handle_err(D::end(handler, body))?;
                self.state = DefinitionParserState::Signature;
                Ok(ControlFlow::Break(()))
            }
        }
    }
}

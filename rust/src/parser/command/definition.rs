use std::ops::ControlFlow;

use crate::{
    SmtCommandHandler,
    parser::{SmtParse, SmtParseError, SmtParseState, handle_err},
    token::SmtCursor,
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
    type Buffer: Default;

    /// Start is invoked before the first definition body token.
    fn start(
        handler: &mut H,
        signature: <Self::Signature as SmtParse<H>>::Result,
        buffer: &mut Self::Buffer,
    ) -> Result<(), H::Error>;
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
    buffer: D::Buffer,
}

impl<H: SmtCommandHandler, D: Definition<H>> DefinitionParser<H, D> {
    pub fn new() -> Self {
        Self {
            state: DefinitionParserState::Signature,
            signature_parser: D::Signature::default(),
            body_parser: D::Body::default(),
            buffer: D::Buffer::default(),
        }
    }
}

impl<H: SmtCommandHandler, D: Definition<H>> Default for DefinitionParser<H, D> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtCommandHandler, D: Definition<H>> SmtParse<H> for DefinitionParser<H, D> {
    type Result = <D::Body as SmtParse<H>>::Result;

    #[inline]
    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        if matches!(self.state, DefinitionParserState::Signature) {
            // parse the signature; it ends at the last consumed token
            match self.signature_parser.parse(handler, parse_state, cursor)? {
                ControlFlow::Continue(()) => return Ok(ControlFlow::Continue(())),
                ControlFlow::Break(signature) => {
                    // start the body in the handler and move to parsing the body
                    handle_err(D::start(handler, signature, &mut self.buffer))?;
                    self.state = DefinitionParserState::Body;
                }
            }
        }
        // parse the body on the tokens left; it ends at the last consumed token
        match self.body_parser.parse(handler, parse_state, cursor)? {
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(body) => {
                // reset and break
                self.state = DefinitionParserState::Signature;
                // the definition end will be processed
                // after the last closing parenthesis
                Ok(ControlFlow::Break(body))
            }
        }
    }
}

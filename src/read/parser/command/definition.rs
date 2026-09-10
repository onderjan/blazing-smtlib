use std::ops::ControlFlow;

use crate::{
    CommandHandler,
    read::parser::{CategoryParser, ParserError, ParserResources, handle_err},
    token::Token,
};

/// A definition where a signature is followed by a body.
///
/// The handler must know the signature before starting the body.
///
/// The commands using a definition parser do not call the
/// handler after ending, as everything is handled by the parser.
pub(super) trait Definition<H: CommandHandler> {
    type Signature: CategoryParser<H> + Default;
    type Body: CategoryParser<H> + Default;

    /// Start is invoked before the first definition body token.
    fn start(
        handler: &mut H,
        signature: <Self::Signature as CategoryParser<H>>::Result,
    ) -> Result<(), H::Error>;

    /// End is invoked when the last definition body token is processed.
    fn end(
        handler: &mut H,
        body: <Self::Body as CategoryParser<H>>::Result,
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
pub(super) struct DefinitionParser<H: CommandHandler, D: Definition<H>> {
    state: DefinitionParserState,
    signature_parser: D::Signature,
    body_parser: D::Body,
}

impl<H: CommandHandler, D: Definition<H>> DefinitionParser<H, D> {
    pub fn new() -> Self {
        Self {
            state: DefinitionParserState::Signature,
            signature_parser: D::Signature::default(),
            body_parser: D::Body::default(),
        }
    }
}

impl<H: CommandHandler, D: Definition<H>> Default for DefinitionParser<H, D> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler, D: Definition<H>> CategoryParser<H> for DefinitionParser<H, D> {
    type Result = ();

    #[inline]
    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        let span = token.span();
        match self.state {
            DefinitionParserState::Signature => {
                // parse the signature
                if let ControlFlow::Break(signature) =
                    self.signature_parser.progress(handler, resources, token)?
                {
                    // start the body in the handler and move to parsing the body
                    handle_err(D::start(handler, signature), span)?;
                    self.state = DefinitionParserState::Body;
                }
            }
            DefinitionParserState::Body => {
                // parse the body
                if let ControlFlow::Break(body) =
                    self.body_parser.progress(handler, resources, token)?
                {
                    // end the body in the handler, reset, and break
                    handle_err(D::end(handler, body), span)?;
                    self.state = DefinitionParserState::Signature;
                    return Ok(ControlFlow::Break(()));
                }
            }
        }

        Ok(ControlFlow::Continue(()))
    }
}

use std::ops::ControlFlow;

use crate::{
    CommandHandler,
    read::parser::{Parser, ParserError, ParserResources, handle_err},
    token::TokenCursor,
};

/// A definition where a signature is followed by a body.
///
/// The handler must know the signature before starting the body.
///
/// The commands using a definition parser do not call the
/// handler after ending, as everything is handled by the parser.
pub(super) trait Definition<H: CommandHandler> {
    type Signature: Parser<H> + Default;
    type Body: Parser<H> + Default;

    /// Start is invoked before the first definition body token.
    fn start(
        handler: &mut H,
        signature: <Self::Signature as Parser<H>>::Result,
    ) -> Result<(), H::Error>;

    /// End is invoked when the last definition body token is processed.
    fn end(handler: &mut H, body: <Self::Body as Parser<H>>::Result) -> Result<(), H::Error>;
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

impl<H: CommandHandler, D: Definition<H>> Parser<H> for DefinitionParser<H, D> {
    type Result = ();

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut TokenCursor,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        if matches!(self.state, DefinitionParserState::Signature) {
            // parse the signature; it ends at the last consumed token
            match self.signature_parser.parse(handler, resources, cursor)? {
                ControlFlow::Continue(()) => return Ok(ControlFlow::Continue(())),
                ControlFlow::Break(signature) => {
                    let span = cursor
                        .last_consumed()
                        .expect("a finished signature parser must have consumed a token")
                        .span();
                    // start the body in the handler and move to parsing the body
                    handle_err(D::start(handler, signature), span)?;
                    self.state = DefinitionParserState::Body;
                }
            }
        }
        // parse the body on the tokens left; it ends at the last consumed token
        match self.body_parser.parse(handler, resources, cursor)? {
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(body) => {
                let span = cursor
                    .last_consumed()
                    .expect("a finished body parser must have consumed a token")
                    .span();
                // end the body in the handler, reset, and break
                handle_err(D::end(handler, body), span)?;
                self.state = DefinitionParserState::Signature;
                Ok(ControlFlow::Break(()))
            }
        }
    }
}

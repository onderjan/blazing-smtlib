use crate::{
    SmtHandler,
    parser::{
        ParserError, ParserOrHandlerError, ParserState, command::CommandCallback, progress_state,
    },
    token::Token,
};

pub fn parse_attribute<H: SmtHandler>(
    handler: &mut H,
    callback: CommandCallback<H, H::Attribute>,
    token: Token,
) -> Result<ParserState<H>, ParserOrHandlerError<H>> {
    let Token::Keyword(keyword) = token else {
        return Err(ParserOrHandlerError::ParserError(
            ParserError::ExpectedKeyword,
        ));
    };

    // TODO: name-value attributes
    let attribute = handler
        .handle_attribute(keyword.as_str(), None)
        .map_err(ParserOrHandlerError::HandlerError)?;
    Ok(progress_state(
        callback(handler, attribute).map_err(ParserOrHandlerError::HandlerError)?,
    ))
}

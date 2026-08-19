use crate::{
    SmtHandler,
    parser::{ParserError, ParserOrHandlerError, ParserState},
    token::Token,
};

pub struct AttributeParser;

/*

pub fn parse_attribute<H: SmtHandler>(
    handler: &mut H,
    token: Token,
) -> Result<<H>, ParserOrHandlerError<H>> {
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

*/

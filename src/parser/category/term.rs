use crate::{
    SmtHandler,
    parser::{ParserOrHandlerError, ParserState, command::CommandCallback},
    token::Token,
};

pub(crate) fn parse_term<H: SmtHandler>(
    _handler: &mut H,
    _callback: CommandCallback<H, H::Term>,
    _token: Token,
) -> Result<ParserState<H>, ParserOrHandlerError<H>> {
    todo!("Parse term")
}

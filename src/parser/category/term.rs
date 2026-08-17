use crate::{
    CommandHandler,
    parser::{Parser, ParserOrHandlerError, ParserState, command::CommandCallback},
    token::Token,
};

impl<H: CommandHandler> Parser<'_, H> {
    pub(crate) fn parse_term(
        &mut self,
        _callback: CommandCallback<H, H::Term>,
        _token: Token,
    ) -> Result<ParserState<H>, ParserOrHandlerError<H>> {
        todo!("Parse term")
    }
}

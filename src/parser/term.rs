use crate::{
    CommandHandler,
    parser::{ParserOrHandlerError, ParserState, command::CommandCallback},
    token::Token,
};

impl<H: CommandHandler> super::Parser<'_, H> {
    pub(super) fn parse_term(
        &mut self,
        _callback: CommandCallback<H, H::Term>,
        _token: Token,
    ) -> Result<ParserState<H>, ParserOrHandlerError<H>> {
        todo!("Parse term")
    }
}

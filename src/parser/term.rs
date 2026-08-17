use crate::{
    CommandHandler,
    parser::{ParserOrHandlerError, ParserState, command::CommandActionTerm},
    token::Token,
};

impl<H: CommandHandler> super::Parser<'_, H> {
    pub(super) fn parse_term(
        &mut self,
        _callback: CommandActionTerm<H>,
        _token: Token,
    ) -> Result<ParserState<H>, ParserOrHandlerError<H>> {
        todo!("Parse term")
    }
}

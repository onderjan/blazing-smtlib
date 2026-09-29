use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtSpan, SmtSymbolView,
    read::parser::{
        ParserError, ParserResources, ParserState, category::CategoryParser, handle_err,
    },
    token::{Token, TokenCursor},
};

mod datatype;
mod definition;
mod function;
mod standard;

pub(super) use standard::{CommandParsers, StandardCommandKind, StandardCommandResult};

pub enum NoCommandParser {}

impl<H: CommandHandler> CategoryParser<H> for NoCommandParser {
    type Result = ();

    #[inline]
    fn progress(
        &mut self,
        _handler: &mut H,
        _resources: &mut ParserResources<H>,
        _token: Token,
    ) -> Result<ControlFlow<()>, ParserError<H::Error>> {
        match *self {}
    }
}

/// Determines how a single command should be handled by a command handler.
pub trait CommandAction<H: CommandHandler> {
    type Parser: CategoryParser<H>;

    /// Handles the result of a command.
    fn handle(
        handler: &mut H,
        result: <Self::Parser as CategoryParser<H>>::Result,
    ) -> Result<(), H::Error>;

    /// Determines whether this should lead to an exit.
    ///
    /// This is overridden by the SMT-LIB (exit) command.
    fn is_exit() -> bool {
        false
    }
}

/// A parser that processes a single command (starting after its name).
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub struct CommandParser<H: CommandHandler, C: CommandAction<H>> {
    parser: C::Parser,
}

impl<H: CommandHandler, C: CommandAction<H>> CommandParser<H, C> {
    pub fn new(parser: C::Parser) -> Self {
        Self { parser }
    }
}

impl<H: CommandHandler, C: CommandAction<H>> Default for CommandParser<H, C>
where
    C::Parser: Default,
{
    fn default() -> Self {
        Self::new(C::Parser::default())
    }
}

impl<H: CommandHandler, C: CommandAction<H>> CategoryParser<H> for CommandParser<H, C> {
    type Result = ();

    #[inline]
    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: Token,
    ) -> Result<ControlFlow<()>, ParserError<H::Error>> {
        self.progress_all(handler, resources, &mut TokenCursor::single(token))
    }

    #[inline]
    fn progress_all(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut TokenCursor,
    ) -> Result<ControlFlow<()>, ParserError<H::Error>> {
        match self.parser.progress_all(handler, resources, cursor)? {
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(result) => {
                // the command ends at the last consumed token, get its span
                let span = cursor
                    .last_consumed()
                    .expect("a finished command parser has consumed a token")
                    .span();
                handle_err(C::handle(handler, result), span)?;
                Ok(ControlFlow::Break(()))
            }
        }
    }
}

impl<H: CommandHandler> super::Parser<'_, H> {
    /// Starts a non-standard command named by a symbol.
    ///
    /// A command identified by a symbol is never standard,
    /// as standard command names are reserved words.
    pub(super) fn start_nonstandard_command(
        &mut self,
        name: SmtSymbolView<'_>,
        span: SmtSpan,
    ) -> Result<ParserState<H>, ParserError<H::Error>> {
        match self.handler.nonstandard_command(name) {
            Ok(parser) => Ok(ParserState::NonstandardCommand(parser)),
            Err(err) => Err(ParserError::handler_error(err, span)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckStandardSyntax, SmtSpan, token::InnerType};

    #[test]
    fn finished_command_parser_parses_the_next_command() {
        let mut handler = CheckStandardSyntax;
        let mut parser: CommandParser<CheckStandardSyntax, standard::CheckSat> =
            CommandParser::default();

        // a check-sat command body is just the closing parenthesis,
        // so one token finishes the command; the parser is self-restarting
        // after the break, so the next command body parses without a restart
        for _ in 0..2 {
            let span = SmtSpan::new_zero();
            let close = Token::new(&Some((InnerType::ParenClose, &[])), &span);
            let flow = parser
                .progress(&mut handler, &mut ParserResources::new(), close)
                .expect("check-sat closing parenthesis must parse");
            assert!(matches!(flow, ControlFlow::Break(())));
        }
    }
}

use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtSpan, SmtSymbolView,
    read::parser::{ParserError, ParserState, category::CategoryParser},
    token::Token,
};

mod standard;

pub(super) use standard::{CommandParsers, StandardCommandKind};

pub trait ParseCommand<H: CommandHandler + ?Sized> {
    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<CommandResult, ()>, ParserError<H::Error>>;
}

pub enum NoCommandParser {}

impl<H: CommandHandler> ParseCommand<H> for NoCommandParser {
    fn progress(
        &mut self,
        _handler: &mut H,
        _token: Token,
    ) -> Result<ControlFlow<CommandResult, ()>, ParserError<H::Error>> {
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
    pub fn new() -> Self {
        Self {
            parser: C::Parser::default(),
        }
    }

    pub fn restart(&mut self) {
        self.parser.restart();
    }
}

impl<H: CommandHandler, C: CommandAction<H>> Default for CommandParser<H, C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler, C: CommandAction<H>> ParseCommand<H> for CommandParser<H, C> {
    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<CommandResult, ()>, ParserError<H::Error>> {
        let span = token.span();
        let ControlFlow::Break(result) = self.parser.progress(handler, token)? else {
            return Ok(ControlFlow::Continue(()));
        };

        match C::handle(handler, result) {
            Ok(()) => {
                let command_result = if C::is_exit() {
                    CommandResult::Exit
                } else {
                    CommandResult::EndCommand
                };
                Ok(ControlFlow::Break(command_result))
            }
            Err(err) => Err(ParserError::handler_error(err, span)),
        }
    }
}

pub enum CommandResult {
    EndCommand,
    Exit,
}

impl<H: CommandHandler> super::Parser<'_, H> {
    pub(super) fn start_command(
        &mut self,
        name: SmtSymbolView<'_>,
        span: SmtSpan,
    ) -> Result<ParserState<H>, ParserError<H::Error>> {
        match StandardCommandKind::from_name(name.as_slice()) {
            Some(kind) => {
                self.command_parsers.restart(kind);
                Ok(ParserState::Command(kind))
            }
            None => match self.handler.nonstandard_command(name) {
                Ok(parser) => Ok(ParserState::NonstandardCommand(parser)),
                Err(err) => Err(ParserError::handler_error(err, span)),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckStandardSyntax, SmtSpan, token::TokenKind};

    #[test]
    fn finished_command_parser_parses_the_next_command() {
        todo!("Fix test")
        /*let mut handler = CheckStandardSyntax;
        let mut parser: CommandParser<CheckStandardSyntax, CommandCheckSat> = CommandParser::new();

        // a check-sat command body is just the closing parenthesis,
        // so one token finishes the command; the parser is self-restarting
        // after the break, so the next command body parses without a restart
        for _ in 0..2 {
            let close = Token::new(TokenKind::ParenClose, SmtSpan::new_zero());
            let flow = parser
                .progress(&mut handler, close)
                .expect("check-sat closing parenthesis must parse");
            assert!(matches!(
                flow,
                ControlFlow::Break(CommandResult::EndCommand)
            ));
        }*/
    }
}

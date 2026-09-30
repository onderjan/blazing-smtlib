use std::ops::ControlFlow;

use crate::{
    CommandHandler,
    read::parser::{CommandParser, CommandParserStop, Parser, ParserError, ParserResources},
    token::TokenCursor,
};

/// Parses an SMT-LIB script: a sequence of commands, each delivered to the
/// command handler as it is parsed.
///
/// The parser is a loop over a [`CommandParser`]. It finishes after the
/// command `(exit)` or at the end of the input between commands, returning
/// [`ControlFlow::Break`] with a [`ScriptParserStop`], and is then back at
/// its start.
pub struct ScriptParser<H: CommandHandler> {
    command: CommandParser<H>,
}

/// Why the script parser finished.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScriptParserStop {
    /// Finished due to an exit command.
    ExitCommand,
    /// Finished due to reaching the end of file.
    EndOfFile,
}

impl<H: CommandHandler> ScriptParser<H> {
    pub fn new() -> Self {
        Self {
            command: CommandParser::new(),
        }
    }
}

impl<H: CommandHandler> Default for ScriptParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler> Parser<H> for ScriptParser<H> {
    type Result = ScriptParserStop;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut TokenCursor,
    ) -> Result<ControlFlow<ScriptParserStop>, ParserError<H::Error>> {
        loop {
            match self.command.parse(handler, resources, cursor)? {
                ControlFlow::Continue(()) => {
                    // the cursor is consumed, the command continues in the next one
                    return Ok(ControlFlow::Continue(()));
                }
                ControlFlow::Break(CommandParserStop::Command) => {
                    // a command has ended: parse the next one
                }
                ControlFlow::Break(CommandParserStop::ExitCommand) => {
                    // the exit command ends the script: stop after it
                    return Ok(ControlFlow::Break(ScriptParserStop::ExitCommand));
                }
                ControlFlow::Break(CommandParserStop::EndOfFile) => {
                    // the end of the input between commands ends the script
                    return Ok(ControlFlow::Break(ScriptParserStop::EndOfFile));
                }
            }
        }
    }
}

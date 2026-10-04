use std::ops::ControlFlow;

use crate::{
    CommandHandler,
    read::parser::{
        CommandParser, CommandParserStop, Parser, ParserResources, SmtParseError,
        SmtSyntaxErrorKind,
    },
    token::{SmtBatchCursor, SmtVersionPosture},
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
    posture: SmtVersionPosture,
    num_version_declarations: u64,
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
    pub fn new(posture: SmtVersionPosture) -> Self {
        Self {
            command: CommandParser::new(),
            posture,
            num_version_declarations: 0,
        }
    }
}

impl<H: CommandHandler> Default for ScriptParser<H> {
    fn default() -> Self {
        Self::new(SmtVersionPosture::default())
    }
}

impl<H: CommandHandler> Parser<H> for ScriptParser<H> {
    type Result = ScriptParserStop;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<ScriptParserStop>, SmtParseError<H::Error>> {
        loop {
            match self.command.parse(handler, resources, cursor)? {
                ControlFlow::Continue(()) => {
                    // the cursor is consumed, the command continues in the next one
                    return Ok(ControlFlow::Continue(()));
                }
                ControlFlow::Break(CommandParserStop::Command) => {
                    // a command has ended: parse the next one
                }
                ControlFlow::Break(CommandParserStop::SetVersion(version, span)) => {
                    // ensure the version is allowed by the posture
                    if !self.posture.allowed().contains(&version) {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::UnsupportedVersion,
                            span,
                        ));
                    }
                    if let Some(max_declarations) = self.posture.max_declarations()
                        && self.num_version_declarations >= max_declarations
                    {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::TooManyVersionDeclarations(max_declarations),
                            span,
                        ));
                    }
                    // allowed, set version on the cursor
                    cursor.set_version(version);
                    self.num_version_declarations += 1;
                }
                ControlFlow::Break(CommandParserStop::ExitCommand) => {
                    // the exit command ends the script: stop after it
                    // reset the number of version declarations before breaking
                    self.num_version_declarations = 0;
                    return Ok(ControlFlow::Break(ScriptParserStop::ExitCommand));
                }
                ControlFlow::Break(CommandParserStop::EndOfFile) => {
                    // the end of the input between commands ends the script
                    // reset the number of version declarations before breaking
                    self.num_version_declarations = 0;
                    return Ok(ControlFlow::Break(ScriptParserStop::EndOfFile));
                }
            }
        }
    }
}

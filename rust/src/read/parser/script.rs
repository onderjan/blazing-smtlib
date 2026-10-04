use std::ops::ControlFlow;

use crate::{
    SmtCommandHandler,
    read::parser::{
        SmtCommandOutcome, SmtCommandParser, SmtParse, SmtParseError, SmtParseState,
        SmtSyntaxErrorKind,
    },
    token::{SmtBatchCursor, SmtVersionPosture},
};

/// Parses an SMT-LIB script: a sequence of commands, each delivered to the
/// command handler as it is parsed.
///
/// The parser is a loop over a [`SmtCommandParser`]. It finishes after the
/// command `(exit)` or at the end of the input between commands, returning
/// [`ControlFlow::Break`] with a [`SmtScriptEnd`], and is then back at
/// its start.
pub struct SmtScriptParser<H: SmtCommandHandler> {
    command: SmtCommandParser<H>,
    posture: SmtVersionPosture,
    num_version_declarations: u64,
}

/// Why the script parser finished.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtScriptEnd {
    /// Finished due to an exit command.
    Exit,
    /// Finished due to reaching the end of file.
    EndOfFile,
}

impl<H: SmtCommandHandler> SmtScriptParser<H> {
    pub fn new(posture: SmtVersionPosture) -> Self {
        Self {
            command: SmtCommandParser::new(),
            posture,
            num_version_declarations: 0,
        }
    }
}

impl<H: SmtCommandHandler> Default for SmtScriptParser<H> {
    fn default() -> Self {
        Self::new(SmtVersionPosture::default())
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for SmtScriptParser<H> {
    type Result = SmtScriptEnd;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut SmtParseState<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<SmtScriptEnd>, SmtParseError<H::Error>> {
        loop {
            match self.command.parse(handler, resources, cursor)? {
                ControlFlow::Continue(()) => {
                    // the cursor is consumed, the command continues in the next one
                    return Ok(ControlFlow::Continue(()));
                }
                ControlFlow::Break(SmtCommandOutcome::Command) => {
                    // a command has ended: parse the next one
                }
                ControlFlow::Break(SmtCommandOutcome::SetVersion(version, span)) => {
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
                ControlFlow::Break(SmtCommandOutcome::Exit) => {
                    // the exit command ends the script: stop after it
                    // reset the number of version declarations before breaking
                    self.num_version_declarations = 0;
                    return Ok(ControlFlow::Break(SmtScriptEnd::Exit));
                }
                ControlFlow::Break(SmtCommandOutcome::EndOfFile) => {
                    // the end of the input between commands ends the script
                    // reset the number of version declarations before breaking
                    self.num_version_declarations = 0;
                    return Ok(ControlFlow::Break(SmtScriptEnd::EndOfFile));
                }
            }
        }
    }
}

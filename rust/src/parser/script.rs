use std::{fmt, ops::ControlFlow};

use crate::{
    SmtCommandHandler, SmtVersionPosture,
    parser::{
        SmtCommandOutcome, SmtCommandParser, SmtParse, SmtParseError, SmtParseState,
        SmtVersionErrorKind,
    },
    token::{SmtCursor, SmtVersionRefused},
};

/// Parses an SMT-LIB script.
///
/// An SMT-LIB script is a (possibly empty) sequence of commands.
///
/// The parser is a loop over a [`SmtCommandParser`]. If the `(exit)` command is
/// encountered, the parser requests the producer to discard everything after
/// its closing parenthesis.
///
/// The parser returns a unit result on EOF.
pub struct SmtScriptParser<H: SmtCommandHandler> {
    command: SmtCommandParser<H>,
    posture: SmtVersionPosture,
    num_version_declarations: u64,
}

impl<H: SmtCommandHandler> fmt::Debug for SmtScriptParser<H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SmtScriptParser").finish_non_exhaustive()
    }
}

impl<H: SmtCommandHandler> SmtScriptParser<H> {
    /// Creates the parser with the version posture.
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
    type Result = ();

    #[inline]
    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<()>, SmtParseError<H::Error>> {
        loop {
            match self.command.parse(handler, parse_state, cursor)? {
                ControlFlow::Continue(()) => {
                    // the cursor is consumed, the command continues in the next one
                    return Ok(ControlFlow::Continue(()));
                }
                ControlFlow::Break(SmtCommandOutcome::Command) => {
                    // a command has ended: parse the next one
                }
                ControlFlow::Break(SmtCommandOutcome::SetVersion(version)) => {
                    // ensure the posture allows setting a new version
                    // do this before checking the version so the refusal is consistent
                    if let Some(max_declarations) = self.posture.max_declarations()
                        && self.num_version_declarations >= max_declarations
                    {
                        return Err(SmtParseError::version(
                            SmtVersionErrorKind::TooManyDeclarations(max_declarations),
                        ));
                    }
                    // ensure the version itself is allowed by the posture
                    if !self.posture.allowed().contains(&version) {
                        return Err(SmtParseError::version(SmtVersionErrorKind::Unsupported));
                    }
                    // allowed by the posture, try to set version on the cursor
                    if let Err(SmtVersionRefused) = cursor.set_version(version) {
                        // the producer rejected the version
                        return Err(SmtParseError::version(SmtVersionErrorKind::Unsupported));
                    }
                    // allowed by the producer, set version on the handler
                    handler.set_version(version);

                    // success, increase the number of version declarations
                    self.num_version_declarations += 1;
                }
                ControlFlow::Break(SmtCommandOutcome::Exit) => {
                    // tell the cursor to discard the rest of the input
                    // and continue until EOF
                    cursor.discard_rest();
                    return Ok(ControlFlow::Continue(()));
                }
                ControlFlow::Break(SmtCommandOutcome::EndOfFile) => {
                    // the end of the input between commands ends the script
                    // reset the number of version declarations before breaking
                    self.num_version_declarations = 0;
                    return Ok(ControlFlow::Break(()));
                }
            }
        }
    }
}

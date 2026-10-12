use std::ops::ControlFlow;

use crate::{
    SmtCommandHandler,
    parser::{
        SmtCommandOutcome, SmtCommandParser, SmtParse, SmtParseError, SmtParseState,
        SmtSyntaxErrorKind,
    },
    token::{SmtProduce, SmtVersionPosture, SmtVersionRefused},
};

/// Parses an SMT-LIB script: a sequence of commands, each delivered to the
/// command handler as it is parsed.
///
/// The parser is a loop over a [`SmtCommandParser`]. If the `(exit)` command
/// is encountered, the parser requests the producer to discard everything
/// after its closing parenthesis.
///
/// The parser always resets and returns a unit result on EOF.
pub struct SmtScriptParser<H: SmtCommandHandler> {
    command: SmtCommandParser<H>,
    posture: SmtVersionPosture,
    num_version_declarations: u64,
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
    type Result = ();

    #[inline]
    fn parse<C: SmtProduce>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
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
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::TooManyVersionDeclarations(max_declarations),
                        ));
                    }
                    // ensure the version itself is allowed by the posture
                    if !self.posture.allowed().contains(&version) {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::UnsupportedVersion,
                        ));
                    }
                    // allowed by the posture, try to set version on the cursor
                    match cursor.set_version(version) {
                        Ok(()) => {
                            // success, increase the number of version declarations
                            self.num_version_declarations += 1;
                        }
                        Err(SmtVersionRefused) => {
                            // the producer itself does not support the version
                            return Err(SmtParseError::category_error(
                                SmtSyntaxErrorKind::UnsupportedVersion,
                            ));
                        }
                    }
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

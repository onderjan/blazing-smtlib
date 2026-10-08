use std::{convert::Infallible, ops::ControlFlow};

use crate::{
    SmtCommandHandler, SmtSpan, SmtSymbol,
    parser::{SmtParse, SmtParseError, SmtParseState, SmtSyntaxErrorKind, handle_err},
    token::{SmtBatchCursor, SmtReserved, SmtSyntaxToken, SmtTokenCategory, SmtVersion},
};

mod datatype;
mod definition;
mod function;
mod standard;

use standard::{StandardCommandKind, StandardCommandParsers};

/// Parses one SMT-LIB command.
///
/// The parser finishes after every command, returning [`ControlFlow::Break`]
/// with a [`SmtCommandOutcome`] that distinguishes the command `(exit)`
/// and the version-switch command `(set-info :smt-lib-version <version>)`
/// from the others. It also finishes after an EOF while awaiting a command.
/// An EOF inside a command is a syntax error.
///
/// The parser self-resets after finishing.
pub struct SmtCommandParser<H: SmtCommandHandler> {
    state: CommandParserState<H>,
    standard_parsers: StandardCommandParsers<H>,
}

/// Why the command parser finished.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtCommandOutcome {
    /// A command other than special ones was parsed.
    Command,
    /// A version-switch command was parsed.
    SetVersion(SmtVersion, SmtSpan),
    /// The exit command was parsed.
    Exit,
    /// The end of the input was reached before a command.
    EndOfFile,
}

enum CommandParserState<H: SmtCommandHandler> {
    AwaitingCommand,
    CommandOpen,
    Standard(StandardCommandKind),
    Nonstandard(H::NonstandardParser),
}

impl<H: SmtCommandHandler> SmtCommandParser<H> {
    pub fn new() -> Self {
        Self {
            state: CommandParserState::AwaitingCommand,
            standard_parsers: StandardCommandParsers::new(),
        }
    }

    /// Starts a non-standard command named by a symbol.
    ///
    /// A command identified by a symbol is never standard,
    /// as standard command names are reserved words.
    fn start_nonstandard_command(
        handler: &mut H,
        name: SmtSymbol<'_>,
        span: SmtSpan,
    ) -> Result<CommandParserState<H>, SmtParseError<H::Error>> {
        match handler.nonstandard_command(name) {
            Ok(parser) => Ok(CommandParserState::Nonstandard(parser)),
            Err(err) => Err(SmtParseError::handler_error(err, span)),
        }
    }
}

impl<H: SmtCommandHandler> Default for SmtCommandParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for SmtCommandParser<H> {
    type Result = SmtCommandOutcome;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<SmtCommandOutcome>, SmtParseError<H::Error>> {
        // State machine:
        // 1. AwaitingCommand takes:
        //  - either the opening parenthesis and moves to CommandOpen,
        //  - or the end of the input, which finishes.
        // 2. CommandOpen takes the command name and selects the payload parser.
        // 3. Standard and Nonstandard drive the payload parser to finish,
        //    after which the parser goes back to AwaitingCommand.
        while let Some(peeked) = cursor.peek() {
            match &mut self.state {
                CommandParserState::AwaitingCommand => {
                    // we will handle the token here
                    cursor.advance(1);
                    match peeked.category() {
                        SmtTokenCategory::ParenOpen => {
                            // open the command
                            self.state = CommandParserState::CommandOpen;
                        }
                        SmtTokenCategory::EndOfFile => {
                            // end of file here finishes the parser,
                            // which is already in its initial state
                            return Ok(ControlFlow::Break(SmtCommandOutcome::EndOfFile));
                        }
                        _ => {
                            return Err(SmtParseError::category_error(
                                SmtSyntaxErrorKind::ExpectedCommand,
                                peeked.span(),
                            ));
                        }
                    }
                }
                CommandParserState::CommandOpen => {
                    // we will handle the token here
                    cursor.advance(1);
                    // expect the command name
                    self.state = match peeked.syntax(cursor.version()) {
                        SmtSyntaxToken::Reserved(SmtReserved::CommandName(name)) => {
                            // a command-name reserved word names a standard command
                            CommandParserState::Standard(StandardCommandKind::from_reserved(
                                name,
                                cursor.version(),
                            ))
                        }
                        SmtSyntaxToken::Symbol(name) => {
                            // a symbol (even a quoted one spelled like a standard command)
                            // can only name a nonstandard command
                            Self::start_nonstandard_command(handler, name, peeked.span())?
                        }
                        _ => {
                            return Err(SmtParseError::category_error(
                                SmtSyntaxErrorKind::ExpectedCommandName,
                                peeked.span(),
                            ));
                        }
                    };
                }
                CommandParserState::Standard(kind) => {
                    // handle the cursor within the standard payload parsers
                    let kind = *kind;
                    let flow = self
                        .standard_parsers
                        .parse(kind, handler, parse_state, cursor)?;
                    if let ControlFlow::Break(stop) = flow {
                        // the command has ended, resources should be back in pristine state;
                        // we trust our own parsers enough to only assert this in debug mode
                        // and never clear them, which would make them pristine but slow us down
                        debug_assert!(
                            parse_state.is_pristine(),
                            "resources should be pristine after end of standard command {kind:?}"
                        );
                        self.state = CommandParserState::AwaitingCommand;
                        return Ok(ControlFlow::Break(stop));
                    }
                }
                CommandParserState::Nonstandard(parser) => {
                    // handle the cursor within the nonstandard payload parser
                    let flow = parser.parse(handler, parse_state, cursor)?;
                    if let ControlFlow::Break(()) = flow {
                        // the command has ended, resources should be back in pristine state;
                        // we do not trust the library users: assert this in debug mode, always clear
                        debug_assert!(
                            parse_state.is_pristine(),
                            "resources should be pristine after end of non-standard command"
                        );
                        parse_state.clear();
                        // a non-standard command cannot be the exit command
                        self.state = CommandParserState::AwaitingCommand;
                        return Ok(ControlFlow::Break(SmtCommandOutcome::Command));
                    }
                }
            }
        }
        // we consumed the cursor, return
        Ok(ControlFlow::Continue(()))
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for Infallible {
    type Result = ();

    #[inline]
    fn parse(
        &mut self,
        _handler: &mut H,
        _parse_state: &mut SmtParseState<H>,
        _cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<()>, SmtParseError<H::Error>> {
        match *self {}
    }
}

/// Determines how a single command should be handled by a command handler.
pub trait SmtCommandRule<H: SmtCommandHandler> {
    type Parser: SmtParse<H>;

    /// Handles the result of a command.
    fn handle(
        handler: &mut H,
        result: <Self::Parser as SmtParse<H>>::Result,
    ) -> Result<(), H::Error>;
}

/// A parser that processes the payload of a single command (starting after its name).
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub struct SmtCommandPayloadParser<H: SmtCommandHandler, C: SmtCommandRule<H>> {
    parser: C::Parser,
}

impl<H: SmtCommandHandler, C: SmtCommandRule<H>> SmtCommandPayloadParser<H, C> {
    pub fn new(parser: C::Parser) -> Self {
        Self { parser }
    }
}

impl<H: SmtCommandHandler, C: SmtCommandRule<H>> Default for SmtCommandPayloadParser<H, C>
where
    C::Parser: Default,
{
    fn default() -> Self {
        Self::new(C::Parser::default())
    }
}

impl<H: SmtCommandHandler, C: SmtCommandRule<H>> SmtParse<H> for SmtCommandPayloadParser<H, C> {
    type Result = ();

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<()>, SmtParseError<H::Error>> {
        match self.parser.parse(handler, parse_state, cursor)? {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        SmtSpan, SmtSyntaxChecker,
        token::{InnerCategory, SmtToken},
    };

    #[test]
    fn finished_command_parser_parses_the_next_command() {
        let mut handler = SmtSyntaxChecker;
        let mut parser: SmtCommandPayloadParser<SmtSyntaxChecker, standard::CheckSat> =
            SmtCommandPayloadParser::default();

        // a check-sat command body is just the closing parenthesis,
        // so one token finishes the command; the parser is self-restarting
        // after the break, so the next command body parses without a restart
        for _ in 0..2 {
            let span = SmtSpan::new_zero();
            let close = SmtToken::new(&Some((InnerCategory::ParenClose, &[])), &span);
            let flow = parser
                .parse(
                    &mut handler,
                    &mut SmtParseState::new(),
                    &mut SmtBatchCursor::single(SmtVersion::V2_7, close),
                )
                .expect("check-sat closing parenthesis must parse");
            assert!(matches!(flow, ControlFlow::Break(())));
        }
    }
}

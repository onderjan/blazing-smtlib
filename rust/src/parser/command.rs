use std::{convert::Infallible, fmt, ops::ControlFlow};

use crate::{
    SmtCommandHandler, SmtVersion,
    lexicon::{SmtReserved, SmtSymbol},
    parser::{
        SmtParse, SmtParseError, SmtParseState, SmtSyntaxErrorKind, SmtSyntaxExpected, expected,
        handle_err,
    },
    token::{SmtCursor, SmtToken},
};

mod datatype;
mod definition;
mod function;
mod standard;

use standard::{StandardCommandKind, StandardCommandParsers};

/// Parses an SMT-LIB command.
///
/// The parser finishes after every command, returning [`ControlFlow::Break`]
/// with a [`SmtCommandOutcome`] that distinguishes the command `(exit)`
/// and the version-switch command `(set-info :smt-lib-version <version>)`
/// from the others. It also finishes after an EOF while awaiting a command.
/// An EOF inside a command is a syntax error.
pub struct SmtCommandParser<H: SmtCommandHandler> {
    state: CommandParserState<H>,
    standard_parsers: StandardCommandParsers<H>,
}

impl<H: SmtCommandHandler> fmt::Debug for SmtCommandParser<H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SmtCommandParser").finish_non_exhaustive()
    }
}

/// Outcome of parsing a command with [`SmtCommandParser`] (command, version switch, exit,
/// or end of file).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtCommandOutcome {
    /// A command other than special ones was parsed.
    Command,
    /// A version-switch command was parsed.
    SetVersion(SmtVersion),
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
    ) -> Result<CommandParserState<H>, SmtParseError<H::Error>> {
        match handler.nonstandard_command(name) {
            Ok(parser) => Ok(CommandParserState::Nonstandard(parser)),
            Err(err) => Err(SmtParseError::handler(err)),
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
    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
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
                    // consume the peeked token
                    let _ = cursor.next();
                    match cursor.syntax(&peeked) {
                        SmtToken::ParenOpen => {
                            // open the command
                            self.state = CommandParserState::CommandOpen;
                        }
                        SmtToken::EndOfFile => {
                            // end of file here finishes the parser,
                            // which is already in its initial state
                            return Ok(ControlFlow::Break(SmtCommandOutcome::EndOfFile));
                        }
                        _ => {
                            return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Expected(&[
                                expected::PAREN_OPEN,
                                expected::END_OF_FILE,
                            ])));
                        }
                    }
                }
                CommandParserState::CommandOpen => {
                    // consume the peeked token
                    let _ = cursor.next();
                    // expect the command name
                    self.state = match cursor.syntax(&peeked) {
                        SmtToken::Reserved(SmtReserved::CommandName(name)) => {
                            // a command-name reserved word names a standard command
                            CommandParserState::Standard(StandardCommandKind::from_reserved(
                                name,
                                cursor.version(),
                            ))
                        }
                        SmtToken::Symbol(name) => {
                            // a symbol (even a quoted one spelled like a standard command)
                            // can only name a nonstandard command
                            Self::start_nonstandard_command(handler, name)?
                        }
                        _ => {
                            return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Expected(&[
                                SmtSyntaxExpected::CommandName,
                            ])));
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
    fn parse<Z: SmtCursor>(
        &mut self,
        _handler: &mut H,
        _parse_state: &mut SmtParseState<H>,
        _cursor: &mut Z,
    ) -> Result<ControlFlow<()>, SmtParseError<H::Error>> {
        match *self {}
    }
}

/// Handles the result of a command parsed by [`SmtCommandPayloadParser`].
pub trait SmtCommandRule<H: SmtCommandHandler> {
    type Parser: SmtParse<H>;

    /// Handles the result of a command.
    fn handle(
        &mut self,
        handler: &mut H,
        result: <Self::Parser as SmtParse<H>>::Result,
    ) -> Result<(), H::Error>;
}

/// Parses the payload of a single command, starting after its name.
pub struct SmtCommandPayloadParser<H: SmtCommandHandler, R: SmtCommandRule<H>> {
    rule: R,
    parser: R::Parser,
}

impl<H: SmtCommandHandler, R: SmtCommandRule<H>> fmt::Debug for SmtCommandPayloadParser<H, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SmtCommandPayloadParser")
            .finish_non_exhaustive()
    }
}

impl<H: SmtCommandHandler, R: SmtCommandRule<H>> SmtCommandPayloadParser<H, R> {
    pub fn new(rule: R, parser: R::Parser) -> Self {
        Self { rule, parser }
    }

    /// Creates the parser with the rule and its default payload parser.
    pub fn with_rule(rule: R) -> Self
    where
        R::Parser: Default,
    {
        Self::new(rule, R::Parser::default())
    }
}

impl<H: SmtCommandHandler, R: SmtCommandRule<H>> Default for SmtCommandPayloadParser<H, R>
where
    R: Default,
    R::Parser: Default,
{
    fn default() -> Self {
        Self::new(R::default(), R::Parser::default())
    }
}

impl<H: SmtCommandHandler, R: SmtCommandRule<H>> SmtParse<H> for SmtCommandPayloadParser<H, R> {
    type Result = ();

    #[inline]
    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<()>, SmtParseError<H::Error>> {
        match self.parser.parse(handler, parse_state, cursor)? {
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(result) => {
                // the command ends at the last consumed token
                handle_err(self.rule.handle(handler, result))?;
                Ok(ControlFlow::Break(()))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        SmtSyntaxChecker,
        lexer::{InnerCategory, SmtLexerCursor, SmtLexerToken},
        span::SmtSpan,
        token::SingleTokenCursor,
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
            let close = SmtLexerToken::new(&Some((InnerCategory::ParenClose, &[])), &span);
            let cursor = SmtLexerCursor::new(SmtVersion::V2_7, &[], &[]);
            let flow = parser
                .parse(
                    &mut handler,
                    &mut SmtParseState::new(),
                    &mut SingleTokenCursor::new(&cursor, close),
                )
                .expect("check-sat closing parenthesis must parse");
            assert!(
                matches!(flow, ControlFlow::Break(())),
                "check-sat should end at its closing parenthesis"
            );
        }
    }
}

use std::{convert::Infallible, ops::ControlFlow};

use crate::{
    CommandHandler, SmtSpan, SmtSymbolView,
    read::parser::{Parser, ParserError, ParserResources, SyntaxErrorKind, handle_err},
    token::{Reserved, SmtVersion, TokenCursor, TokenKind, TokenType},
};

mod datatype;
mod definition;
mod function;
mod standard;

use standard::{StandardCommandKind, StandardCommandParsers};

/// Parses one SMT-LIB command.
///
/// The parser finishes after every command, returning [`ControlFlow::Break`]
/// with a [`CommandParserStop`] that distinguishes the command `(exit)`
/// and the version-switch command `(set-info :smt-lib-version <version>)`
/// from the others. It also finishes after an EOF while awaiting a command.
/// An EOF inside a command is a syntax error.
///
/// The parser self-resets after finishing.
pub struct CommandParser<H: CommandHandler> {
    state: CommandParserState<H>,
    standard_parsers: StandardCommandParsers<H>,
}

/// Why the command parser finished.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommandParserStop {
    /// A command other than special ones was parsed.
    Command,
    /// A version-switch command was parsed.
    SetVersion(SmtVersion, SmtSpan),
    /// The exit command was parsed.
    ExitCommand,
    /// The end of the input was reached before a command.
    EndOfFile,
}

enum CommandParserState<H: CommandHandler> {
    AwaitingCommand,
    CommandOpen,
    Standard(StandardCommandKind),
    Nonstandard(H::NonstandardParser),
}

impl<H: CommandHandler> CommandParser<H> {
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
        name: SmtSymbolView<'_>,
        span: SmtSpan,
    ) -> Result<CommandParserState<H>, ParserError<H::Error>> {
        match handler.nonstandard_command(name) {
            Ok(parser) => Ok(CommandParserState::Nonstandard(parser)),
            Err(err) => Err(ParserError::handler_error(err, span)),
        }
    }
}

impl<H: CommandHandler> Default for CommandParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler> Parser<H> for CommandParser<H> {
    type Result = CommandParserStop;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut TokenCursor,
    ) -> Result<ControlFlow<CommandParserStop>, ParserError<H::Error>> {
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
                    match peeked.ty() {
                        TokenType::ParenOpen => {
                            // open the command
                            self.state = CommandParserState::CommandOpen;
                        }
                        TokenType::EndOfFile => {
                            // end of file here finishes the parser,
                            // which is already in its initial state
                            return Ok(ControlFlow::Break(CommandParserStop::EndOfFile));
                        }
                        _ => {
                            return Err(ParserError::category_error(
                                SyntaxErrorKind::ExpectedCommand,
                                peeked.span(),
                            ));
                        }
                    }
                }
                CommandParserState::CommandOpen => {
                    // we will handle the token here
                    cursor.advance(1);
                    // expect the command name
                    self.state = match peeked.kind(cursor.version()) {
                        TokenKind::Reserved(Reserved::CommandName(name)) => {
                            // a command-name reserved word names a standard command
                            CommandParserState::Standard(StandardCommandKind::from_reserved(name))
                        }
                        TokenKind::Symbol(name) => {
                            // a symbol (even a quoted one spelled like a standard command)
                            // can only name a nonstandard command
                            Self::start_nonstandard_command(handler, name, peeked.span())?
                        }
                        _ => {
                            return Err(ParserError::category_error(
                                SyntaxErrorKind::ExpectedCommandName,
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
                        .parse(kind, handler, resources, cursor)?;
                    if let ControlFlow::Break(stop) = flow {
                        // the command has ended, resources should be back in pristine state;
                        // we trust our own parsers enough to only assert this in debug mode
                        // and never clear them, which would make them pristine but slow us down
                        debug_assert!(
                            resources.are_pristine(),
                            "resources should be pristine after end of standard command {kind:?}"
                        );
                        self.state = CommandParserState::AwaitingCommand;
                        return Ok(ControlFlow::Break(stop));
                    }
                }
                CommandParserState::Nonstandard(parser) => {
                    // handle the cursor within the nonstandard payload parser
                    let flow = parser.parse(handler, resources, cursor)?;
                    if let ControlFlow::Break(()) = flow {
                        // the command has ended, resources should be back in pristine state;
                        // we do not trust the library users: assert this in debug mode, always clear
                        debug_assert!(
                            resources.are_pristine(),
                            "resources should be pristine after end of non-standard command"
                        );
                        resources.clear();
                        // a non-standard command cannot be the exit command
                        self.state = CommandParserState::AwaitingCommand;
                        return Ok(ControlFlow::Break(CommandParserStop::Command));
                    }
                }
            }
        }
        // we consumed the cursor, return
        Ok(ControlFlow::Continue(()))
    }
}

impl<H: CommandHandler> Parser<H> for Infallible {
    type Result = ();

    #[inline]
    fn parse(
        &mut self,
        _handler: &mut H,
        _resources: &mut ParserResources<H>,
        _cursor: &mut TokenCursor,
    ) -> Result<ControlFlow<()>, ParserError<H::Error>> {
        match *self {}
    }
}

/// Determines how a single command should be handled by a command handler.
pub trait CommandAction<H: CommandHandler> {
    type Parser: Parser<H>;

    /// Handles the result of a command.
    fn handle(handler: &mut H, result: <Self::Parser as Parser<H>>::Result)
    -> Result<(), H::Error>;
}

/// A parser that processes the payload of a single command (starting after its name).
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub struct CommandPayloadParser<H: CommandHandler, C: CommandAction<H>> {
    parser: C::Parser,
}

impl<H: CommandHandler, C: CommandAction<H>> CommandPayloadParser<H, C> {
    pub fn new(parser: C::Parser) -> Self {
        Self { parser }
    }
}

impl<H: CommandHandler, C: CommandAction<H>> Default for CommandPayloadParser<H, C>
where
    C::Parser: Default,
{
    fn default() -> Self {
        Self::new(C::Parser::default())
    }
}

impl<H: CommandHandler, C: CommandAction<H>> Parser<H> for CommandPayloadParser<H, C> {
    type Result = ();

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut TokenCursor,
    ) -> Result<ControlFlow<()>, ParserError<H::Error>> {
        match self.parser.parse(handler, resources, cursor)? {
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
        CheckStandardSyntax, SmtSpan,
        token::{InnerType, Token},
    };

    #[test]
    fn finished_command_parser_parses_the_next_command() {
        let mut handler = CheckStandardSyntax;
        let mut parser: CommandPayloadParser<CheckStandardSyntax, standard::CheckSat> =
            CommandPayloadParser::default();

        // a check-sat command body is just the closing parenthesis,
        // so one token finishes the command; the parser is self-restarting
        // after the break, so the next command body parses without a restart
        for _ in 0..2 {
            let span = SmtSpan::new_zero();
            let close = Token::new(&Some((InnerType::ParenClose, &[])), &span);
            let flow = parser
                .parse(
                    &mut handler,
                    &mut ParserResources::new(),
                    &mut TokenCursor::single(SmtVersion::V2_7, close),
                )
                .expect("check-sat closing parenthesis must parse");
            assert!(matches!(flow, ControlFlow::Break(())));
        }
    }
}

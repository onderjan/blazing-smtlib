use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtSpan, SmtSymbolView,
    read::parser::{
        CommandParsers, Parser, ParserError, ParserResources, StandardCommandKind,
        StandardCommandResult, SyntaxErrorKind,
    },
    token::{Reserved, TokenCursor, TokenKind, TokenType},
};

/// Parses an SMT-LIB script: a sequence of commands, each delivered to the
/// command handler as it is parsed.
///
/// The parser finishes at the exit command, returning [`ControlFlow::Break`];
/// the end of the input is accepted between commands and asks for more.
/// It is back at its start after every command, so one instance parses
/// any number of scripts in turn.
pub struct ScriptParser<H: CommandHandler> {
    state: ScriptParserState<H>,
    command_parsers: CommandParsers<H>,
}

pub(crate) enum ScriptParserState<H: CommandHandler> {
    AwaitingCommand,
    CommandOpen,
    Command(StandardCommandKind),
    NonstandardCommand(H::NonstandardParser),
}

impl<H: CommandHandler> ScriptParser<H> {
    pub fn new() -> Self {
        Self {
            state: ScriptParserState::AwaitingCommand,
            command_parsers: CommandParsers::new(),
        }
    }

    fn handle_command_progress<R>(
        resources: &mut ParserResources<H>,
        flow: ControlFlow<R>,
        standard_kind: Option<StandardCommandKind>,
    ) -> Option<R> {
        let ControlFlow::Break(result) = flow else {
            // still progressing
            return None;
        };

        // the command has ended, resources should be back in pristine state
        if let Some(standard_kind) = standard_kind {
            // we trust ourselves enough to only assert this in debug mode
            // and we will not without clear in release
            debug_assert!(
                resources.are_pristine(),
                "resources should be pristine after end of standard command {standard_kind:?}"
            );
        } else {
            // we do not trust the library users: assert this in debug mode, always clear
            debug_assert!(
                resources.are_pristine(),
                "resources should be pristine after end of non-standard command"
            );
            resources.clear();
        }

        Some(result)
    }

    /// Starts a non-standard command named by a symbol.
    ///
    /// A command identified by a symbol is never standard,
    /// as standard command names are reserved words.
    fn start_nonstandard_command(
        handler: &mut H,
        name: SmtSymbolView<'_>,
        span: SmtSpan,
    ) -> Result<ScriptParserState<H>, ParserError<H::Error>> {
        match handler.nonstandard_command(name) {
            Ok(parser) => Ok(ScriptParserState::NonstandardCommand(parser)),
            Err(err) => Err(ParserError::handler_error(err, span)),
        }
    }
}

impl<H: CommandHandler> Default for ScriptParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler> Parser<H> for ScriptParser<H> {
    type Result = ();

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut TokenCursor,
    ) -> Result<ControlFlow<()>, ParserError<H::Error>> {
        while let Some(peeked) = cursor.peek() {
            match &mut self.state {
                ScriptParserState::AwaitingCommand => {
                    // we will handle the token here
                    cursor.advance(1);
                    match peeked.ty() {
                        TokenType::ParenOpen => {
                            // open the command
                            self.state = ScriptParserState::CommandOpen;
                        }
                        TokenType::EndOfFile => {
                            // end of file here is fine, do not change the state
                            self.state = ScriptParserState::AwaitingCommand;
                        }
                        _ => {
                            return Err(ParserError::category_error(
                                SyntaxErrorKind::ExpectedCommand,
                                peeked.span(),
                            ));
                        }
                    }
                }
                ScriptParserState::CommandOpen => {
                    // we will handle the token here
                    cursor.advance(1);
                    // expect the command name
                    self.state = match resources.arena.token_kind(peeked) {
                        TokenKind::Reserved(Reserved::CommandName(name)) => {
                            // a command-name reserved word names a standard command
                            ScriptParserState::Command(StandardCommandKind::from_reserved(name))
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
                ScriptParserState::Command(kind) => {
                    // handle the cursor within standard command parsers
                    let kind = *kind;
                    let flow = self
                        .command_parsers
                        .parse(kind, handler, resources, cursor)?;
                    if let Some(result) = Self::handle_command_progress(resources, flow, Some(kind))
                    {
                        // the script parser is back at its start after every command
                        self.state = ScriptParserState::AwaitingCommand;
                        if let StandardCommandResult::Exit = result {
                            // the exit command ends the script: stop lexing after it
                            return Ok(ControlFlow::Break(()));
                        }
                    }
                }
                ScriptParserState::NonstandardCommand(parser) => {
                    // handle the cursor within nonstandard command parsers
                    let flow = parser.parse(handler, resources, cursor)?;
                    if let Some(()) = Self::handle_command_progress(resources, flow, None) {
                        // update the state; a non-standard command cannot force an early exit
                        self.state = ScriptParserState::AwaitingCommand;
                    }
                }
            }
        }
        // we consumed the cursor, return
        Ok(ControlFlow::Continue(()))
    }
}

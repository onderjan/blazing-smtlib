use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtSpan, SmtSymbolView,
    read::parser::{
        CommandParsers, Parser, ParserError, ParserResources, StandardCommandKind,
        StandardCommandResult, SyntaxErrorKind,
    },
    token::{Reserved, TokenCursor, TokenHandler, TokenKind, TokenType},
};

pub struct ScriptParser<'a, H: CommandHandler> {
    handler: &'a mut H,
    state: ScriptParserState<H>,
    resources: ParserResources<H>,

    command_parsers: CommandParsers<H>,
}

pub(crate) enum ScriptParserState<H: CommandHandler> {
    AwaitingCommand,
    CommandOpen,
    Command(StandardCommandKind),
    NonstandardCommand(H::NonstandardParser),
}

impl<'a, H: CommandHandler> ScriptParser<'a, H> {
    pub fn new(handler: &'a mut H) -> Self {
        Self {
            handler,
            state: ScriptParserState::AwaitingCommand,
            resources: ParserResources::new(),
            command_parsers: CommandParsers::new(),
        }
    }

    fn handle_command_progress<R>(
        &mut self,
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
                self.resources.are_pristine(),
                "resources should be pristine after end of standard command {standard_kind:?}"
            );
        } else {
            // we do not trust the library users: assert this in debug mode, always clear
            debug_assert!(
                self.resources.are_pristine(),
                "resources should be pristine after end of non-standard command"
            );
            self.resources.clear();
        }

        Some(result)
    }

    /// Starts a non-standard command named by a symbol.
    ///
    /// A command identified by a symbol is never standard,
    /// as standard command names are reserved words.
    pub(super) fn start_nonstandard_command(
        &mut self,
        name: SmtSymbolView<'_>,
        span: SmtSpan,
    ) -> Result<ScriptParserState<H>, ParserError<H::Error>> {
        match self.handler.nonstandard_command(name) {
            Ok(parser) => Ok(ScriptParserState::NonstandardCommand(parser)),
            Err(err) => Err(ParserError::handler_error(err, span)),
        }
    }
}

impl<'a, H: CommandHandler> TokenHandler for ScriptParser<'a, H> {
    type Result = ();
    type Error = ParserError<H::Error>;

    #[inline]
    fn handle_tokens(
        &mut self,
        cursor: &mut TokenCursor<'_>,
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
                    self.state = match self.resources.arena.token_kind(peeked) {
                        TokenKind::Reserved(Reserved::CommandName(name)) => {
                            // a command-name reserved word names a standard command
                            ScriptParserState::Command(StandardCommandKind::from_reserved(name))
                        }
                        TokenKind::Symbol(name) => {
                            // a symbol (even a quoted one spelled like a standard command)
                            // can only name a nonstandard command
                            self.start_nonstandard_command(name, peeked.span())?
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
                    let flow = self.command_parsers.parse(
                        kind,
                        self.handler,
                        &mut self.resources,
                        cursor,
                    )?;
                    if let Some(result) = self.handle_command_progress(flow, Some(kind)) {
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
                    let flow = parser.parse(self.handler, &mut self.resources, cursor)?;
                    if let Some(()) = self.handle_command_progress(flow, None) {
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

use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtSpan,
    token::{Token, TokenHandler, TokenKind},
};

mod category;
mod command;

pub use category::*;
pub use command::*;

#[derive(Debug)]
pub enum ParserErrorKind<E> {
    Category(CategoryParserErrorKind),
    Handler(E),
}

#[derive(Debug)]
pub struct ParserError<E> {
    kind: ParserErrorKind<E>,
    span: SmtSpan,
}

impl<E> ParserError<E> {
    pub(crate) fn new(kind: ParserErrorKind<E>, span: SmtSpan) -> Self {
        Self { kind, span }
    }

    pub(crate) fn handler_error(err: E, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::Handler(err), span)
    }

    pub(crate) fn category_error(err: CategoryParserErrorKind, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::Category(err), span)
    }

    pub fn kind(&self) -> &ParserErrorKind<E> {
        &self.kind
    }

    pub fn span(&self) -> SmtSpan {
        self.span
    }

    pub fn into_kind(self) -> ParserErrorKind<E> {
        self.kind
    }
}

impl<E> From<CategoryParserError> for ParserError<E> {
    fn from(value: CategoryParserError) -> Self {
        let span = value.span();
        Self::new(ParserErrorKind::Category(value.into_kind()), span)
    }
}

pub struct Parser<'a, H: CommandHandler> {
    handler: &'a mut H,
    state: ParserState<H>,

    command_parsers: CommandParsers<H>,
}

pub(crate) enum ParserState<H: CommandHandler> {
    AwaitingCommand,
    CommandOpen,
    Command(StandardCommandKind),
    NonstandardCommand(H::NonstandardParser),
    Exit,
}

impl<'a, H: CommandHandler> Parser<'a, H> {
    pub fn new(handler: &'a mut H) -> Self {
        Self {
            handler,
            state: ParserState::AwaitingCommand,
            command_parsers: CommandParsers::new(),
        }
    }

    fn handle_command_progress(&mut self, flow: ControlFlow<CommandResult>) {
        match flow {
            ControlFlow::Continue(()) => {}
            ControlFlow::Break(CommandResult::EndCommand) => {
                self.state = ParserState::AwaitingCommand;
            }
            ControlFlow::Break(CommandResult::Exit) => {
                self.state = ParserState::Exit;
            }
        }
    }
}

impl<'a, H: CommandHandler> TokenHandler for Parser<'a, H> {
    type Error = ParserError<H::Error>;

    fn handle_token(&mut self, token: Token) -> Result<(), ParserError<H::Error>> {
        let span = token.span();
        match &mut self.state {
            ParserState::AwaitingCommand => {
                match token.kind() {
                    TokenKind::ParenOpen => {
                        // open the command
                        self.state = ParserState::CommandOpen;
                    }
                    TokenKind::EndOfFile => {
                        // end of file here is fine, do not change the state
                        self.state = ParserState::AwaitingCommand;
                    }
                    _ => {
                        return Err(CategoryParserError::new(
                            CategoryParserErrorKind::ExpectedCommand,
                            span,
                        )
                        .into());
                    }
                }
            }
            ParserState::CommandOpen => {
                // expect a symbol identifying the command
                let TokenKind::Symbol(command_name) = token.kind() else {
                    return Err(CategoryParserError::new(
                        CategoryParserErrorKind::ExpectedCommandName,
                        span,
                    )
                    .into());
                };
                self.state = self.start_command(command_name, span)?;
            }
            ParserState::Command(kind) => {
                let flow = self.command_parsers.progress(*kind, self.handler, token)?;
                self.handle_command_progress(flow);
            }
            ParserState::NonstandardCommand(parser) => {
                let flow = parser.progress(self.handler, token)?;
                self.handle_command_progress(flow);
            }
            ParserState::Exit => {
                // no operation on fed tokens
            }
        }
        Ok(())
    }
}

fn handle_err<O, E>(handled: Result<O, E>, span: SmtSpan) -> Result<O, ParserError<E>> {
    match handled {
        Ok(ok) => Ok(ok),
        Err(err) => Err(ParserError::handler_error(err, span)),
    }
}

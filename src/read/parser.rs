use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtHandler, SmtSpan,
    read::lexer::TokenHandler,
    token::{Token, TokenKind},
};

mod category;
mod command;

pub use category::*;
pub use command::*;

pub enum ParserErrorKind<H: SmtHandler + ?Sized> {
    Category(CategoryParserErrorKind),
    Handler(H::Error),
}

pub struct ParserError<H: SmtHandler + ?Sized> {
    kind: ParserErrorKind<H>,
    span: SmtSpan,
}

impl<H: SmtHandler> ParserError<H> {
    pub(crate) fn new(kind: ParserErrorKind<H>, span: SmtSpan) -> Self {
        Self { kind, span }
    }

    pub(crate) fn handler_error(err: H::Error, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::Handler(err), span)
    }

    pub(crate) fn category_error(err: CategoryParserErrorKind, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::Category(err), span)
    }

    pub fn kind(&self) -> &ParserErrorKind<H> {
        &self.kind
    }

    pub fn span(&self) -> SmtSpan {
        self.span
    }

    pub fn into_kind(self) -> ParserErrorKind<H> {
        self.kind
    }
}

impl<H: SmtHandler> From<CategoryParserError> for ParserError<H> {
    fn from(value: CategoryParserError) -> Self {
        let span = value.span();
        Self::new(ParserErrorKind::Category(value.into_kind()), span)
    }
}

pub struct Parser<'a, H: CommandHandler> {
    handler: &'a mut H,
    state: ParserState<H>,
}

pub(crate) enum ParserState<H: CommandHandler> {
    AwaitingCommand,
    CommandOpen,
    Command(CommandParser<H>),
    Exit,
}

impl<'a, H: CommandHandler> Parser<'a, H> {
    pub fn new(handler: &'a mut H) -> Self {
        Self {
            handler,
            state: ParserState::AwaitingCommand,
        }
    }
}

impl<'a, H: CommandHandler> TokenHandler for Parser<'a, H> {
    type Error = ParserError<H>;

    fn handle_token(&mut self, token: Token) -> Result<(), ParserError<H>> {
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
                self.state = ParserState::Command(self.start_command(command_name, span)?);
            }
            ParserState::Command(stage) => match stage.progress(self.handler, token)? {
                ControlFlow::Continue(()) => {}
                ControlFlow::Break(CommandResult::EndCommand) => {
                    self.state = ParserState::AwaitingCommand;
                }
                ControlFlow::Break(CommandResult::Exit) => {
                    self.state = ParserState::Exit;
                }
            },
            ParserState::Exit => {
                // no operation on fed tokens
            }
        }
        Ok(())
    }
}

fn handle_err<O, H: SmtHandler>(
    handled: Result<O, H::Error>,
    span: SmtSpan,
) -> Result<O, ParserError<H>> {
    match handled {
        Ok(ok) => Ok(ok),
        Err(err) => Err(ParserError::handler_error(err, span)),
    }
}

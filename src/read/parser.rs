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
    Category(CategoryErrorKind),
    Handler(E),
}

#[derive(Debug)]
struct ParserErrorInner<E> {
    kind: ParserErrorKind<E>,
    span: SmtSpan,
}

/// Error emitted by a parser, including the error span.
#[derive(Debug)]
pub struct ParserError<E>(Box<ParserErrorInner<E>>);

impl<E> ParserError<E> {
    #[cold]
    #[inline(never)]
    pub(crate) fn new(kind: ParserErrorKind<E>, span: SmtSpan) -> Self {
        // PERFORMANCE: error kind and span are boxed
        // so that parser results are not unnecessarily large
        // this method boxes them, which forces an allocation
        // so it is is marked cold and never-inline
        Self(Box::new(ParserErrorInner { kind, span }))
    }

    pub(crate) fn handler_error(err: E, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::Handler(err), span)
    }

    pub(crate) fn category_error(err: CategoryErrorKind, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::Category(err), span)
    }

    pub fn kind(&self) -> &ParserErrorKind<E> {
        &self.0.kind
    }

    pub fn span(&self) -> SmtSpan {
        self.0.span
    }

    pub fn into_kind(self) -> ParserErrorKind<E> {
        self.0.kind
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

    #[inline]
    fn handle_token(&mut self, token: &Token) -> Result<(), ParserError<H::Error>> {
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
                        return Err(ParserError::category_error(
                            CategoryErrorKind::ExpectedCommand,
                            span,
                        ));
                    }
                }
            }
            ParserState::CommandOpen => {
                // expect a symbol identifying the command
                let TokenKind::Symbol(command_name) = token.kind() else {
                    return Err(ParserError::category_error(
                        CategoryErrorKind::ExpectedCommandName,
                        span,
                    ));
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

use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtSpan,
    token::{Reserved, Token, TokenHandler, TokenKind, TokenType},
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
    resources: ParserResources<H>,

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
}

impl<'a, H: CommandHandler> TokenHandler for Parser<'a, H> {
    type Error = ParserError<H::Error>;

    #[inline]
    fn handle_token(&mut self, token: Token) -> Result<(), ParserError<H::Error>> {
        let span = token.span();
        match &mut self.state {
            ParserState::AwaitingCommand => {
                match token.ty() {
                    TokenType::ParenOpen => {
                        // open the command
                        self.state = ParserState::CommandOpen;
                    }
                    TokenType::EndOfFile => {
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
                // expect the command name
                self.state = match self.resources.store.token_kind(token) {
                    TokenKind::Reserved(Reserved::CommandName(name)) => {
                        // a command-name reserved word names a standard command
                        ParserState::Command(StandardCommandKind::from_reserved(name))
                    }
                    TokenKind::Symbol(name) => {
                        // a symbol (even a quoted one spelled like a standard command)
                        // can only name a nonstandard command
                        self.start_nonstandard_command(name, span)?
                    }
                    _ => {
                        return Err(ParserError::category_error(
                            CategoryErrorKind::ExpectedCommandName,
                            span,
                        ));
                    }
                };
            }
            ParserState::Command(kind) => {
                let kind = *kind;
                let flow = self.command_parsers.progress(
                    kind,
                    self.handler,
                    &mut self.resources,
                    token,
                )?;
                if let Some(result) = self.handle_command_progress(flow, Some(kind)) {
                    self.state = match result {
                        StandardCommandResult::EndCommand => ParserState::AwaitingCommand,
                        StandardCommandResult::Exit => ParserState::Exit,
                    }
                }
            }
            ParserState::NonstandardCommand(parser) => {
                let flow = parser.progress(self.handler, &mut self.resources, token)?;
                if let Some(()) = self.handle_command_progress(flow, None) {
                    // update the state; a non-standard command cannot force an early exit
                    self.state = ParserState::AwaitingCommand;
                }
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

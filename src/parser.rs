use std::ops::ControlFlow;

use crate::{
    CommandHandler,
    api::SmtHandler,
    parser::command::{CommandResult, DynamicCommandParser, ParseCommand},
    token::{Token, TokenKind},
};

mod category;
mod command;

#[derive(Debug)]
pub enum ParserError {
    ExpectedToken(TokenKind),
    ExpectedUnderscore,
    ExpectedSymbol,
    ExpectedKeyword,
    ExpectedOpenOrCloseParen,
    EmptyIdentIndices,
    InvalidIdent,
    InvalidAttributeValue,
    EmptyApplication,
    EmptyLetBindings,
    ExpectedIndexOrCloseParen,
    ExpectedOperator,
    ExpectedSExpr,
    ExpectedIdent,
    ExpectedSort,
    ExpectedSortInner,
    ExpectedTerm,
    ExpectedAttribute,
    ExpectedCommand,
    ExpectedCommandName,
    UnsupportedCommand,
    SortApplicationNotSupported,
    ExpectedLetBinding,
    RequiredIndices,
}

#[derive(Debug)]
pub enum ParserOrHandlerError<H: SmtHandler> {
    ParserError(ParserError),
    HandlerError(H::Error),
}

impl<H: SmtHandler> From<ParserError> for ParserOrHandlerError<H> {
    fn from(value: ParserError) -> Self {
        ParserOrHandlerError::ParserError(value)
    }
}

pub struct Parser<'a, H: CommandHandler> {
    handler: &'a mut H,
    state: ParserState<H>,
}

pub(crate) enum ParserState<H: CommandHandler> {
    AwaitingCommand,
    CommandOpen,
    StandardCommand(DynamicCommandParser<H>),
    Exit,
}

impl<'a, H: CommandHandler> Parser<'a, H> {
    pub fn new(handler: &'a mut H) -> Self {
        Self {
            handler,
            state: ParserState::AwaitingCommand,
        }
    }

    pub fn parse_token(&mut self, token: Token) -> Result<(), ParserOrHandlerError<H>> {
        //eprintln!("Token: {:?}", token);
        let state = std::mem::replace(&mut self.state, ParserState::AwaitingCommand);
        let state = match state {
            ParserState::AwaitingCommand => {
                match token.kind() {
                    TokenKind::ParenOpen => {
                        // open the command
                        ParserState::CommandOpen
                    }
                    TokenKind::EndOfFile => {
                        // end of file here is fine, do not change the state
                        ParserState::AwaitingCommand
                    }
                    _ => {
                        return Err(ParserOrHandlerError::ParserError(
                            ParserError::ExpectedCommand,
                        ));
                    }
                }
            }
            ParserState::CommandOpen => {
                // expect a symbol identifying the command
                let TokenKind::Symbol(command_name) = token.into_kind() else {
                    return Err(ParserError::ExpectedCommand.into());
                };
                ParserState::StandardCommand(self.start_command(command_name.as_view())?)
            }
            ParserState::StandardCommand(mut stage) => match stage.progress(self.handler, token)? {
                ControlFlow::Continue(()) => ParserState::StandardCommand(stage),
                ControlFlow::Break(CommandResult::EndCommand) => ParserState::AwaitingCommand,
                ControlFlow::Break(CommandResult::Exit) => ParserState::Exit,
            },
            ParserState::Exit => {
                // no operation on fed tokens
                ParserState::Exit
            }
        };
        self.state = state;
        Ok(())
    }
}

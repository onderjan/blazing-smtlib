use std::ops::ControlFlow;

use crate::{
    CommandHandler, String8,
    api::SmtHandler,
    parser::command::{CommandBreak, StandardCommand},
    token::Token,
};

mod category;
mod command;

#[derive(Debug)]
pub enum ParserError {
    ExpectedToken(Token),
    ExpectedUnderscore,
    ExpectedSymbol,
    ExpectedKeyword,
    EmptyIdentIndices,
    InvalidIdent,
    InvalidAttributeValue,
    EmptyApplication,
    EmptyLetBindings,
    ExpectedIndexOrCloseParen,
    ExpectedOperator,
    ExpectedSExpr,
    ExpectedSort,
    ExpectedSortInner,
    ExpectedTerm,
    ExpectedCommand,
    ExpectedCommandName,
    UnsupportedCommand,
    SortApplicationNotSupported,
    ExpectedLetBinding,
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
    StandardCommand(StandardCommand<H>),
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
        eprintln!("Token: {:?}", token);
        let state = match &mut self.state {
            ParserState::AwaitingCommand => {
                // expect open paren
                if !matches!(token, Token::ParenOpen) {
                    return Err(ParserOrHandlerError::ParserError(
                        ParserError::ExpectedCommand,
                    ));
                }
                ParserState::CommandOpen
            }
            ParserState::CommandOpen => {
                // expect a symbol identifying the command
                let Token::Symbol(command_name) = token else {
                    return Err(ParserError::ExpectedCommand.into());
                };
                ParserState::StandardCommand(self.start_command(command_name.as_str())?)
            }
            ParserState::StandardCommand(stage) => match stage.progress(self.handler, token)? {
                ControlFlow::Continue(()) => return Ok(()),
                ControlFlow::Break(CommandBreak::EndCommand) => ParserState::AwaitingCommand,
                ControlFlow::Break(CommandBreak::Exit) => ParserState::Exit,
            },
            ParserState::Exit => {
                // no operation on fed tokens
                ParserState::Exit
            }
        };
        self.state = state;
        Ok(())
    }

    fn parse_symbol(&mut self, token: Token) -> Result<H::Symbol, ParserOrHandlerError<H>> {
        if let Token::Symbol(symbol) = token {
            self.parse_symbol_string(symbol)
        } else {
            Err(ParserError::ExpectedSymbol.into())
        }
    }

    fn parse_symbol_string(
        &mut self,
        symbol: String8,
    ) -> Result<H::Symbol, ParserOrHandlerError<H>> {
        self.handler
            .handle_symbol(symbol.as_str())
            .map_err(ParserOrHandlerError::HandlerError)
    }
}

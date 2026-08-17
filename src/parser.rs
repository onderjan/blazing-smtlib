use std::ops::ControlFlow;

use crate::{
    CommandHandler, String8,
    api::SmtHandler,
    parser::{
        command::{CommandActionSort, CommandProgress, CommandStage},
        sort::SortParserState,
    },
    token::Token,
};

mod command;
mod index;
mod sort;
mod term;

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
    ExpectedApplicationOrBinder,
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

struct SortParser<H: SmtHandler> {
    callback: CommandActionSort<H>,
    state: SortParserState<H>,
}

enum ParserState<H: SmtHandler> {
    AwaitingCommand,
    CommandOpen,
    Command(Box<dyn CommandStage<H>>),
    Sort(SortParser<H>),
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
        let mut state = ParserState::AwaitingCommand;
        std::mem::swap(&mut self.state, &mut state);
        let state = match state {
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
                ParserState::Command(self.start_command(command_name.as_str())?)
            }
            ParserState::Command(stage) => self.progress_command(stage, token)?,
            ParserState::Sort(sort_parser) => {
                match sort_parser.state.progress(self.handler, token)? {
                    ControlFlow::Continue(state) => ParserState::Sort(SortParser {
                        callback: sort_parser.callback,
                        state,
                    }),
                    ControlFlow::Break(sort) => progress_state(
                        (sort_parser.callback)(self.handler, sort)
                            .map_err(ParserOrHandlerError::HandlerError)?,
                    ),
                }
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

fn progress_state<H: SmtHandler>(progress: CommandProgress<H>) -> ParserState<H> {
    match progress {
        CommandProgress::Continuation(stage) => ParserState::Command(stage),
        CommandProgress::End => ParserState::AwaitingCommand,
    }
}

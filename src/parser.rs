use std::ops::ControlFlow;

use crate::{
    CommandHandler, String8,
    api::SmtHandler,
    parser::{
        category::{CategoryParserState, sort::SortParserState, term::TermParser},
        command::{CommandProgress, CommandStage},
    },
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

pub(crate) enum ParserState<H: SmtHandler> {
    AwaitingCommand,
    CommandOpen,
    Command(Box<dyn CommandStage<H>>),
    Sort(CategoryParserState<H, SortParserState<H>>),
    Term(CategoryParserState<H, TermParser<H>>),
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
            ParserState::Sort(sort_parser) => match sort_parser.progress(self.handler, token)? {
                ControlFlow::Continue(state) => ParserState::Sort(state),
                ControlFlow::Break(progress) => progress_state(progress),
            },
            ParserState::Term(parser) => match parser.progress(self.handler, token)? {
                ControlFlow::Continue(state) => ParserState::Term(state),
                ControlFlow::Break(progress) => progress_state(progress),
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

fn progress_state<H: SmtHandler>(progress: CommandProgress<H>) -> ParserState<H> {
    match progress {
        CommandProgress::Continuation(stage) => ParserState::Command(stage),
        CommandProgress::EndCommand => ParserState::AwaitingCommand,
        CommandProgress::Exit => ParserState::Exit,
    }
}

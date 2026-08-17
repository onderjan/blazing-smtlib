use std::ops::ControlFlow;

use crate::{CommandHandler, String8, api::SmtHandler, token::Token};

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

#[derive(Debug)]
enum UnprocessedCommand {
    Echo,
    GetOption,
    SetOption,
    GetInfo,
    SetInfo,
    SetLogic,
    DeclareConst,
    DefineFun,
    Assert,
    CheckSat,
    Reset,
    ResetAssertions,
    Exit,
}

#[derive(Debug)]
enum SmtFrame {}

type CommandActionResult<H> =
    Result<ControlFlow<(), Box<dyn CommandStage<H>>>, <H as SmtHandler>::Error>;

type CommandActionCloseParen<H> = Box<dyn FnOnce(&mut H) -> CommandActionResult<H>>;

type CommandActionSymbol<H> = Box<
    dyn FnOnce(
        &mut H,
        <H as SmtHandler>::Symbol,
    ) -> Result<ControlFlow<(), Box<dyn CommandStage<H>>>, <H as SmtHandler>::Error>,
>;

enum CommandAction<H: CommandHandler> {
    CloseParen(CommandActionCloseParen<H>),
    Symbol(CommandActionSymbol<H>),
}

trait CommandStage<H: CommandHandler> {
    fn action(self: Box<Self>) -> CommandAction<H>;
}

enum CommandState<H: SmtHandler> {
    Closed,
    Open,
    Command(Box<dyn CommandStage<H>>),
}

struct SetLogicStage1;

impl<H: CommandHandler> CommandStage<H> for SetLogicStage1 {
    fn action(self: Box<Self>) -> CommandAction<H> {
        CommandAction::Symbol(Box::new(|_handler, symbol| {
            Ok(ControlFlow::Continue(Box::new(SetLogicStage2(symbol))))
        }))
    }
}

struct SetLogicStage2<H: SmtHandler>(H::Symbol);

impl<H: CommandHandler> CommandStage<H> for SetLogicStage2<H> {
    fn action(self: Box<Self>) -> CommandAction<H> {
        CommandAction::CloseParen(Box::new(|handler| {
            handler.command_set_logic(self.0)?;
            Ok(ControlFlow::Break(()))
        }))
    }
}

#[derive(Debug)]
enum Processed<H: SmtHandler> {
    Symbol(H::Symbol),
    Keyword(H::Symbol),
    String(H::String),
    Ident(H::Ident),
    AttributeName(String8),
    SExpr(H::SExpr),
    Attribute(H::Attribute),
    Sort(H::Sort),
    Term(H::Term),
}

pub struct Parser<'a, H: CommandHandler> {
    handler: &'a mut H,
    state: CommandState<H>,
    frames: Vec<SmtFrame>,
    processed: Vec<Processed<H>>,
}

impl<'a, H: CommandHandler> Parser<'a, H> {
    pub fn new(handler: &'a mut H) -> Self {
        Self {
            handler,
            state: CommandState::Closed,
            frames: Vec::new(),
            processed: Vec::new(),
        }
    }

    pub fn handler(&self) -> &H {
        self.handler
    }

    pub fn handler_mut(&mut self) -> &mut H {
        self.handler
    }

    pub fn parse_token(&mut self, token: Token) -> Result<(), ParserOrHandlerError<H>> {
        eprintln!("Token: {:?}", token);
        let mut state = CommandState::Closed;
        std::mem::swap(&mut self.state, &mut state);
        let state = match state {
            CommandState::Closed => {
                // expect open paren
                if !matches!(token, Token::ParenOpen) {
                    return Err(ParserOrHandlerError::ParserError(
                        ParserError::ExpectedCommand,
                    ));
                }
                CommandState::Open
            }
            CommandState::Open => {
                // expect a symbol identifying the command
                let Token::Symbol(command_name) = token else {
                    return Err(ParserError::ExpectedCommand.into());
                };
                match command_name.bytes() {
                    b"set-logic" => CommandState::Command(Box::new(SetLogicStage1)),
                    _ => todo!("Unknown command {:?}", command_name),
                }
            }
            CommandState::Command(stage) => {
                let result = match stage.action() {
                    CommandAction::Symbol(callback) => {
                        let Token::Symbol(symbol) = token else {
                            return Err(ParserError::ExpectedSymbol.into());
                        };
                        let symbol = self
                            .handler
                            .handle_symbol(symbol.as_str())
                            .map_err(ParserOrHandlerError::HandlerError)?;
                        callback(self.handler, symbol)
                    }
                    CommandAction::CloseParen(callback) => {
                        if !matches!(token, Token::ParenClose) {
                            return Err(ParserOrHandlerError::ParserError(
                                ParserError::ExpectedToken(Token::ParenClose),
                            ));
                        }
                        callback(self.handler)
                    }
                }
                .map_err(ParserOrHandlerError::HandlerError)?;

                match result {
                    ControlFlow::Continue(stage) => CommandState::Command(stage),
                    ControlFlow::Break(()) => CommandState::Closed,
                }
            }
        };
        self.state = state;
        Ok(())
    }
}

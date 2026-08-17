use crate::{
    CommandHandler, String8,
    api::SmtHandler,
    parser::command::{CommandProgress, CommandStage},
    token::Token,
};

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
    state: ParserState<H>,
    frames: Vec<SmtFrame>,
    processed: Vec<Processed<H>>,
}

pub enum ParserState<H: SmtHandler> {
    AwaitingCommand,
    CommandOpen,
    Command(Box<dyn CommandStage<H>>),
}

impl<'a, H: CommandHandler> Parser<'a, H> {
    pub fn new(handler: &'a mut H) -> Self {
        Self {
            handler,
            state: ParserState::AwaitingCommand,
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
            ParserState::Command(stage) => match self.progress_command(stage, token)? {
                CommandProgress::Continuation(stage) => ParserState::Command(stage),
                CommandProgress::End => ParserState::AwaitingCommand,
            },
        };
        self.state = state;
        Ok(())
    }
}

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

enum CommandFrame<H: SmtHandler> {
    SetLogic(Option<H::Symbol>),
}

enum CommandState<H: SmtHandler> {
    Closed,
    Open,
    Frame(CommandFrame<H>),
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
                    b"set-logic" => CommandState::Frame(CommandFrame::SetLogic(None)),
                    _ => todo!("Unknown command {:?}", command_name),
                }
            }
            CommandState::Frame(command_frame) => self.parse_command_token(command_frame, token)?,
        };
        self.state = state;
        Ok(())
    }

    fn parse_command_token(
        &mut self,
        command_frame: CommandFrame<H>,
        token: Token,
    ) -> Result<CommandState<H>, ParserOrHandlerError<H>> {
        match command_frame {
            CommandFrame::SetLogic(logic) => match logic {
                None => {
                    let Token::Symbol(logic) = token else {
                        return Err(ParserError::ExpectedSymbol.into());
                    };
                    let logic = self
                        .handler
                        .handle_symbol(logic.as_str())
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    Ok(CommandState::Frame(CommandFrame::SetLogic(Some(logic))))
                }
                Some(logic) => {
                    self.handler
                        .command_set_logic(logic)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    Ok(CommandState::Closed)
                }
            },
        }
    }
}

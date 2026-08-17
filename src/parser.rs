use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtIndex, SmtSort, String8,
    api::SmtHandler,
    parser::command::{CommandActionSort, CommandProgress, CommandStage},
    token::{Reserved, Token},
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

enum IndexedIdentParserState<H: SmtHandler> {
    AwaitingSymbol,
    ProcessingIndices {
        symbol: String8,
        indices: Vec<H::Index>,
    },
}

impl<H: SmtHandler> IndexedIdentParserState<H> {
    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Ident, Self>, ParserOrHandlerError<H>> {
        match self {
            IndexedIdentParserState::AwaitingSymbol => {
                let Token::Symbol(symbol) = token else {
                    return Err(ParserError::ExpectedSymbol.into());
                };

                Ok(ControlFlow::Continue(
                    IndexedIdentParserState::ProcessingIndices {
                        symbol,
                        indices: Vec::new(),
                    },
                ))
            }
            IndexedIdentParserState::ProcessingIndices {
                symbol,
                mut indices,
            } => match token {
                Token::ParenOpen => {
                    todo!("Multiply-indexed token");
                }
                Token::ParenClose => {
                    //todo!("Close indexed ident with {} indices", indices.len());
                    let ident = handler
                        .handle_ident(symbol.as_str(), indices)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    Ok(ControlFlow::Break(ident))
                }
                Token::Numeral(value) => {
                    // numeral index
                    let index = handler
                        .handle_index(SmtIndex::Numeral(value.as_str()))
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    indices.push(index);
                    Ok(ControlFlow::Continue(
                        IndexedIdentParserState::ProcessingIndices { symbol, indices },
                    ))
                }
                Token::Symbol(symbol) => {
                    // symbol index
                    let index = handler
                        .handle_index(SmtIndex::Symbol(symbol.as_str()))
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    indices.push(index);
                    Ok(ControlFlow::Continue(
                        IndexedIdentParserState::ProcessingIndices { symbol, indices },
                    ))
                }
                _ => Err(ParserError::ExpectedIndexOrCloseParen.into()),
            },
        }
    }
}

enum SortParserState<H: SmtHandler> {
    Deciding,
    IndexedIdent(IndexedIdentParserState<H>),
}

impl<H: SmtHandler> SortParserState<H> {
    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Sort, Self>, ParserOrHandlerError<H>> {
        match self {
            SortParserState::Deciding => match token {
                Token::Symbol(symbol) => {
                    let _symbol = handler
                        .handle_symbol(symbol.as_str())
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    todo!("Indexed sort");
                }
                Token::Reserved(Reserved::Underscore) => Ok(ControlFlow::Continue(
                    SortParserState::IndexedIdent(IndexedIdentParserState::AwaitingSymbol),
                )),
                _ => Err(ParserError::ExpectedSortInner.into()),
            },
            SortParserState::IndexedIdent(state) => match state.progress(handler, token)? {
                ControlFlow::Continue(state) => {
                    Ok(ControlFlow::Continue(SortParserState::IndexedIdent(state)))
                }
                ControlFlow::Break(ident) => {
                    let sort = SmtSort::Ident(ident);
                    let sort = handler
                        .handle_sort(sort)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    Ok(ControlFlow::Break(sort))
                }
            },
        }

        //todo!("Progress sort with token {:?}", token)
    }
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

    fn parse_sort(
        &mut self,
        callback: CommandActionSort<H>,
        token: Token,
    ) -> Result<ParserState<H>, ParserOrHandlerError<H>> {
        match token {
            Token::Symbol(symbol) => {
                let ident = self
                    .handler
                    .handle_ident(symbol.as_str(), Vec::new())
                    .map_err(ParserOrHandlerError::HandlerError)?;
                let sort = SmtSort::Ident(ident);
                let sort = self
                    .handler
                    .handle_sort(sort)
                    .map_err(ParserOrHandlerError::HandlerError)?;

                Ok(progress_state(
                    callback(self.handler, sort).map_err(ParserOrHandlerError::HandlerError)?,
                ))
            }
            Token::ParenOpen => Ok(ParserState::Sort(SortParser {
                callback,
                state: SortParserState::Deciding,
            })),
            _ => Err(ParserError::ExpectedSort.into()),
        }
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

use crate::{String8, api::SmtHandler, token::Token};

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
enum Unprocessed {}

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

pub struct Parser<'a, H: SmtHandler> {
    handler: &'a mut H,
    unprocessed: Vec<Unprocessed>,
    processed: Vec<Processed<H>>,
}

impl<'a, H: SmtHandler> Parser<'a, H> {
    pub fn new(handler: &'a mut H) -> Self {
        Self {
            handler,
            unprocessed: Vec::new(),
            processed: Vec::new(),
        }
    }

    pub fn handler(&self) -> &H {
        &self.handler
    }

    pub fn handler_mut(&mut self) -> &mut H {
        &mut self.handler
    }

    pub fn parse_token(&mut self, token: Token) -> Result<(), ParserOrHandlerError<H>> {
        todo!("Parse token")
    }
}

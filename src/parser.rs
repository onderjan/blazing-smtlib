use crate::{SmtIdent, SmtIndex, String8, api::SmtHandler, token::Token};

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
pub enum ParserOrHandlerError<E> {
    ParserError,
    HandlerError(E),
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
struct SExprRest {
    start: usize,
    attribute: bool,
}

#[derive(Debug)]
enum IndexedIdentOuter {
    None,
    Sort,
    Term,
}

#[derive(Debug)]
struct IndexedIdentRest {
    name: String8,
    indices: Vec<SmtIndex>,
    outer: IndexedIdentOuter,
}

#[derive(Debug)]
enum Unprocessed {}

#[derive(Debug)]
enum Processed<H: SmtHandler> {
    Symbol(String8),
    Keyword(String8),
    String(String8),
    Ident(SmtIdent),
    AttributeName(String8),
    SExpr(H::SExpr),
    Attribute(H::Attribute),
    Sort(H::Sort),
    Term(H::Term),
}

pub struct Parser<H: SmtHandler> {
    handler: H,
    unprocessed: Vec<Unprocessed>,
    processed: Vec<Processed<H>>,
}

impl<H: SmtHandler> Parser<H> {
    pub fn new(handler: H) -> Self {
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

    pub fn into_handler(self) -> H {
        self.handler
    }
}

use std::ops::ControlFlow;

use crate::{
    CommandHandler, String8,
    parser::{
        ParserOrHandlerError,
        category::{
            CategoryParser, CloseParenParser, ClosedParser, MultipleParser, PairParser,
            SymbolParser, attribute::ClosedAttributeParser, sort::SortParser, term::TermParser,
        },
    },
    token::Token,
};

pub trait Command<H: CommandHandler> {
    type Parser: CategoryParser<H>;

    fn handle(
        handler: &mut H,
        result: <Self::Parser as CategoryParser<H>>::Result,
    ) -> Result<(), H::Error>;
}

pub struct CommandParser<H: CommandHandler, C: Command<H>>(C::Parser);

impl<H: CommandHandler, C: Command<H>> CommandParser<H, C> {
    pub fn new() -> Self {
        Self(C::Parser::init())
    }

    pub fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>> {
        match self.0.progress(handler, token)? {
            ControlFlow::Continue(parser) => Ok(ControlFlow::Continue(Self(parser))),
            ControlFlow::Break(result) => {
                C::handle(handler, result).map_err(ParserOrHandlerError::HandlerError)?;
                Ok(ControlFlow::Break(()))
            }
        }
    }
}

pub struct CommandSetLogic;

impl<H: CommandHandler> Command<H> for CommandSetLogic {
    type Parser = ClosedParser<H, SymbolParser>;

    fn handle(handler: &mut H, logic: String8) -> Result<(), <H>::Error> {
        handler.command_set_logic(logic)
    }
}

pub struct CommandDeclareConst;

impl<H: CommandHandler> Command<H> for CommandDeclareConst {
    type Parser = ClosedParser<H, PairParser<H, SymbolParser, SortParser>>;

    fn handle(handler: &mut H, result: (String8, H::Sort)) -> Result<(), <H>::Error> {
        let (name, sort) = result;
        handler.command_declare_const(name, sort)
    }
}

pub struct CommandDeclareFun;

impl<H: CommandHandler> Command<H> for CommandDeclareFun {
    type Parser = ClosedParser<
        H,
        PairParser<H, SymbolParser, PairParser<H, MultipleParser<H, SortParser>, SortParser>>,
    >;

    fn handle(
        handler: &mut H,
        result: (String8, (Vec<H::Sort>, H::Sort)),
    ) -> Result<(), <H>::Error> {
        let (name, (param_sorts, result_sort)) = result;
        handler.command_declare_fun(name, param_sorts, result_sort)
    }
}

pub struct CommandAssert;

impl<H: CommandHandler> Command<H> for CommandAssert {
    type Parser = ClosedParser<H, TermParser<H>>;

    fn handle(handler: &mut H, term: H::Term) -> Result<(), <H>::Error> {
        handler.command_assert(term)
    }
}

pub struct CommandCheckSat;

impl<H: CommandHandler> Command<H> for CommandCheckSat {
    type Parser = CloseParenParser;

    fn handle(handler: &mut H, _unit: ()) -> Result<(), <H>::Error> {
        handler.command_check_sat()
    }
}

pub struct CommandExit;

impl<H: CommandHandler> Command<H> for CommandExit {
    type Parser = CloseParenParser;

    fn handle(_handler: &mut H, _unit: ()) -> Result<(), <H>::Error> {
        // do not call anything, exit is handled within parsing
        Ok(())
    }
}

pub struct CommandSetInfo;

impl<H: CommandHandler> Command<H> for CommandSetInfo {
    type Parser = ClosedAttributeParser<H>;

    fn handle(handler: &mut H, attribute: H::Attribute) -> Result<(), <H>::Error> {
        handler.command_set_info(attribute)
    }
}

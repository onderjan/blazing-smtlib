use crate::{
    CommandHandler, SmtSymbol,
    parser::{
        category::{
            CloseParenParser, ClosedParser, MultipleParser, OpenClosedParser, PairParser,
            SymbolParser, attribute::ClosedAttributeParser, sort::SortParser, term::TermParser,
        },
        command::Command,
    },
};

pub struct CommandSetLogic;

impl<H: CommandHandler> Command<H> for CommandSetLogic {
    type Parser = ClosedParser<H, SymbolParser>;

    fn handle(handler: &mut H, logic: SmtSymbol) -> Result<(), <H>::Error> {
        handler.command_set_logic(logic)
    }
}

pub struct CommandDeclareConst;

impl<H: CommandHandler> Command<H> for CommandDeclareConst {
    type Parser = ClosedParser<H, PairParser<H, SymbolParser, SortParser>>;

    fn handle(handler: &mut H, result: (SmtSymbol, H::Sort)) -> Result<(), <H>::Error> {
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
        result: (SmtSymbol, (Vec<H::Sort>, H::Sort)),
    ) -> Result<(), <H>::Error> {
        let (name, (param_sorts, result_sort)) = result;
        handler.command_declare_fun(name, param_sorts, result_sort)
    }
}

pub struct CommandDefineFun;

pub type SortedVarParser<H> = OpenClosedParser<H, PairParser<H, SymbolParser, SortParser>>;
pub type FunctionDefParser<H> = PairParser<
    H,
    SymbolParser,
    PairParser<H, MultipleParser<H, SortedVarParser<H>>, PairParser<H, SortParser, TermParser<H>>>,
>;

impl<H: CommandHandler> Command<H> for CommandDefineFun {
    type Parser = ClosedParser<H, FunctionDefParser<H>>;

    fn handle(
        handler: &mut H,
        result: (SmtSymbol, (Vec<(SmtSymbol, H::Sort)>, (H::Sort, H::Term))),
    ) -> Result<(), <H>::Error> {
        let (name, (param_sorts, (result_sort, definition))) = result;
        handler.command_define_fun(name, param_sorts, result_sort, definition)
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

    fn is_exit() -> bool {
        true
    }
}

pub struct CommandSetInfo;

impl<H: CommandHandler> Command<H> for CommandSetInfo {
    type Parser = ClosedAttributeParser<H>;

    fn handle(handler: &mut H, attribute: H::Attribute) -> Result<(), <H>::Error> {
        handler.command_set_info(attribute)
    }
}

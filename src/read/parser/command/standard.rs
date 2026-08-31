use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtFunctionSignature, SmtSymbol,
    read::parser::{
        CategoryParser, ParserError,
        category::{
            CloseParenParser, ClosedAttributeParser, ClosedParser, MultipleParser,
            OpenClosedParser, PairParser, SortParser, SymbolParser, TermParser,
        },
        command::StandardCommand,
        handle_err,
    },
    token::Token,
};

pub struct CommandSetLogic;

impl<H: CommandHandler> StandardCommand<H> for CommandSetLogic {
    type Parser = ClosedParser<H, SymbolParser>;

    fn handle(handler: &mut H, logic: SmtSymbol) -> Result<(), <H>::Error> {
        handler.command_set_logic(logic)
    }
}

pub struct CommandDeclareConst;

impl<H: CommandHandler> StandardCommand<H> for CommandDeclareConst {
    type Parser = ClosedParser<H, PairParser<H, SymbolParser, SortParser<H>>>;

    fn handle(handler: &mut H, result: (SmtSymbol, H::Sort)) -> Result<(), <H>::Error> {
        let (name, sort) = result;
        handler.command_declare_const(name, sort)
    }
}

pub struct CommandDeclareFun;

impl<H: CommandHandler> StandardCommand<H> for CommandDeclareFun {
    type Parser = ClosedParser<
        H,
        PairParser<H, SymbolParser, PairParser<H, MultipleParser<H, SortParser<H>>, SortParser<H>>>,
    >;

    fn handle(
        handler: &mut H,
        result: (SmtSymbol, (Vec<H::Sort>, H::Sort)),
    ) -> Result<(), <H>::Error> {
        let (name, (param_sorts, result_sort)) = result;
        handler.command_declare_fun(name, param_sorts, result_sort)
    }
}

type SortedVarParser<H> = OpenClosedParser<H, PairParser<H, SymbolParser, SortParser<H>>>;
type DefineFunSignatureParser<H> = PairParser<
    H,
    SymbolParser,
    PairParser<H, MultipleParser<H, SortedVarParser<H>>, SortParser<H>>,
>;

pub enum DefineFunParser<H: CommandHandler> {
    Signature(DefineFunSignatureParser<H>),
    Body(TermParser<H>),
}

impl<H: CommandHandler> DefineFunParser<H> {
    pub fn new() -> Self {
        Self::Signature(DefineFunSignatureParser::new())
    }
}

impl<H: CommandHandler> Default for DefineFunParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler> CategoryParser<H> for DefineFunParser<H> {
    type Result = ();

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserError<H>> {
        let span = token.span();
        let result = match self {
            DefineFunParser::Signature(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => DefineFunParser::Signature(parser),
                ControlFlow::Break((name, (params, result_sort))) => {
                    let signature = SmtFunctionSignature {
                        name,
                        params,
                        result_sort,
                    };

                    handle_err(handler.start_define_fun(signature), span)?;
                    DefineFunParser::Body(TermParser::new())
                }
            },
            DefineFunParser::Body(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => DefineFunParser::Body(parser),
                ControlFlow::Break(term) => {
                    handle_err(handler.end_define_fun(term), span)?;
                    return Ok(ControlFlow::Break(()));
                }
            },
        };
        Ok(ControlFlow::Continue(result))
    }
}

pub struct CommandDefineFun;

impl<H: CommandHandler> StandardCommand<H> for CommandDefineFun {
    type Parser = ClosedParser<H, DefineFunParser<H>>;

    fn handle(_handler: &mut H, _result: ()) -> Result<(), <H>::Error> {
        // already handled by the parser
        Ok(())
    }
}

pub struct CommandAssert;

impl<H: CommandHandler> StandardCommand<H> for CommandAssert {
    type Parser = ClosedParser<H, TermParser<H>>;

    fn handle(handler: &mut H, term: H::Term) -> Result<(), <H>::Error> {
        handler.command_assert(term)
    }
}

pub struct CommandCheckSat;

impl<H: CommandHandler> StandardCommand<H> for CommandCheckSat {
    type Parser = CloseParenParser;

    fn handle(handler: &mut H, _unit: ()) -> Result<(), <H>::Error> {
        handler.command_check_sat()
    }
}

pub struct CommandExit;

impl<H: CommandHandler> StandardCommand<H> for CommandExit {
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

impl<H: CommandHandler> StandardCommand<H> for CommandSetInfo {
    type Parser = ClosedAttributeParser<H>;

    fn handle(handler: &mut H, attribute: H::Attribute) -> Result<(), <H>::Error> {
        handler.command_set_info(attribute)
    }
}

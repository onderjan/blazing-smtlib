use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtFunctionSignature,
    read::parser::{
        CategoryParser, CloseParenParser, KeywordParser, ParserError, StringParser, SymbolParser,
        category::{
            ClosedAttributeParser, ClosedParser, MultipleParser, OpenClosedParser, PairParser,
            SortParser, TermParser,
        },
        command::StandardCommand,
        handle_err,
    },
    token::Token,
};

macro_rules! standard_command {
    ($command:ident, $parser:ty, |$handler:ident, $result:pat_param| $handle:expr) => {
        pub struct $command;

        impl<H: CommandHandler> StandardCommand<H> for $command {
            type Parser = $parser;

            fn handle(
                $handler: &mut H,
                $result: <$parser as CategoryParser<H>>::Result,
            ) -> Result<(), H::Error> {
                $handle
            }
        }
    };
}

// standard parsers used, handler called at the end
standard_command!(CommandSetLogic, ClosedParser<H, SymbolParser>,
    |handler, logic| handler.command_set_logic(logic));
standard_command!(CommandDeclareConst,
    ClosedParser<H, PairParser<H, SymbolParser, SortParser<H>>>,
    |handler, (name,sort)| handler.command_declare_const(name, sort)
);
standard_command!(CommandDeclareFun,
    ClosedParser<H, PairParser<H, SymbolParser,
        PairParser<H, MultipleParser<H, SortParser<H>>, SortParser<H>>>>,
    |handler, (name, (param_sorts, result_sort))|
        handler.command_declare_fun(name, param_sorts, result_sort));
standard_command!(CommandAssert, ClosedParser<H, TermParser<H>>,
    |handler, term| handler.command_assert(term)
);
standard_command!(CommandCheckSat, CloseParenParser, |handler, ()| handler
    .command_check_sat());
standard_command!(
    CommandSetInfo,
    ClosedAttributeParser<H>,
    |handler, attribute| handler.command_set_info(attribute)
);
standard_command!(CommandEcho, ClosedParser<H, StringParser>,
    |handler, value| handler.command_echo(value));
standard_command!(CommandGetOption, ClosedParser<H, KeywordParser>,
    |handler, option| handler.command_get_option(option));
standard_command!(
    CommandSetOption,
    ClosedAttributeParser<H>,
    |handler, option| handler.command_set_option(option)
);
standard_command!(CommandGetInfo, ClosedParser<H, KeywordParser>,
    |handler, keyword| handler.command_get_info(keyword));
standard_command!(CommandReset, CloseParenParser, |handler, ()| handler
    .command_reset());
standard_command!(CommandResetAssertions, CloseParenParser, |handler, ()| {
    handler.command_reset_assertions()
});

// the handler is called by the custom parser
standard_command!(CommandDefineFun, ClosedParser<H, DefineFunParser<H>>,
    |_handler, ()| Ok(()));

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

use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtFunctionSignature, SmtSymbol,
    read::parser::{
        CategoryParser, CloseParenParser, CommandParser, CommandResult, KeywordParser,
        ParenMultipleParser, ParserError, SortedVarParser, StringParser, SymbolParser,
        category::{ClosedAttributeParser, ClosedParser, PairParser, SortParser, TermParser},
        command::{CommandAction, ParseCommand},
        handle_err,
    },
    token::Token,
};

macro_rules! standard_commands {
    ($($name:literal => $field:ident: $kind:ident(
        $parser:ty,
        |$handler:ident, $result:pat_param| $handle:expr
        $(, $is_exit:ident)?
    )),* $(,)?) => {
        $(
            pub(super) struct $kind;

            impl<H: CommandHandler> CommandAction<H> for $kind {
                type Parser = $parser;

                fn handle(
                    $handler: &mut H,
                    $result: <$parser as CategoryParser<H>>::Result,
                ) -> Result<(), H::Error> {
                    $handle
                }

                $(fn $is_exit() -> bool {
                    true
                })?
            }
        )*

        /// Identifies a standard command.
        #[derive(Clone, Copy)]
        pub(crate) enum StandardCommandKind {
            $($kind,)*
        }

        impl StandardCommandKind {
            pub fn from_name(name: &[u8]) -> Option<Self> {
                match name {
                    $($name => Some(Self::$kind),)*
                    _ => None,
                }
            }
        }

        /// A struct containing all command parsers.
        ///
        /// All parsers are persistent to avoid dropping buffers.
        pub(crate) struct CommandParsers<H: CommandHandler> {
            $($field: CommandParser<H, $kind>,)*
        }

        impl<H: CommandHandler> CommandParsers<H> {
            pub fn new() -> Self {
                Self {
                    $($field: CommandParser::new(),)*
                }
            }
            pub fn restart(&mut self, kind: StandardCommandKind) {
                match kind {
                    $(StandardCommandKind::$kind => self.$field.restart(),)*
                }
            }
            pub fn progress(
                &mut self,
                kind: StandardCommandKind,
                handler: &mut H,
                token: Token,
            ) -> Result<ControlFlow<CommandResult, ()>, ParserError<H::Error>> {
                match kind {
                    $(StandardCommandKind::$kind => self.$field.progress(handler, token),)*
                }
            }
        }

        impl<H: CommandHandler> Default for CommandParsers<H> {
            fn default() -> Self {
                Self::new()
            }
        }
    };
}

standard_commands! {
    b"set-logic" => set_logic: SetLogic(
        ClosedParser<H, SymbolParser>,
        |handler, logic| handler.command_set_logic(logic)),
    b"declare-const" => declare_const: DeclareConst(
        ClosedParser<H, PairParser<H, SymbolParser, SortParser<H>>>,
        |handler, (name, sort)| handler.command_declare_fun(name, Vec::new(), sort)),
    b"declare-fun" => declare_fun: DeclareFun(
        ClosedParser<H, PairParser<H, SymbolParser,
            PairParser<H, ParenMultipleParser<H, SortParser<H>>, SortParser<H>>>>,
        |handler, (name, (param_sorts, result_sort))|
            handler.command_declare_fun(name, param_sorts, result_sort)),
    b"define-const" => define_const: DefineConst(
        ClosedParser<H, DefineFunParser<H, true>>,
        |_handler, ()| {
            // handler calls are done by the DefineFunParser
            Ok(())
        }),
    b"define-fun" => define_fun: DefineFun(
        ClosedParser<H, DefineFunParser<H, false>>,
        |_handler, ()| {
            // handler calls are done by the DefineFunParser
            Ok(())
        }),
    b"assert" => assert: Assert(
        ClosedParser<H, TermParser<H>>,
        |handler, term| handler.command_assert(term)),
    b"check-sat" => check_sat: CheckSat(
        CloseParenParser,
        |handler, ()| handler.command_check_sat(Vec::new())),
    b"check-sat-assuming" => check_sat_assuming: CheckSatAssuming(
        ClosedParser<H, ParenMultipleParser<H, TermParser<H>>>,
        |handler, assuming| handler.command_check_sat(assuming)),
    b"exit" => exit: Exit(
        CloseParenParser,
        |handler, ()| handler.command_exit(), is_exit),
    b"set-info" => set_info: SetInfo(
        ClosedAttributeParser<H>,
        |handler, attribute| handler.command_set_info(attribute)),
    b"echo" => echo: Echo(
        ClosedParser<H, StringParser>,
        |handler, value| handler.command_echo(value)),
    b"get-option" => get_option: GetOption(
        ClosedParser<H, KeywordParser>,
        |handler, option| handler.command_get_option(option)),
    b"set-option" => set_option: SetOption(
        ClosedAttributeParser<H>,
        |handler, option| handler.command_set_option(option)),
    b"get-info" => get_info: GetInfo(
        ClosedParser<H, KeywordParser>,
        |handler, keyword| handler.command_get_info(keyword)),
    b"reset" => reset: Reset(
        CloseParenParser,
        |handler, ()| handler.command_reset()),
    b"reset-assertions" => reset_assertions: ResetAssertions(
        CloseParenParser,
        |handler, ()| handler.command_reset_assertions()),
}

enum DefineFunParserState<H: CommandHandler> {
    Name,
    Params {
        name: SmtSymbol,
    },
    ResultSort {
        name: SmtSymbol,
        params: Vec<(SmtSymbol, H::Sort)>,
    },
    Body,
}

pub(super) struct DefineFunParser<H: CommandHandler, const IS_CONST: bool> {
    state: DefineFunParserState<H>,

    name_parser: SymbolParser,
    param_sorts_parser: ParenMultipleParser<H, SortedVarParser<H>>,
    result_sort_parser: SortParser<H>,
    body_parser: TermParser<H>,
}

impl<H: CommandHandler, const IS_CONST: bool> DefineFunParser<H, IS_CONST> {
    pub fn new() -> Self {
        Self {
            state: DefineFunParserState::Name,

            name_parser: SymbolParser::new(),
            param_sorts_parser: ParenMultipleParser::new(),
            result_sort_parser: SortParser::new(),
            body_parser: TermParser::new(),
        }
    }
}

impl<H: CommandHandler, const IS_CONST: bool> Default for DefineFunParser<H, IS_CONST> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler, const IS_CONST: bool> CategoryParser<H> for DefineFunParser<H, IS_CONST> {
    type Result = ();

    fn restart(&mut self) {
        self.state = DefineFunParserState::Name;

        self.name_parser.restart();
        self.param_sorts_parser.restart();
        self.result_sort_parser.restart();
        self.body_parser.restart();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        let span = token.span();
        let state = std::mem::replace(&mut self.state, DefineFunParserState::Name);
        let state = match state {
            DefineFunParserState::Name => {
                // parse name
                match self.name_parser.progress(handler, token)? {
                    ControlFlow::Continue(()) => DefineFunParserState::Name,
                    ControlFlow::Break(name) => {
                        if IS_CONST {
                            // this is `define-const`, has no params
                            // move straight to result sort parsing
                            let params = Vec::new();
                            DefineFunParserState::ResultSort { name, params }
                        } else {
                            // this is `define-fun`
                            // move to params parsing
                            DefineFunParserState::Params { name }
                        }
                    }
                }
            }
            DefineFunParserState::Params { name } => {
                // parse param sorts
                match self.param_sorts_parser.progress(handler, token)? {
                    ControlFlow::Continue(()) => DefineFunParserState::Params { name },
                    ControlFlow::Break(params) => {
                        // move to result sort parsing
                        DefineFunParserState::ResultSort { name, params }
                    }
                }
            }
            DefineFunParserState::ResultSort { name, params } => {
                // parse result sort
                match self.result_sort_parser.progress(handler, token)? {
                    ControlFlow::Continue(()) => DefineFunParserState::ResultSort { name, params },
                    ControlFlow::Break(result_sort) => {
                        // start the function definition body
                        let signature = SmtFunctionSignature {
                            name,
                            params,
                            result_sort,
                        };

                        handle_err(handler.start_define_fun(signature), span)?;

                        // move to body parsing
                        DefineFunParserState::Body
                    }
                }
            }
            DefineFunParserState::Body => {
                // parse body term
                match self.body_parser.progress(handler, token)? {
                    ControlFlow::Continue(()) => DefineFunParserState::Body,
                    ControlFlow::Break(term) => {
                        // end the function definition body
                        handle_err(handler.end_define_fun(term), span)?;

                        // reset to initial state and return
                        self.state = DefineFunParserState::Name;
                        return Ok(ControlFlow::Break(()));
                    }
                }
            }
        };
        self.state = state;
        Ok(ControlFlow::Continue(()))
    }
}

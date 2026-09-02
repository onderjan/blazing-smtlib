use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtFunctionSignature,
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
            pub struct $kind;

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
        |handler, (name, sort)| handler.command_declare_const(name, sort)),
    b"declare-fun" => declare_fun: DeclareFun(
        ClosedParser<H, PairParser<H, SymbolParser,
            PairParser<H, ParenMultipleParser<H, SortParser<H>>, SortParser<H>>>>,
        |handler, (name, (param_sorts, result_sort))|
            handler.command_declare_fun(name, param_sorts, result_sort)),
    b"define-fun" => define_fun: DefineFun(
        ClosedParser<H, DefineFunParser<H>>,
        |_handler, ()| Ok(())),
    b"assert" => assert: Assert(
        ClosedParser<H, TermParser<H>>,
        |handler, term| handler.command_assert(term)),
    b"check-sat" => check_sat: CheckSat(
        CloseParenParser,
        |handler, ()| handler.command_check_sat()),
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

type DefineFunSignatureParser<H> = PairParser<
    H,
    SymbolParser,
    PairParser<H, ParenMultipleParser<H, SortedVarParser<H>>, SortParser<H>>,
>;

pub struct DefineFunParser<H: CommandHandler> {
    parse_signature: bool,

    signature_parser: DefineFunSignatureParser<H>,
    body_parser: TermParser<H>,
}

impl<H: CommandHandler> DefineFunParser<H> {
    pub fn new() -> Self {
        Self {
            parse_signature: true,

            signature_parser: DefineFunSignatureParser::new(),
            body_parser: TermParser::new(),
        }
    }
}

impl<H: CommandHandler> Default for DefineFunParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler> CategoryParser<H> for DefineFunParser<H> {
    type Result = ();

    fn restart(&mut self) {
        self.parse_signature = true;

        self.signature_parser.restart();
        self.body_parser.restart();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        let span = token.span();
        if self.parse_signature {
            if let ControlFlow::Break((name, (params, result_sort))) =
                self.signature_parser.progress(handler, token)?
            {
                let signature = SmtFunctionSignature {
                    name,
                    params,
                    result_sort,
                };

                handle_err(handler.start_define_fun(signature), span)?;
                self.parse_signature = false;
            }
        } else {
            if let ControlFlow::Break(term) = self.body_parser.progress(handler, token)? {
                handle_err(handler.end_define_fun(term), span)?;
                self.parse_signature = true;

                return Ok(ControlFlow::Break(()));
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

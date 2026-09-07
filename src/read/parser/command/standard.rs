use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtFunctionSignature, SmtSymbol,
    read::parser::{
        CategoryParser, CloseParenParser, CommandParser, CommandResult, KeywordParser,
        NumeralParser, ParenMultipleParser, ParserError, SortedVarParser, StringParser,
        SymbolParser,
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
    b"declare-sort" => declare_sort: DeclareSort(
        ClosedParser<H, PairParser<H, SymbolParser, NumeralParser>>,
        |handler, (name, arity)| handler.command_declare_sort(name, arity)),
    b"declare-sort-parameter" => declare_sort_parameter: DeclareSortParameter(
        ClosedParser<H, SymbolParser>,
        |handler, name| handler.command_declare_sort_parameter(name)),
    b"declare-const" => declare_const: DeclareConst(
        ClosedParser<H, PairParser<H, SymbolParser, SortParser<H>>>,
        |handler, (name, sort)| handler.command_declare_fun(name, Vec::new(), sort)),
    b"declare-fun" => declare_fun: DeclareFun(
        ClosedParser<H, PairParser<H, SymbolParser,
            PairParser<H, ParenMultipleParser<H, SortParser<H>>, SortParser<H>>>>,
        |handler, (name, (param_sorts, result_sort))|
            handler.command_declare_fun(name, param_sorts, result_sort)),
    b"define-sort" => define_sort: DefineSort(
        ClosedParser<H, DefinitionParser<H, DefineSort>>,
        |_handler, ()| Ok(())),
    b"define-const" => define_const: DefineConst(
        ClosedParser<H, DefinitionParser<H, DefineConst>>,
        |_handler, ()| Ok(())),
    b"define-fun" => define_fun: DefineFun(
        ClosedParser<H, DefinitionParser<H, DefineFun>>,
        |_handler, ()| Ok(())),
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
    b"push" => push: Push(
        ClosedParser<H,NumeralParser>,
        |handler, amount| handler.command_push(amount)),
    b"pop" => pop: Pop(
        ClosedParser<H,NumeralParser>,
        |handler, amount| handler.command_pop(amount)),
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

/// A definition where a signature is followed by a body.
///
/// The handler must know the signature before starting the body.
///
/// The commands using a definition parser do not call the
/// handler after ending, as everything is handled by the parser.
pub(super) trait Definition<H: CommandHandler> {
    type Signature: CategoryParser<H>;
    type Body: CategoryParser<H>;

    /// Start is invoked before the first definition body token.
    fn start(
        handler: &mut H,
        signature: <Self::Signature as CategoryParser<H>>::Result,
    ) -> Result<(), H::Error>;

    /// End is invoked when the last definition body token is processed.
    fn end(
        handler: &mut H,
        body: <Self::Body as CategoryParser<H>>::Result,
    ) -> Result<(), H::Error>;
}

impl<H: CommandHandler> Definition<H> for DefineConst {
    type Signature = PairParser<H, SymbolParser, SortParser<H>>;
    type Body = TermParser<H>;

    fn start(handler: &mut H, signature: (SmtSymbol, H::Sort)) -> Result<(), H::Error> {
        let (name, result_sort) = signature;
        let signature = SmtFunctionSignature {
            name,
            params: Vec::new(),
            result_sort,
        };
        handler.start_define_fun(signature)
    }

    fn end(handler: &mut H, term: H::Term) -> Result<(), H::Error> {
        handler.end_define_fun(term)
    }
}

impl<H: CommandHandler> Definition<H> for DefineFun {
    type Signature = PairParser<
        H,
        SymbolParser,
        PairParser<H, ParenMultipleParser<H, SortedVarParser<H>>, SortParser<H>>,
    >;
    type Body = TermParser<H>;

    fn start(
        handler: &mut H,
        signature: (SmtSymbol, (Vec<(SmtSymbol, H::Sort)>, H::Sort)),
    ) -> Result<(), H::Error> {
        let (name, (params, result_sort)) = signature;
        let signature = SmtFunctionSignature {
            name,
            params,
            result_sort,
        };
        handler.start_define_fun(signature)
    }

    fn end(handler: &mut H, term: H::Term) -> Result<(), H::Error> {
        handler.end_define_fun(term)
    }
}

impl<H: CommandHandler> Definition<H> for DefineSort {
    type Signature = PairParser<H, SymbolParser, ParenMultipleParser<H, SymbolParser>>;
    type Body = SortParser<H>;

    fn start(handler: &mut H, signature: (SmtSymbol, Vec<SmtSymbol>)) -> Result<(), H::Error> {
        let (name, params) = signature;
        handler.start_define_sort(name, params)
    }

    fn end(handler: &mut H, sort: H::Sort) -> Result<(), H::Error> {
        handler.end_define_sort(sort)
    }
}

enum DefinitionParserState {
    Signature,
    Body,
}

/// Parser of a definition that has a signature followed by a body.
///
/// The commands using this parser do not call the
/// handler after ending, as everything is handled by the parser.
pub(super) struct DefinitionParser<H: CommandHandler, D: Definition<H>> {
    state: DefinitionParserState,
    signature_parser: D::Signature,
    body_parser: D::Body,
}

impl<H: CommandHandler, D: Definition<H>> DefinitionParser<H, D> {
    pub fn new() -> Self {
        Self {
            state: DefinitionParserState::Signature,
            signature_parser: D::Signature::default(),
            body_parser: D::Body::default(),
        }
    }
}

impl<H: CommandHandler, D: Definition<H>> Default for DefinitionParser<H, D> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler, D: Definition<H>> CategoryParser<H> for DefinitionParser<H, D> {
    type Result = ();

    fn restart(&mut self) {
        self.state = DefinitionParserState::Signature;
        self.signature_parser.restart();
        self.body_parser.restart();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        let span = token.span();
        match self.state {
            DefinitionParserState::Signature => {
                // parse the signature
                if let ControlFlow::Break(signature) =
                    self.signature_parser.progress(handler, token)?
                {
                    // start the body in the handler and move to parsing the body
                    handle_err(D::start(handler, signature), span)?;
                    self.state = DefinitionParserState::Body;
                }
            }
            DefinitionParserState::Body => {
                // parse the body
                if let ControlFlow::Break(body) = self.body_parser.progress(handler, token)? {
                    // end the body in the handler, reset, and break
                    handle_err(D::end(handler, body), span)?;
                    self.state = DefinitionParserState::Signature;
                    return Ok(ControlFlow::Break(()));
                }
            }
        }

        Ok(ControlFlow::Continue(()))
    }
}

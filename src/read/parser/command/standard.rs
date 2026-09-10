use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtFunctionSignature, SmtSymbol,
    read::parser::{
        CategoryErrorKind, CategoryParser, CloseParenParser, CommandParser, CommandResult,
        KeywordParser, NumeralParser, ParenMultipleParser, ParserError, ParserResources,
        StringParser, SymbolParser,
        category::{ClosedAttributeParser, ClosedParser, PairParser, SortParser, TermParser},
        command::{
            CommandAction, ParseCommand,
            datatype::{DeclareDatatypeParser, DeclareDatatypesParser},
            definition::{Definition, DefinitionParser},
            function::{DefineFunsRecParser, FunctionSignatureParser, RecursiveBodyParser},
        },
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
        #[derive(Clone, Copy, Debug)]
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
                    $($field: CommandParser::default(),)*
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
                resources: &mut ParserResources,
                token: &Token,
            ) -> Result<ControlFlow<CommandResult, ()>, ParserError<H::Error>> {
                match kind {
                    $(StandardCommandKind::$kind => self.$field.progress(handler, resources, token),)*
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
    b"declare-datatype" => declare_datatype: DeclareDatatype(
        ClosedParser<H, DeclareDatatypeParser<H>>,
        |_handler, ()| Ok(())),
    b"declare-datatypes" => declare_datatypes: DeclareDatatypes(
        ClosedParser<H, DeclareDatatypesParser<H>>,
        |_handler, ()| Ok(())),
    b"define-sort" => define_sort: DefineSort(
        ClosedParser<H, DefinitionParser<H, DefineSort>>,
        |_handler, ()| Ok(())),
    b"define-const" => define_const: DefineConst(
        ClosedParser<H, DefinitionParser<H, DefineConst>>,
        |_handler, ()| Ok(())),
    b"define-fun" => define_fun: DefineFun(
        ClosedParser<H, DefinitionParser<H, DefineFun>>,
        |_handler, ()| Ok(())),
    b"define-fun-rec" => define_fun_rec: DefineFunRec(
        ClosedParser<H, DefinitionParser<H, DefineFunRec>>,
        |_handler, ()| Ok(())),
    b"define-funs-rec" => define_funs_rec: DefineFunsRec(
        ClosedParser<H, DefineFunsRecParser<H>>,
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
    b"get-value" => get_value: GetValue(
        ClosedParser<H,GetValueParser<H>>,
        |handler, terms| handler.command_get_value(terms)),
    b"reset" => reset: Reset(
        CloseParenParser,
        |handler, ()| handler.command_reset()),
    b"reset-assertions" => reset_assertions: ResetAssertions(
        CloseParenParser,
        |handler, ()| handler.command_reset_assertions()),
    b"get-assertions" => get_assertions: GetAssertions(
        CloseParenParser,
        |handler, ()| handler.command_get_assertions()),
    b"get-assignment" => get_assignment: GetAssignment(
        CloseParenParser,
        |handler, ()| handler.command_get_assignment()),
    b"get-model" => get_model: GetModel(
        CloseParenParser,
        |handler, ()| handler.command_get_model()),
    b"get-proof" => get_proof: GetProof(
        CloseParenParser,
        |handler, ()| handler.command_get_proof()),
    b"get-unsat-assumptions" => get_unsat_assumptions: GetUnsatAssumptions(
        CloseParenParser,
        |handler, ()| handler.command_get_unsat_assumptions()),
    b"get-unsat-core" => get_unsat_core: GetUnsatCore(
        CloseParenParser,
        |handler, ()| handler.command_get_unsat_core()),
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
    type Signature = FunctionSignatureParser<H>;
    type Body = TermParser<H>;

    fn start(handler: &mut H, signature: SmtFunctionSignature<H>) -> Result<(), H::Error> {
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

impl<H: CommandHandler> Definition<H> for DefineFunRec {
    type Signature = FunctionSignatureParser<H>;
    type Body = RecursiveBodyParser<H>;

    fn start(handler: &mut H, signature: SmtFunctionSignature<H>) -> Result<(), H::Error> {
        handler.start_define_funs_rec(vec![signature])
    }

    fn end(handler: &mut H, _: ()) -> Result<(), H::Error> {
        handler.end_define_funs_rec()
    }
}

/// A parser for parameters of `get-value`: a non-empty list of terms.
pub(super) struct GetValueParser<H: CommandHandler> {
    inner: ParenMultipleParser<H, TermParser<H>>,
}

impl<H: CommandHandler> GetValueParser<H> {
    fn new() -> Self {
        Self {
            inner: ParenMultipleParser::default(),
        }
    }
}

impl<H: CommandHandler> Default for GetValueParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler> CategoryParser<H> for GetValueParser<H> {
    type Result = Vec<H::Term>;

    fn restart(&mut self) {
        self.inner.restart();
    }

    #[inline]
    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources,
        token: &Token,
    ) -> Result<ControlFlow<Vec<H::Term>, ()>, ParserError<H::Error>> {
        let span = token.span();
        match self.inner.progress(handler, resources, token)? {
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(terms) => {
                // ensure there is at least one term
                if terms.is_empty() {
                    return Err(ParserError::category_error(
                        CategoryErrorKind::EmptyGetValueTerms,
                        span,
                    ));
                }
                Ok(ControlFlow::Break(terms))
            }
        }
    }
}

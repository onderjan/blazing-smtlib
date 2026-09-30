use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtFunctionSignature, SmtSymbol,
    read::parser::{
        CloseParenParser, CommandParser, KeywordParser, NumeralParser, ParenMultipleParser, Parser,
        ParserError, ParserResources, StringParser, SymbolParser, SyntaxErrorKind,
        category::{ClosedAttributeParser, ClosedParser, PairParser, SortParser, TermParser},
        command::{
            CommandAction,
            datatype::{DeclareDatatypeParser, DeclareDatatypesParser},
            definition::{Definition, DefinitionParser},
            function::{DefineFunsRecParser, FunctionSignatureParser, RecursiveBodyParser},
        },
    },
    token::{CommandNameReserved, TokenCursor},
};

pub enum StandardCommandResult {
    EndCommand,
    Exit,
}

/// Defines the standard commands, each named like its variant of
/// [`CommandNameReserved`], which the command kinds are mapped from.
macro_rules! standard_commands {
    ($($field:ident: $kind:ident(
        $parser:ty,
        |$handler:ident, $result:pat_param| $handle:expr
    )),* $(,)?) => {
        $(
            pub(super) struct $kind;

            impl<H: CommandHandler> CommandAction<H> for $kind {
                type Parser = $parser;

                fn handle(
                    $handler: &mut H,
                    $result: <$parser as Parser<H>>::Result,
                ) -> Result<(), H::Error> {
                    $handle
                }
            }
        )*

        /// Identifies a standard command.
        #[derive(Clone, Copy, Debug)]
        pub(crate) enum StandardCommandKind {
            $($kind,)*
        }

        impl StandardCommandKind {
            /// The command named by the reserved word.
            #[inline]
            pub fn from_reserved(name: CommandNameReserved) -> Self {
                match name {
                    $(CommandNameReserved::$kind => Self::$kind,)*
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
            pub fn progress_all(
                &mut self,
                kind: StandardCommandKind,
                handler: &mut H,
                resources: &mut ParserResources<H>,
                cursor: &mut TokenCursor<'_>,
            ) -> Result<ControlFlow<StandardCommandResult, ()>, ParserError<H::Error>> {
                let flow = match kind {
                    $(StandardCommandKind::$kind => self.$field.parse(handler, resources, cursor)?,)*
                };
                // only the exit command ends reading
                Ok(flow.map_break(|()| match kind {
                    StandardCommandKind::Exit => StandardCommandResult::Exit,
                    _ => StandardCommandResult::EndCommand,
                }))
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
    set_logic: SetLogic(
        ClosedParser<H, SymbolParser>,
        |handler, logic| handler.command_set_logic(logic)),
    declare_sort: DeclareSort(
        ClosedParser<H, PairParser<H, SymbolParser, NumeralParser>>,
        |handler, (name, arity)| handler.command_declare_sort(name, arity)),
    declare_sort_parameter: DeclareSortParameter(
        ClosedParser<H, SymbolParser>,
        |handler, name| handler.command_declare_sort_parameter(name)),
    declare_const: DeclareConst(
        ClosedParser<H, PairParser<H, SymbolParser, SortParser<H>>>,
        |handler, (name, sort)| handler.command_declare_fun(name, Vec::new(), sort)),
    declare_fun: DeclareFun(
        ClosedParser<H, PairParser<H, SymbolParser,
            PairParser<H, ParenMultipleParser<H, SortParser<H>>, SortParser<H>>>>,
        |handler, (name, (param_sorts, result_sort))|
            handler.command_declare_fun(name, param_sorts, result_sort)),
    declare_datatype: DeclareDatatype(
        ClosedParser<H, DeclareDatatypeParser<H>>,
        |_handler, ()| Ok(())),
    declare_datatypes: DeclareDatatypes(
        ClosedParser<H, DeclareDatatypesParser<H>>,
        |_handler, ()| Ok(())),
    define_sort: DefineSort(
        ClosedParser<H, DefinitionParser<H, DefineSort>>,
        |_handler, ()| Ok(())),
    define_const: DefineConst(
        ClosedParser<H, DefinitionParser<H, DefineConst>>,
        |_handler, ()| Ok(())),
    define_fun: DefineFun(
        ClosedParser<H, DefinitionParser<H, DefineFun>>,
        |_handler, ()| Ok(())),
    define_fun_rec: DefineFunRec(
        ClosedParser<H, DefinitionParser<H, DefineFunRec>>,
        |_handler, ()| Ok(())),
    define_funs_rec: DefineFunsRec(
        ClosedParser<H, DefineFunsRecParser<H>>,
        |_handler, ()| Ok(())),
    assert: Assert(
        ClosedParser<H, TermParser<H>>,
        |handler, term| handler.command_assert(term)),
    check_sat: CheckSat(
        CloseParenParser,
        |handler, ()| handler.command_check_sat(Vec::new())),
    check_sat_assuming: CheckSatAssuming(
        ClosedParser<H, ParenMultipleParser<H, TermParser<H>>>,
        |handler, assuming| handler.command_check_sat(assuming)),
    exit: Exit(
        CloseParenParser,
        |handler, ()| handler.command_exit()),
    push: Push(
        ClosedParser<H,NumeralParser>,
        |handler, amount| handler.command_push(amount)),
    pop: Pop(
        ClosedParser<H,NumeralParser>,
        |handler, amount| handler.command_pop(amount)),
    set_info: SetInfo(
        ClosedAttributeParser<H>,
        |handler, attribute| handler.command_set_info(attribute)),
    echo: Echo(
        ClosedParser<H, StringParser>,
        |handler, value| handler.command_echo(value)),
    get_option: GetOption(
        ClosedParser<H, KeywordParser>,
        |handler, option| handler.command_get_option(option)),
    set_option: SetOption(
        ClosedAttributeParser<H>,
        |handler, option| handler.command_set_option(option)),
    get_info: GetInfo(
        ClosedParser<H, KeywordParser>,
        |handler, keyword| handler.command_get_info(keyword)),
    get_value: GetValue(
        ClosedParser<H,GetValueParser<H>>,
        |handler, terms| handler.command_get_value(terms)),
    reset: Reset(
        CloseParenParser,
        |handler, ()| handler.command_reset()),
    reset_assertions: ResetAssertions(
        CloseParenParser,
        |handler, ()| handler.command_reset_assertions()),
    get_assertions: GetAssertions(
        CloseParenParser,
        |handler, ()| handler.command_get_assertions()),
    get_assignment: GetAssignment(
        CloseParenParser,
        |handler, ()| handler.command_get_assignment()),
    get_model: GetModel(
        CloseParenParser,
        |handler, ()| handler.command_get_model()),
    get_proof: GetProof(
        CloseParenParser,
        |handler, ()| handler.command_get_proof()),
    get_unsat_assumptions: GetUnsatAssumptions(
        CloseParenParser,
        |handler, ()| handler.command_get_unsat_assumptions()),
    get_unsat_core: GetUnsatCore(
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

impl<H: CommandHandler> Parser<H> for GetValueParser<H> {
    type Result = Vec<H::Term>;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut TokenCursor,
    ) -> Result<ControlFlow<Vec<H::Term>, ()>, ParserError<H::Error>> {
        match self.inner.parse(handler, resources, cursor)? {
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(terms) => {
                // ensure there is at least one term; the list ends at the last consumed token
                if terms.is_empty() {
                    let span = cursor
                        .last_consumed()
                        .expect("a finished term list parser must have consumed a token")
                        .span();
                    return Err(ParserError::category_error(
                        SyntaxErrorKind::EmptyGetValueTerms,
                        span,
                    ));
                }
                Ok(ControlFlow::Break(terms))
            }
        }
    }
}

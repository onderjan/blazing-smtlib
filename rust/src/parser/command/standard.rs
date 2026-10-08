use std::ops::ControlFlow;

use crate::{
    SmtCommandHandler, SmtFunctionSignature, SmtSymbolBuf,
    parser::{
        SmtCloseParenParser, SmtCommandPayloadParser, SmtKeywordParser, SmtNumeralParser,
        SmtParenMultipleParser, SmtParse, SmtParseError, SmtParseState, SmtStringParser,
        SmtSymbolParser, SmtSyntaxErrorKind,
        category::{
            SingleAttribute, SmtClosedAttributeParser, SmtClosedParser, SmtPairParser,
            SmtSortParser, SmtTermParser, TermSlot,
        },
        command::{
            SmtCommandOutcome, SmtCommandRule,
            datatype::{DeclareDatatypeParser, DeclareDatatypesParser},
            definition::{Definition, DefinitionParser},
            function::{DefineFunsRecParser, FunctionSignatureParser, RecursiveBodyParser},
        },
        parse_by_token,
    },
    token::{SmtBatchCursor, SmtCommandNameReserved, SmtSyntaxToken, SmtTokenCategory, SmtVersion},
};

/// Defines the rule of one standard command: its payload parser
/// and the handler call that delivers the parsed payload.
macro_rules! standard_command_rule {
    ($kind:ident, $parser:ty, |$handler:ident, $result:pat_param| $handle:expr) => {
        pub(super) struct $kind;

        impl<H: SmtCommandHandler> SmtCommandRule<H> for $kind {
            type Parser = $parser;

            fn handle(
                $handler: &mut H,
                $result: <$parser as SmtParse<H>>::Result,
            ) -> Result<(), H::Error> {
                $handle
            }
        }
    };
}

/// Defines the standard commands.
///
/// The commands before the semicolon are each named like their variant of
/// [`SmtCommandNameReserved`], which the command kinds are mapped from.
///
/// A command after the semicolon is the form a command had before the given
/// version, where its payload has another grammar: before that version,
/// the reserved word of the replaced command is mapped to it instead.
macro_rules! standard_commands {
    (
        $($field:ident: $kind:ident(
            $parser:ty,
            |$handler:ident, $result:pat_param| $handle:expr
        )),* $(,)?
        ;
        $($old_field:ident: $old_kind:ident(
            $old_parser:ty,
            |$old_handler:ident, $old_result:pat_param| $old_handle:expr
        ) replaces $replaced:ident before $before:ident),* $(,)?
    ) => {
        $(standard_command_rule!($kind, $parser, |$handler, $result| $handle);)*
        $(standard_command_rule!(
            $old_kind, $old_parser, |$old_handler, $old_result| $old_handle
        );)*

        /// Identifies a standard command.
        #[derive(Clone, Copy, Debug)]
        pub(crate) enum StandardCommandKind {
            $($kind,)*
            $($old_kind,)*
        }

        impl StandardCommandKind {
            /// The command named by the reserved word under the version.
            #[inline]
            pub fn from_reserved(name: SmtCommandNameReserved, version: SmtVersion) -> Self {
                match name {
                    $(SmtCommandNameReserved::$replaced if version < SmtVersion::$before => {
                        Self::$old_kind
                    })*
                    $(SmtCommandNameReserved::$kind => Self::$kind,)*
                }
            }
        }

        /// A struct containing all command parsers.
        ///
        /// All parsers are persistent to avoid dropping buffers.
        pub(crate) struct StandardCommandParsers<H: SmtCommandHandler> {
            $($field: SmtCommandPayloadParser<H, $kind>,)*
            $($old_field: SmtCommandPayloadParser<H, $old_kind>,)*
        }

        impl<H: SmtCommandHandler> StandardCommandParsers<H> {
            pub fn new() -> Self {
                Self {
                    $($field: SmtCommandPayloadParser::default(),)*
                    $($old_field: SmtCommandPayloadParser::default(),)*
                }
            }
            pub fn parse(
                &mut self,
                kind: StandardCommandKind,
                handler: &mut H,
                parse_state: &mut SmtParseState<H>,
                cursor: &mut SmtBatchCursor<'_>,
            ) -> Result<ControlFlow<SmtCommandOutcome, ()>, SmtParseError<H::Error>> {
                let flow = match kind {
                    $(StandardCommandKind::$kind => self.$field.parse(handler, parse_state, cursor)?,)*
                    $(StandardCommandKind::$old_kind => {
                        self.$old_field.parse(handler, parse_state, cursor)?
                    })*
                };
                let ControlFlow::Break(()) = flow else {
                    return Ok(ControlFlow::Continue(()));
                };

                // handle version-switch and exit specially
                let result = match kind {
                    StandardCommandKind::SetInfo => {
                        match self.set_info.parser.take_declared_version() {
                            Some(version) => SmtCommandOutcome::SetVersion(version),
                            None => SmtCommandOutcome::Command,
                        }
                    }
                    StandardCommandKind::Exit => SmtCommandOutcome::Exit,
                    _ => SmtCommandOutcome::Command,
                };
                Ok(ControlFlow::Break(result))
            }
        }

        impl<H: SmtCommandHandler> Default for StandardCommandParsers<H> {
            fn default() -> Self {
                Self::new()
            }
        }
    };
}

standard_commands! {
    set_logic: SetLogic(
        SmtClosedParser<H, SmtSymbolParser>,
        |handler, logic| handler.command_set_logic(logic)),
    declare_sort: DeclareSort(
        SmtClosedParser<H, SmtPairParser<H, SmtSymbolParser, SmtNumeralParser>>,
        |handler, (name, arity)| handler.command_declare_sort(name, arity)),
    declare_sort_parameter: DeclareSortParameter(
        SmtClosedParser<H, SmtSymbolParser>,
        |handler, name| handler.command_declare_sort_parameter(name)),
    declare_const: DeclareConst(
        SmtClosedParser<H, SmtPairParser<H, SmtSymbolParser, SmtSortParser<H>>>,
        |handler, (name, sort)| handler.command_declare_fun(name, Vec::new(), sort)),
    declare_fun: DeclareFun(
        SmtClosedParser<H, SmtPairParser<H, SmtSymbolParser,
            SmtPairParser<H, SmtParenMultipleParser<H, SmtSortParser<H>>, SmtSortParser<H>>>>,
        |handler, (name, (param_sorts, result_sort))|
            handler.command_declare_fun(name, param_sorts, result_sort)),
    declare_datatype: DeclareDatatype(
        SmtClosedParser<H, DeclareDatatypeParser<H>>,
        |_handler, ()| Ok(())),
    declare_datatypes: DeclareDatatypes(
        SmtClosedParser<H, DeclareDatatypesParser<H>>,
        |_handler, ()| Ok(())),
    define_sort: DefineSort(
        SmtClosedParser<H, DefinitionParser<H, DefineSort>>,
        |_handler, ()| Ok(())),
    define_const: DefineConst(
        SmtClosedParser<H, DefinitionParser<H, DefineConst>>,
        |_handler, ()| Ok(())),
    define_fun: DefineFun(
        SmtClosedParser<H, DefinitionParser<H, DefineFun>>,
        |_handler, ()| Ok(())),
    define_fun_rec: DefineFunRec(
        SmtClosedParser<H, DefinitionParser<H, DefineFunRec>>,
        |_handler, ()| Ok(())),
    define_funs_rec: DefineFunsRec(
        SmtClosedParser<H, DefineFunsRecParser<H>>,
        |_handler, ()| Ok(())),
    assert: Assert(
        SmtClosedParser<H, SmtTermParser<H>>,
        |handler, term| handler.command_assert(term)),
    check_sat: CheckSat(
        SmtCloseParenParser,
        |handler, ()| handler.command_check_sat(Vec::new())),
    check_sat_assuming: CheckSatAssuming(
        SmtClosedParser<H, SmtParenMultipleParser<H, SmtTermParser<H>>>,
        |handler, assumptions| handler.command_check_sat(assumptions)),
    exit: Exit(
        SmtCloseParenParser,
        |handler, ()| handler.command_exit()),
    push: Push(
        SmtClosedParser<H,SmtNumeralParser>,
        |handler, amount| handler.command_push(amount)),
    pop: Pop(
        SmtClosedParser<H,SmtNumeralParser>,
        |handler, amount| handler.command_pop(amount)),
    set_info: SetInfo(
        SetInfoParser,
        |handler, attribute| handler.command_set_info(attribute)),
    echo: Echo(
        SmtClosedParser<H, SmtStringParser>,
        |handler, value| handler.command_echo(value)),
    get_option: GetOption(
        SmtClosedParser<H, SmtKeywordParser>,
        |handler, option| handler.command_get_option(option)),
    set_option: SetOption(
        SmtClosedAttributeParser<H>,
        |handler, option| handler.command_set_option(option)),
    get_info: GetInfo(
        SmtClosedParser<H, SmtKeywordParser>,
        |handler, keyword| handler.command_get_info(keyword)),
    get_value: GetValue(
        SmtClosedParser<H,GetValueParser<H>>,
        |handler, terms| handler.command_get_value(terms)),
    reset: Reset(
        SmtCloseParenParser,
        |handler, ()| handler.command_reset()),
    reset_assertions: ResetAssertions(
        SmtCloseParenParser,
        |handler, ()| handler.command_reset_assertions()),
    get_assertions: GetAssertions(
        SmtCloseParenParser,
        |handler, ()| handler.command_get_assertions()),
    get_assignment: GetAssignment(
        SmtCloseParenParser,
        |handler, ()| handler.command_get_assignment()),
    get_model: GetModel(
        SmtCloseParenParser,
        |handler, ()| handler.command_get_model()),
    get_proof: GetProof(
        SmtCloseParenParser,
        |handler, ()| handler.command_get_proof()),
    get_unsat_assumptions: GetUnsatAssumptions(
        SmtCloseParenParser,
        |handler, ()| handler.command_get_unsat_assumptions()),
    get_unsat_core: GetUnsatCore(
        SmtCloseParenParser,
        |handler, ()| handler.command_get_unsat_core()),
    ;
    check_sat_assuming_literals: CheckSatAssumingLiterals(
        SmtClosedParser<H, SmtParenMultipleParser<H, PropLiteralParser>>,
        |handler, assumptions| handler.command_check_sat(assumptions))
        replaces CheckSatAssuming before V2_7,
}

impl<H: SmtCommandHandler> Definition<H> for DefineConst {
    type Signature = SmtPairParser<H, SmtSymbolParser, SmtSortParser<H>>;
    type Body = SmtTermParser<H>;

    fn start(handler: &mut H, signature: (SmtSymbolBuf, H::Sort)) -> Result<(), H::Error> {
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

impl<H: SmtCommandHandler> Definition<H> for DefineFun {
    type Signature = FunctionSignatureParser<H>;
    type Body = SmtTermParser<H>;

    fn start(handler: &mut H, signature: SmtFunctionSignature<H>) -> Result<(), H::Error> {
        handler.start_define_fun(signature)
    }

    fn end(handler: &mut H, term: H::Term) -> Result<(), H::Error> {
        handler.end_define_fun(term)
    }
}

impl<H: SmtCommandHandler> Definition<H> for DefineSort {
    type Signature = SmtPairParser<H, SmtSymbolParser, SmtParenMultipleParser<H, SmtSymbolParser>>;
    type Body = SmtSortParser<H>;

    fn start(
        handler: &mut H,
        signature: (SmtSymbolBuf, Vec<SmtSymbolBuf>),
    ) -> Result<(), H::Error> {
        let (name, params) = signature;
        handler.start_define_sort(name, params)
    }

    fn end(handler: &mut H, sort: H::Sort) -> Result<(), H::Error> {
        handler.end_define_sort(sort)
    }
}

impl<H: SmtCommandHandler> Definition<H> for DefineFunRec {
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
pub(super) struct GetValueParser<H: SmtCommandHandler> {
    inner: SmtParenMultipleParser<H, SmtTermParser<H>>,
}

impl<H: SmtCommandHandler> GetValueParser<H> {
    fn new() -> Self {
        Self {
            inner: SmtParenMultipleParser::default(),
        }
    }
}

impl<H: SmtCommandHandler> Default for GetValueParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for GetValueParser<H> {
    type Result = Vec<H::Term>;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Vec<H::Term>, ()>, SmtParseError<H::Error>> {
        match self.inner.parse(handler, parse_state, cursor)? {
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(terms) => {
                // ensure there is at least one term
                if terms.is_empty() {
                    return Err(SmtParseError::category_error(
                        SmtSyntaxErrorKind::EmptyGetValueTerms,
                    ));
                }
                Ok(ControlFlow::Break(terms))
            }
        }
    }
}

/// A parser for the payload of `set-info`.
///
/// The payload for `set-info` is an attribute followed by a closing parenthesis.
///
/// This parser is necessary to recognise the version declaration attribute
/// `:smt-lib-version <version>`, where the version should be a decimal.
pub(super) struct SetInfoParser {
    state: SetInfoState,
    declared_version: Option<SmtVersion>,
    unsupported_version: bool,
}

enum SetInfoState {
    /// The next token of the payload is the attribute name.
    Name,
    /// The attribute name was `:smt-lib-version`,
    /// the next token of the payload is the version.
    Version,
    /// Continue to parse normally.
    Rest,
}

impl SetInfoParser {
    fn new() -> Self {
        Self {
            state: SetInfoState::Name,
            declared_version: None,
            unsupported_version: false,
        }
    }

    /// Takes the version declared by the last parsed command if it exists.
    pub(super) fn take_declared_version(&mut self) -> Option<SmtVersion> {
        self.declared_version.take()
    }
}

impl Default for SetInfoParser {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for SetInfoParser {
    type Result = H::Attribute;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<H::Attribute, ()>, SmtParseError<H::Error>> {
        // The version declaration must be treated specially while parsing
        // the attribute. We look at the set-info attribute name; if it's s
        // :smt-lib-version we parse the version to be able to switch.
        //
        // The state machine is as follows:
        // 1. Name: if the first token is :smt-lib-version, move to version handling;
        //    otherwise, move to the rest.
        // 2. Version takes the second token of the payload, remembers the version
        //    it names, or that it names none, and moves to Rest.
        // 3. Rest looks at nothing more.
        //
        // A value that names no version is an error of the command as a whole:
        // it is raised once the payload has ended, at the closing parenthesis.
        let SmtParseState {
            attribute_slot,
            arena,
            s_expr_slot,
            ..
        } = parse_state;
        parse_by_token(cursor, |version, token| {
            match self.state {
                SetInfoState::Name => {
                    let declares_version = token.category() == SmtTokenCategory::Keyword
                        && token.content() == b"smt-lib-version";
                    self.state = if declares_version {
                        SetInfoState::Version
                    } else {
                        SetInfoState::Rest
                    };
                }
                SetInfoState::Version => {
                    // only a decimal that converts to a version names one
                    let declared = match token.category() {
                        SmtTokenCategory::Decimal => SmtVersion::from_decimal_opt(token.content()),
                        _ => None,
                    };
                    match declared {
                        Some(declared) => self.declared_version = Some(declared),
                        None => self.unsupported_version = true,
                    }
                    self.state = SetInfoState::Rest;
                }
                SetInfoState::Rest => {}
            }

            let flow = attribute_slot.progress::<H, SingleAttribute>(
                handler,
                arena,
                s_expr_slot,
                version,
                token,
            )?;
            if flow.is_break() {
                // the command has ended, the next payload starts with its attribute name
                self.state = SetInfoState::Name;
                if self.unsupported_version {
                    // TODO: this was take(), rewrite after tests are done
                    self.unsupported_version = false;

                    return Err(SmtParseError::category_error(
                        SmtSyntaxErrorKind::UnsupportedVersion,
                    ));
                }
            }
            Ok(flow)
        })
    }
}

/// A parser for a propositional literal: `<symbol>` or `(not <symbol>)`.
///
/// Before SMT-LIB 2.7, the assumptions of `check-sat-assuming` are
/// propositional literals. The literals are terms, and are handled as such.
pub(super) struct PropLiteralParser {
    state: PropLiteralState,
}

enum PropLiteralState {
    /// The next token starts a literal.
    Start,
    /// After the parenthesis that opens a negated literal: the next token is `not`.
    Not,
    /// After `not`: the next token is the negated symbol.
    Negated,
    /// After the negated symbol: the next token closes the literal.
    Close,
}

impl PropLiteralParser {
    fn new() -> Self {
        Self {
            state: PropLiteralState::Start,
        }
    }
}

impl Default for PropLiteralParser {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for PropLiteralParser {
    type Result = H::Term;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<H::Term, ()>, SmtParseError<H::Error>> {
        // A literal is a term of one of two shapes, so every token is
        // progressed in the term slot once it is known to fit the shape.
        // The term slot finishes the term at the last token of the literal.
        //
        // The state machine is as follows:
        // 1. Start: a symbol is a literal by itself; "(" opens a negated
        //    literal, move to Not.
        // 2. Not, Negated, Close: expect the symbol "not", any symbol and ")"
        //    in turn, then move back to Start.
        parse_by_token(cursor, |version, token| {
            self.state = match (&self.state, token.syntax(version)) {
                (PropLiteralState::Start, SmtSyntaxToken::Symbol(_)) => PropLiteralState::Start,
                (PropLiteralState::Start, SmtSyntaxToken::ParenOpen) => PropLiteralState::Not,
                (PropLiteralState::Not, SmtSyntaxToken::Symbol(symbol))
                    if symbol.as_slice() == b"not" =>
                {
                    PropLiteralState::Negated
                }
                (PropLiteralState::Negated, SmtSyntaxToken::Symbol(_)) => PropLiteralState::Close,
                (PropLiteralState::Close, SmtSyntaxToken::ParenClose) => PropLiteralState::Start,
                _ => {
                    return Err(SmtParseError::category_error(
                        SmtSyntaxErrorKind::ExpectedPropositionalLiteral,
                    ));
                }
            };

            let flow = TermSlot::progress(handler, parse_state, version, token)?;
            debug_assert_eq!(
                flow.is_break(),
                matches!(self.state, PropLiteralState::Start),
                "the term must finish exactly at the last token of the literal"
            );
            Ok(flow)
        })
    }
}

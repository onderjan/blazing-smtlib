use std::ops::ControlFlow;

use crate::{
    SmtCommandHandler, SmtFunctionSignature, SmtSpan, SmtSymbol,
    parser::{
        SmtCloseParenParser, SmtCommandPayloadParser, SmtKeywordParser, SmtNumeralParser,
        SmtParenMultipleParser, SmtParse, SmtParseError, SmtParseState, SmtStringParser,
        SmtSymbolParser, SmtSyntaxErrorKind,
        category::{
            SmtClosedAttributeParser, SmtClosedParser, SmtPairParser, SmtSortParser, SmtTermParser,
        },
        command::{
            SmtCommandOutcome, SmtCommandRule,
            datatype::{DeclareDatatypeParser, DeclareDatatypesParser},
            definition::{Definition, DefinitionParser},
            function::{DefineFunsRecParser, FunctionSignatureParser, RecursiveBodyParser},
        },
    },
    token::{SmtBatchCursor, SmtCommandNameReserved, SmtSyntaxToken, SmtTokenCategory, SmtVersion},
};

/// Defines the standard commands, each named like its variant of
/// [`SmtCommandNameReserved`], which the command kinds are mapped from.
macro_rules! standard_commands {
    ($($field:ident: $kind:ident(
        $parser:ty,
        |$handler:ident, $result:pat_param| $handle:expr
    )),* $(,)?) => {
        $(
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
        )*

        /// Identifies a standard command.
        #[derive(Clone, Copy, Debug)]
        pub(crate) enum StandardCommandKind {
            $($kind,)*
        }

        impl StandardCommandKind {
            /// The command named by the reserved word.
            #[inline]
            pub fn from_reserved(name: SmtCommandNameReserved) -> Self {
                match name {
                    $(SmtCommandNameReserved::$kind => Self::$kind,)*
                }
            }
        }

        /// A struct containing all command parsers.
        ///
        /// All parsers are persistent to avoid dropping buffers.
        pub(crate) struct StandardCommandParsers<H: SmtCommandHandler> {
            $($field: SmtCommandPayloadParser<H, $kind>,)*
        }

        impl<H: SmtCommandHandler> StandardCommandParsers<H> {
            pub fn new() -> Self {
                Self {
                    $($field: SmtCommandPayloadParser::default(),)*
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
                };
                let ControlFlow::Break(()) = flow else {
                    return Ok(ControlFlow::Continue(()));
                };

                // handle version-switch and exit specially
                let result = match kind {
                    StandardCommandKind::SetInfo => {
                        match self.set_info.parser.take_declared_version() {
                            Some((version, span)) => SmtCommandOutcome::SetVersion(version, span),
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
        CheckSatAssumingParser<H>,
        |handler, assuming| handler.command_check_sat(assuming)),
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
        SetInfoParser<H>,
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
}

impl<H: SmtCommandHandler> Definition<H> for DefineConst {
    type Signature = SmtPairParser<H, SmtSymbolParser, SmtSortParser<H>>;
    type Body = SmtTermParser<H>;

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

    fn start(handler: &mut H, signature: (SmtSymbol, Vec<SmtSymbol>)) -> Result<(), H::Error> {
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
                // ensure there is at least one term; the list ends at the last consumed token
                if terms.is_empty() {
                    let span = cursor
                        .last_consumed()
                        .expect("a finished term list parser must have consumed a token")
                        .span();
                    return Err(SmtParseError::category_error(
                        SmtSyntaxErrorKind::EmptyGetValueTerms,
                        span,
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
pub(super) struct SetInfoParser<H: SmtCommandHandler> {
    inner: SmtClosedAttributeParser<H>,
    state: SetInfoState,
    declared_version: Option<(SmtVersion, SmtSpan)>,
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

impl<H: SmtCommandHandler> SetInfoParser<H> {
    fn new() -> Self {
        Self {
            inner: SmtClosedAttributeParser::new(),
            state: SetInfoState::Name,
            declared_version: None,
        }
    }

    /// Takes the spanned version declared by the last parsed command if it exists.
    pub(super) fn take_declared_version(&mut self) -> Option<(SmtVersion, SmtSpan)> {
        self.declared_version.take()
    }
}

impl<H: SmtCommandHandler> Default for SetInfoParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for SetInfoParser<H> {
    type Result = H::Attribute;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<H::Attribute, ()>, SmtParseError<H::Error>> {
        // We process the version before the actual processing, as we
        // cannot process token-by-token in parallel, just look at the cursor
        // and then hand it over.
        //
        // The state machine is as follows:
        // 1. Name: if the first token is :smt-lib-version, move to version handling;
        //    otherwise, move to the rest.
        // 2. Version looks at the second token of the payload, which must name
        //    a version, remembers the version and moves to Rest.
        // 3. Rest looks at nothing more.

        let mut ahead = 0;
        while let Some(token) = cursor.get(ahead) {
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
                    // disallow any version that isn't a decimal that converts to a version
                    let version = match token.category() {
                        SmtTokenCategory::Decimal => SmtVersion::from_decimal_opt(token.content()),
                        _ => None,
                    };
                    let Some(version) = version else {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::UnsupportedVersion,
                            token.span(),
                        ));
                    };
                    self.declared_version = Some((version, token.span()));
                    self.state = SetInfoState::Rest;
                }
                SetInfoState::Rest => break,
            }
            ahead += 1;
        }

        let flow = self.inner.parse(handler, parse_state, cursor)?;
        if flow.is_break() {
            // the command has ended, the next payload starts with its attribute name
            self.state = SetInfoState::Name;
        }
        Ok(flow)
    }
}

/// A parser for the payload of `check-sat-assuming`.
///
/// `check-sat-assuming` payload is a parenthesised list of assumptions
/// followed by a closing parenthesis.
///
/// The assumptions are terms since SMT-LIB 2.7. Before it, each assumption
/// must be a propositional literal: `<symbol>` or `(not <symbol>)`.
/// The literals are terms too, and are parsed as such.
pub(super) struct CheckSatAssumingParser<H: SmtCommandHandler> {
    inner: SmtClosedParser<H, SmtParenMultipleParser<H, SmtTermParser<H>>>,
    state: PropLiteralsState,
}

enum PropLiteralsState {
    /// The next token of the payload opens the list.
    Open,
    /// Inside the list: the next token starts a literal or closes the list.
    Literal,
    /// After the parenthesis that opens a literal: the next token is `not`.
    Not,
    /// After `not`: the next token is the negated symbol.
    Negated,
    /// After the negated symbol: the next token closes the literal.
    Close,
    /// Continue to parse normally.
    Rest,
}

impl<H: SmtCommandHandler> CheckSatAssumingParser<H> {
    fn new() -> Self {
        Self {
            inner: SmtClosedParser::default(),
            state: PropLiteralsState::Open,
        }
    }
}

impl<H: SmtCommandHandler> Default for CheckSatAssumingParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for CheckSatAssumingParser<H> {
    type Result = Vec<H::Term>;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Vec<H::Term>, ()>, SmtParseError<H::Error>> {
        // Any terms are allowed as assumptions since SMT-LIB 2.7. Before it,
        // the terms must be propositional literals, i.e. `<symbol>` or `(not <symbol>)`.
        // In that case, we check that the assumptions are propositional literals
        // before handing the cursor off to the actual processing.
        //
        // The state machine is as follows:
        // 1. Open: the first token should open the list, move to Literal;
        //    otherwise, move to Rest and leave the error to the actual processing.
        // 2. Literal: a symbol is a literal; "(" starts a negated one, move to Not;
        //    ")" closes the list, move to Rest.
        // 3. Not, Negated, Close: expect the symbol "not", any symbol and ")"
        //    in turn, then move back to Literal.
        // 4. Rest looks at nothing more.
        let version = cursor.version();
        if version < SmtVersion::V2_7 {
            let mut ahead = 0;
            while let Some(token) = cursor.get(ahead) {
                let kind = token.syntax(version);
                self.state = match (&self.state, kind) {
                    (PropLiteralsState::Rest, _) => break,
                    (PropLiteralsState::Open, SmtSyntaxToken::ParenOpen) => {
                        PropLiteralsState::Literal
                    }
                    // anything else, and the end of the input in any state,
                    // is left to the actual processing
                    (PropLiteralsState::Open, _) | (_, SmtSyntaxToken::EndOfFile) => {
                        PropLiteralsState::Rest
                    }
                    (PropLiteralsState::Literal, SmtSyntaxToken::Symbol(_)) => {
                        PropLiteralsState::Literal
                    }
                    (PropLiteralsState::Literal, SmtSyntaxToken::ParenOpen) => {
                        PropLiteralsState::Not
                    }
                    (PropLiteralsState::Literal, SmtSyntaxToken::ParenClose) => {
                        PropLiteralsState::Rest
                    }
                    (PropLiteralsState::Not, SmtSyntaxToken::Symbol(symbol))
                        if symbol.as_slice() == b"not" =>
                    {
                        PropLiteralsState::Negated
                    }
                    (PropLiteralsState::Negated, SmtSyntaxToken::Symbol(_)) => {
                        PropLiteralsState::Close
                    }
                    (PropLiteralsState::Close, SmtSyntaxToken::ParenClose) => {
                        PropLiteralsState::Literal
                    }
                    _ => {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::ExpectedPropositionalLiteral,
                            token.span(),
                        ));
                    }
                };
                ahead += 1;
            }
        }

        let flow = self.inner.parse(handler, parse_state, cursor)?;
        if flow.is_break() {
            // the command has ended, the next payload starts with the list
            self.state = PropLiteralsState::Open;
        }
        Ok(flow)
    }
}

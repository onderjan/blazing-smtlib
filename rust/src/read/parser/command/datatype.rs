use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtDatatypeConstructor, SmtNumeral, SmtSpan, SmtSymbol,
    read::parser::{
        CloseParenParser, ClosedMultipleParser, NumeralParser, OpenParenParser, OpenedParser,
        ParenMaximumParser, ParenMultipleParser, ParenParser, Parser, ParserResources,
        SmtParseError, SmtSyntaxErrorKind, SortedVarParser, SymbolParser, category::PairParser,
        handle_err, parse_by_token,
    },
    token::{
        SmtBatchCursor, SmtGeneralReserved, SmtReserved, SmtSyntaxToken, SmtToken, SmtVersion,
    },
};

/// Parser for a single datatype introduction (name and arity in parentheses).
type IntroductionParser<H> = ParenParser<H, PairParser<H, SymbolParser, NumeralParser>>;

/// Parser for a single datatype constructor.
type ConstructorParser<H> =
    OpenedParser<H, PairParser<H, SymbolParser, ClosedMultipleParser<H, SortedVarParser<H>>>>;

#[derive(Clone, Copy)]
enum DatatypeState {
    /// Before opening parenthesis of the datatype declaration.
    Start,
    /// Expecting the kind of the datatype.
    ///
    /// This is either the opening parenthesis for the simple constructors,
    /// or the reserved word "par" for parametric constructors.
    Kind,
    /// Parsing simple constructor declarations, without parameters.
    SimpleConstructors,
    /// Parsing parameters for parametric constructors.
    Parameters,
    /// Expecting opening parenthesis of the parametric constructors.
    ParametricOpen,
    /// Parsing parametric constructors.
    ParametricConstructors,
    /// Expecting closing parenthesis for the whole datatype.
    ///
    /// This is only reached with parametric constructors,
    /// as simple constructors are closed in their own parser.
    Close,
}

/// Parser for a datatype.
struct DatatypeParser<H: CommandHandler> {
    state: DatatypeState,
    single_introduction: Option<(SmtSymbol, SmtSpan)>,

    symbols_parser: ParenMultipleParser<H, SymbolParser>,
    constructors_parser: ClosedMultipleParser<H, ConstructorParser<H>>,
}

impl<H: CommandHandler> DatatypeParser<H> {
    fn new() -> Self {
        Self {
            state: DatatypeState::Start,
            single_introduction: None,
            symbols_parser: ParenMultipleParser::default(),
            constructors_parser: ClosedMultipleParser::default(),
        }
    }

    /// Switches this datatype to "single datatype mode".
    ///
    /// This mode calls `start_declare_datatypes` as per the definition of
    /// `declare-datatype`, which depends on the form of the single datatype.
    fn set_single_datatype_mode(&mut self, name: SmtSymbol, span: SmtSpan) {
        self.single_introduction = Some((name, span))
    }

    /// Starts a datatype, taking into account the "single datatype mode".
    fn start_datatype(
        &mut self,
        handler: &mut H,
        params: Vec<SmtSymbol>,
        span: SmtSpan,
    ) -> Result<(), SmtParseError<H::Error>> {
        if let Some((name, name_span)) = self.single_introduction.take() {
            // start declare datatypes with the arity equal to the number of parameters
            let arity = SmtNumeral::from_usize(params.len());
            handle_err(
                handler.start_declare_datatypes(vec![(name, arity)]),
                name_span,
            )?;
        }
        handle_err(handler.start_datatype_declaration(params), span)
    }
}

impl<H: CommandHandler> Default for DatatypeParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler> Parser<H> for DatatypeParser<H> {
    type Result = ();

    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        parse_by_token(cursor, |version, token| {
            self.progress(handler, resources, version, token)
        })
    }
}

impl<H: CommandHandler> DatatypeParser<H> {
    /// Progresses the parser by one token.
    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        version: SmtVersion,
        token: SmtToken,
    ) -> Result<ControlFlow<()>, SmtParseError<H::Error>> {
        let span = token.span();
        let constructors = match self.state {
            DatatypeState::Start => {
                // expect opening parenthesis and move to deciding the kind
                OpenParenParser::expect(token)?;
                self.state = DatatypeState::Kind;
                None
            }
            DatatypeState::Kind => match token.syntax(version) {
                SmtSyntaxToken::ParenOpen => {
                    // simple constructors, start the datatype with no parameters
                    self.start_datatype(handler, Vec::new(), span)?;
                    self.state = DatatypeState::SimpleConstructors;
                    // this parenthesis already is the start of the constructor,
                    // so we will forward it
                    let result = self.constructors_parser.parse(
                        handler,
                        resources,
                        &mut SmtBatchCursor::single(version, token),
                    )?;
                    debug_assert!(
                        matches!(result, ControlFlow::Continue(())),
                        "datatype constructor should continue on opening parenthesis"
                    );
                    None
                }
                SmtSyntaxToken::Reserved(SmtReserved::General(SmtGeneralReserved::Par)) => {
                    // parametric constructors, we need to parse the parameters first
                    self.state = DatatypeState::Parameters;
                    None
                }
                _ => {
                    return Err(SmtParseError::category_error(
                        SmtSyntaxErrorKind::ExpectedDatatypeKind,
                        span,
                    ));
                }
            },
            DatatypeState::SimpleConstructors => {
                // parse the simple constructors
                self.constructors_parser
                    .parse(
                        handler,
                        resources,
                        &mut SmtBatchCursor::single(version, token),
                    )?
                    .break_value()
            }
            DatatypeState::Parameters => {
                // parse the parameters
                if let ControlFlow::Break(params) = self.symbols_parser.parse(
                    handler,
                    resources,
                    &mut SmtBatchCursor::single(version, token),
                )? {
                    // there must be at least one parameter
                    if params.is_empty() {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::EmptyDatatypeParameters,
                            span,
                        ));
                    }
                    // start the datatype with the parameters
                    self.start_datatype(handler, params, span)?;
                    // move to parsing the opening parenthesis of parametric constructors
                    self.state = DatatypeState::ParametricOpen;
                }
                None
            }
            DatatypeState::ParametricOpen => {
                // expect opening parenthesis and move to parsing parametric constructors
                OpenParenParser::expect(token)?;
                self.state = DatatypeState::ParametricConstructors;
                None
            }
            DatatypeState::ParametricConstructors => {
                // parse the parametric constructors
                self.constructors_parser
                    .parse(
                        handler,
                        resources,
                        &mut SmtBatchCursor::single(version, token),
                    )?
                    .break_value()
            }
            DatatypeState::Close => {
                // expect closing parenthesis, reset and break
                CloseParenParser::expect(token)?;
                self.state = DatatypeState::Start;
                return Ok(ControlFlow::Break(()));
            }
        };

        if let Some(constructors) = constructors {
            // there must be at least one constructor
            if constructors.is_empty() {
                return Err(SmtParseError::category_error(
                    SmtSyntaxErrorKind::EmptyDatatypeConstructors,
                    span,
                ));
            }

            // TODO: do not retype the constructors
            let constructors = constructors
                .into_iter()
                .map(|(name, selectors)| SmtDatatypeConstructor { name, selectors })
                .collect();
            // end the datatype
            handle_err(handler.end_datatype_declaration(constructors), span)?;
            if matches!(self.state, DatatypeState::SimpleConstructors) {
                // we have already parsed the closing parenthesis
                // reset and break
                self.state = DatatypeState::Start;
                return Ok(ControlFlow::Break(()));
            }
            // we still need to wait for the closing parenthesis
            self.state = DatatypeState::Close
        }

        Ok(ControlFlow::Continue(()))
    }
}

#[derive(Clone, Copy)]
enum DeclareDatatypesState {
    /// Parsing the datatype introductions.
    Introductions,
    /// Parsing the datatype declarations.
    Declarations,
}

/// Parser for the command `declare-datatypes`.
pub(super) struct DeclareDatatypesParser<H: CommandHandler> {
    state: DeclareDatatypesState,

    introductions_parser: ParenMultipleParser<H, IntroductionParser<H>>,
    datatypes_parser: ParenMaximumParser<H, DatatypeParser<H>>,
}

impl<H: CommandHandler> DeclareDatatypesParser<H> {
    pub fn new() -> Self {
        // the number of maximum elements for datatypes parser will be
        // resized before each parse, it does not matter in the initial state
        Self {
            state: DeclareDatatypesState::Introductions,
            introductions_parser: ParenMultipleParser::default(),
            datatypes_parser: ParenMaximumParser::new(DatatypeParser::new(), 0),
        }
    }
}

impl<H: CommandHandler> Parser<H> for DeclareDatatypesParser<H> {
    type Result = ();

    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        parse_by_token(cursor, |version, token| {
            self.progress(handler, resources, version, token)
        })
    }
}

impl<H: CommandHandler> DeclareDatatypesParser<H> {
    /// Progresses the parser by one token.
    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        version: SmtVersion,
        token: SmtToken,
    ) -> Result<ControlFlow<()>, SmtParseError<H::Error>> {
        let span = token.span();
        match self.state {
            DeclareDatatypesState::Introductions => {
                // parse datatype introductions
                if let ControlFlow::Break(introductions) = self.introductions_parser.parse(
                    handler,
                    resources,
                    &mut SmtBatchCursor::single(version, token),
                )? {
                    // introductions must not be empty
                    if introductions.is_empty() {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::EmptyDatatypeIntroductions,
                            span,
                        ));
                    }
                    // ensure the datatypes parser is expecting the correct number of elements
                    self.datatypes_parser.set_maximum(introductions.len());
                    // start datatype declarations
                    handle_err(handler.start_declare_datatypes(introductions), span)?;
                    self.state = DeclareDatatypesState::Declarations;
                }
            }
            DeclareDatatypesState::Declarations => {
                // parse datatypes
                if let ControlFlow::Break(datatypes) = self.datatypes_parser.parse(
                    handler,
                    resources,
                    &mut SmtBatchCursor::single(version, token),
                )? {
                    // there cannot be more datatypes than sort declarations due to the maximum parser
                    // ensure there are not more sort declarations than datatypes
                    if datatypes.len() != self.datatypes_parser.max_elements() {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::ExpectedDatatype,
                            span,
                        ));
                    }

                    // end datatypes declarations, reset, and break
                    // the datatypes parser can have a changed number of maximum elements,
                    // but it will be changed before it is used next time
                    handle_err(handler.end_declare_datatypes(), span)?;
                    self.state = DeclareDatatypesState::Introductions;
                    return Ok(ControlFlow::Break(()));
                }
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

impl<H: CommandHandler> Default for DeclareDatatypesParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Copy)]
enum DeclareDatatypeState {
    /// Expecting datatype name.
    Name,
    /// Parsing the datatype.
    Datatype,
}

/// Parser for the command `declare-datatype`.
pub(super) struct DeclareDatatypeParser<H: CommandHandler> {
    state: DeclareDatatypeState,
    datatype_parser: DatatypeParser<H>,
}

impl<H: CommandHandler> Default for DeclareDatatypeParser<H> {
    fn default() -> Self {
        Self {
            state: DeclareDatatypeState::Name,
            datatype_parser: DatatypeParser::new(),
        }
    }
}

impl<H: CommandHandler> Parser<H> for DeclareDatatypeParser<H> {
    type Result = ();

    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        parse_by_token(cursor, |version, token| {
            self.progress(handler, resources, version, token)
        })
    }
}

impl<H: CommandHandler> DeclareDatatypeParser<H> {
    /// Progresses the parser by one token.
    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        version: SmtVersion,
        token: SmtToken,
    ) -> Result<ControlFlow<()>, SmtParseError<H::Error>> {
        let span = token.span();
        match self.state {
            DeclareDatatypeState::Name => {
                // parse the datatype name
                let name = SymbolParser::expect::<H>(version, token)?;
                self.datatype_parser.set_single_datatype_mode(name, span);
                self.state = DeclareDatatypeState::Datatype;
            }
            DeclareDatatypeState::Datatype => {
                if let ControlFlow::Break(()) = self.datatype_parser.parse(
                    handler,
                    resources,
                    &mut SmtBatchCursor::single(version, token),
                )? {
                    // the single declaration ends the command
                    handle_err(handler.end_declare_datatypes(), span)?;
                    self.state = DeclareDatatypeState::Name;
                    return Ok(ControlFlow::Break(()));
                }
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

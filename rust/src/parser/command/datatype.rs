use std::ops::ControlFlow;

use crate::{
    SmtCommandHandler, SmtNodeTypes,
    grammar::{SmtConstructors, SmtConstructorsBuf, SmtSortAritiesBuf, SmtSymbolsBuf},
    lexicon::{SmtGeneralReserved, SmtReserved, SmtSymbolBuf},
    parser::{
        SmtCloseParenParser, SmtClosedMultipleParser, SmtMissingItem, SmtNonEmptyList,
        SmtNumeralParser, SmtOpenParenParser, SmtOpenedParser, SmtParenMaximumParser,
        SmtParenMultipleParser, SmtParenParser, SmtParse, SmtParseError, SmtParseState,
        SmtSortedVarParser, SmtSymbolParser, SmtSyntaxErrorKind, category::SmtPairParser, expected,
        handle_err, parse_by_token,
    },
    token::{SingleTokenCursor, SmtCursor, SmtToken},
};

/// Parser for a single datatype introduction (name and arity in parentheses).
type IntroductionParser<H> = SmtParenParser<H, SmtPairParser<H, SmtSymbolParser, SmtNumeralParser>>;

/// Datatype constructors as parsed, owned until they are handed over:
/// each a name with its selectors.
pub(crate) type OwnedConstructors<S> = Vec<(SmtSymbolBuf, Vec<(SmtSymbolBuf, S)>)>;

/// Hands the constructors to `f` as a view, through `buf`, which is cleared afterwards.
pub(crate) fn hand_over_constructors<N: SmtNodeTypes + ?Sized, R>(
    buf: &mut SmtConstructorsBuf<N>,
    constructors: OwnedConstructors<N::Sort>,
    f: impl FnOnce(SmtConstructors<'_, N>) -> R,
) -> R {
    for (name, selectors) in constructors {
        buf.push(name.view());
        for (selector, sort) in selectors {
            buf.push_selector(selector.view(), sort);
        }
    }
    let result = f(buf.view_mut());
    // do not keep the handled sorts past the call
    buf.clear();
    result
}

/// Parser for a single datatype constructor.
type ConstructorParser<H> = SmtOpenedParser<
    H,
    SmtPairParser<H, SmtSymbolParser, SmtClosedMultipleParser<H, SmtSortedVarParser<H>>>,
>;

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

enum DatatypeMode {
    Single(Option<SmtSymbolBuf>),
    Multiple,
}

/// Parser for a datatype.
struct DatatypeParser<H: SmtCommandHandler> {
    state: DatatypeState,
    mode: DatatypeMode,

    symbols_parser: SmtParenMultipleParser<H, SmtSymbolParser>,
    constructors_parser: SmtClosedMultipleParser<H, ConstructorParser<H>>,
    constructors: Option<OwnedConstructors<H::Sort>>,
    /// The parameters handed over, reused across datatypes.
    params_buf: SmtSymbolsBuf,
    /// The constructors handed over, reused across datatypes.
    constructors_buf: SmtConstructorsBuf<H>,
}

impl<H: SmtCommandHandler> DatatypeParser<H> {
    fn new() -> Self {
        Self {
            state: DatatypeState::Start,
            mode: DatatypeMode::Multiple,
            symbols_parser: SmtParenMultipleParser::default(),
            constructors_parser: SmtClosedMultipleParser::default(),
            constructors: None,
            params_buf: SmtSymbolsBuf::new(),
            constructors_buf: SmtConstructorsBuf::new(),
        }
    }

    /// Switches this datatype to "single datatype mode".
    fn set_single_datatype_mode(&mut self, name: SmtSymbolBuf) {
        self.mode = DatatypeMode::Single(Some(name))
    }

    /// Starts a datatype, taking into account the "single datatype mode".
    fn start_datatype(
        &mut self,
        handler: &mut H,
        params: Vec<SmtSymbolBuf>,
    ) -> Result<(), SmtParseError<H::Error>> {
        self.params_buf.clear();
        for param in &params {
            self.params_buf.push(param.view());
        }
        match &mut self.mode {
            DatatypeMode::Single(name) => {
                let name = name.take().expect("datatype should be only started once");
                handle_err(handler.start_declare_datatype(name.view(), self.params_buf.view()))
            }
            DatatypeMode::Multiple => {
                handle_err(handler.start_datatype_declaration(self.params_buf.view()))
            }
        }
    }
}

impl<H: SmtCommandHandler> Default for DatatypeParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for DatatypeParser<H> {
    type Result = Option<OwnedConstructors<H::Sort>>;

    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        parse_by_token(cursor, |cursor, token| {
            self.progress(handler, parse_state, cursor, token)
        })
    }
}

impl<H: SmtCommandHandler> DatatypeParser<H> {
    /// Progresses the parser by one token.
    #[allow(clippy::type_complexity)]
    fn progress<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &Z,
        token: Z::Token,
    ) -> Result<ControlFlow<Option<OwnedConstructors<H::Sort>>>, SmtParseError<H::Error>> {
        let constructors = match self.state {
            DatatypeState::Start => {
                // expect opening parenthesis and move to deciding the kind
                SmtOpenParenParser::expect(cursor, token)?;
                self.state = DatatypeState::Kind;
                None
            }
            DatatypeState::Kind => match cursor.syntax(&token) {
                SmtToken::ParenOpen => {
                    // simple constructors, start the datatype with no parameters
                    self.start_datatype(handler, Vec::new())?;
                    self.state = DatatypeState::SimpleConstructors;
                    // this parenthesis already is the start of the constructor,
                    // so we will forward it
                    let result = self.constructors_parser.parse(
                        handler,
                        parse_state,
                        &mut SingleTokenCursor::new(cursor, token),
                    )?;
                    debug_assert!(
                        matches!(result, ControlFlow::Continue(())),
                        "datatype constructor should continue on opening parenthesis"
                    );
                    None
                }
                SmtToken::Reserved(SmtReserved::General(SmtGeneralReserved::Par)) => {
                    // parametric constructors, we need to parse the parameters first
                    self.state = DatatypeState::Parameters;
                    None
                }
                _ => {
                    return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Expected(&[
                        expected::PAR,
                        expected::PAREN_OPEN,
                    ])));
                }
            },
            DatatypeState::SimpleConstructors => {
                // parse the simple constructors
                self.constructors_parser
                    .parse(
                        handler,
                        parse_state,
                        &mut SingleTokenCursor::new(cursor, token),
                    )?
                    .break_value()
            }
            DatatypeState::Parameters => {
                // parse the parameters
                if let ControlFlow::Break(params) = self.symbols_parser.parse(
                    handler,
                    parse_state,
                    &mut SingleTokenCursor::new(cursor, token),
                )? {
                    // there must be at least one parameter
                    if params.is_empty() {
                        return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Empty(
                            SmtNonEmptyList::DatatypeParameters,
                        )));
                    }
                    // start the datatype with the parameters
                    self.start_datatype(handler, params)?;
                    // move to parsing the opening parenthesis of parametric constructors
                    self.state = DatatypeState::ParametricOpen;
                }
                None
            }
            DatatypeState::ParametricOpen => {
                // expect opening parenthesis and move to parsing parametric constructors
                SmtOpenParenParser::expect(cursor, token)?;
                self.state = DatatypeState::ParametricConstructors;
                None
            }
            DatatypeState::ParametricConstructors => {
                // parse the parametric constructors
                self.constructors_parser
                    .parse(
                        handler,
                        parse_state,
                        &mut SingleTokenCursor::new(cursor, token),
                    )?
                    .break_value()
            }
            DatatypeState::Close => {
                let Some(constructors) = self.constructors.take() else {
                    panic!("constructors should be present when closing parametric datatype")
                };
                // expect closing parenthesis
                SmtCloseParenParser::expect(cursor, token)?;

                // end the datatype, this will reset
                let result = self.end_datatype(handler, constructors)?;
                return Ok(ControlFlow::Break(result));
            }
        };

        if let Some(constructors) = constructors {
            // there must be at least one constructor
            if constructors.is_empty() {
                return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Empty(
                    SmtNonEmptyList::DatatypeConstructors,
                )));
            }

            if matches!(self.state, DatatypeState::SimpleConstructors) {
                // end the datatype, this will reset
                let result = self.end_datatype(handler, constructors)?;
                return Ok(ControlFlow::Break(result));
            }
            // we still need to wait for the closing parenthesis,
            // do not end the datatype before it
            self.constructors = Some(constructors);
            self.state = DatatypeState::Close
        }

        Ok(ControlFlow::Continue(()))
    }

    fn end_datatype(
        &mut self,
        handler: &mut H,
        constructors: OwnedConstructors<H::Sort>,
    ) -> Result<Option<OwnedConstructors<H::Sort>>, SmtParseError<H::Error>> {
        // process the datatype
        let result = match self.mode {
            DatatypeMode::Single(_) => {
                // return the datatype
                Ok(Some(constructors))
            }
            DatatypeMode::Multiple => {
                // end the datatype declaration
                handle_err(hand_over_constructors(
                    &mut self.constructors_buf,
                    constructors,
                    |constructors| handler.end_datatype_declaration(constructors),
                ))?;
                Ok(None)
            }
        };
        // reset and return
        self.state = DatatypeState::Start;
        self.mode = DatatypeMode::Multiple;
        result
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
pub(super) struct DeclareDatatypesParser<H: SmtCommandHandler> {
    state: DeclareDatatypesState,

    introductions_parser: SmtParenMultipleParser<H, IntroductionParser<H>>,
    datatypes_parser: SmtParenMaximumParser<H, DatatypeParser<H>>,
    /// The introductions handed over, reused across commands.
    arities_buf: SmtSortAritiesBuf,
}

impl<H: SmtCommandHandler> DeclareDatatypesParser<H> {
    pub(crate) fn new() -> Self {
        // the number of maximum elements for datatypes parser will be
        // resized before each parse, it does not matter in the initial state
        Self {
            state: DeclareDatatypesState::Introductions,
            introductions_parser: SmtParenMultipleParser::default(),
            datatypes_parser: SmtParenMaximumParser::new(DatatypeParser::new(), 0),
            arities_buf: SmtSortAritiesBuf::new(),
        }
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for DeclareDatatypesParser<H> {
    type Result = ();

    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        parse_by_token(cursor, |cursor, token| {
            self.progress(handler, parse_state, cursor, token)
        })
    }
}

impl<H: SmtCommandHandler> DeclareDatatypesParser<H> {
    /// Progresses the parser by one token.
    fn progress<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &Z,
        token: Z::Token,
    ) -> Result<ControlFlow<()>, SmtParseError<H::Error>> {
        match self.state {
            DeclareDatatypesState::Introductions => {
                // parse datatype introductions
                if let ControlFlow::Break(introductions) = self.introductions_parser.parse(
                    handler,
                    parse_state,
                    &mut SingleTokenCursor::new(cursor, token),
                )? {
                    // introductions must not be empty
                    if introductions.is_empty() {
                        return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Empty(
                            SmtNonEmptyList::DatatypeIntroductions,
                        )));
                    }
                    // ensure the datatypes parser is expecting the correct number of elements
                    self.datatypes_parser.set_max_items(introductions.len());
                    // start datatype declarations
                    self.arities_buf.clear();
                    for (name, arity) in &introductions {
                        self.arities_buf.push(name.view(), arity.view());
                    }
                    handle_err(handler.start_declare_datatypes(self.arities_buf.view()))?;
                    self.state = DeclareDatatypesState::Declarations;
                }
            }
            DeclareDatatypesState::Declarations => {
                // parse datatypes
                if let ControlFlow::Break(datatypes) = self.datatypes_parser.parse(
                    handler,
                    parse_state,
                    &mut SingleTokenCursor::new(cursor, token),
                )? {
                    // there cannot be more datatypes than sort declarations due to the maximum parser
                    // ensure there are not more sort declarations than datatypes
                    if datatypes.len() != self.datatypes_parser.max_items() {
                        return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Missing(
                            SmtMissingItem::Datatype,
                        )));
                    }

                    // we are done, reset and break
                    // the datatypes parser can have a changed number of maximum elements,
                    // but it will be changed before it is used next time
                    self.state = DeclareDatatypesState::Introductions;
                    return Ok(ControlFlow::Break(()));
                }
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

impl<H: SmtCommandHandler> Default for DeclareDatatypesParser<H> {
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
pub(super) struct DeclareDatatypeParser<H: SmtCommandHandler> {
    state: DeclareDatatypeState,
    datatype_parser: DatatypeParser<H>,
}

impl<H: SmtCommandHandler> Default for DeclareDatatypeParser<H> {
    fn default() -> Self {
        Self {
            state: DeclareDatatypeState::Name,
            datatype_parser: DatatypeParser::new(),
        }
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for DeclareDatatypeParser<H> {
    type Result = OwnedConstructors<H::Sort>;

    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        parse_by_token(cursor, |cursor, token| {
            self.progress(handler, parse_state, cursor, token)
        })
    }
}

impl<H: SmtCommandHandler> DeclareDatatypeParser<H> {
    /// Progresses the parser by one token.
    fn progress<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &Z,
        token: Z::Token,
    ) -> Result<ControlFlow<OwnedConstructors<H::Sort>>, SmtParseError<H::Error>> {
        match self.state {
            DeclareDatatypeState::Name => {
                // parse the datatype name
                let name = SmtSymbolParser::expect::<H, Z>(cursor, token)?;
                self.datatype_parser.set_single_datatype_mode(name);
                self.state = DeclareDatatypeState::Datatype;
            }
            DeclareDatatypeState::Datatype => {
                if let ControlFlow::Break(constructors) = self.datatype_parser.parse(
                    handler,
                    parse_state,
                    &mut SingleTokenCursor::new(cursor, token),
                )? {
                    // the single declaration ends the command, reset and break
                    self.state = DeclareDatatypeState::Name;
                    let constructors =
                        constructors.expect("single datatype should produce constructors");
                    return Ok(ControlFlow::Break(constructors));
                }
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

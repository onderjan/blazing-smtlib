use std::ops::ControlFlow;

use crate::{
    SmtCommandHandler, SmtDatatypeConstructor, SmtNumeralBuf, SmtSymbolBuf,
    parser::{
        SmtCloseParenParser, SmtClosedMultipleParser, SmtNumeralParser, SmtOpenParenParser,
        SmtOpenedParser, SmtParenMaximumParser, SmtParenMultipleParser, SmtParenParser, SmtParse,
        SmtParseError, SmtParseState, SmtSortedVarParser, SmtSymbolParser, SmtSyntaxErrorKind,
        category::SmtPairParser, handle_err, parse_by_token,
    },
    token::{SingleTokenProducer, SmtGeneralReserved, SmtProduce, SmtReserved, SmtSyntaxToken},
};

/// Parser for a single datatype introduction (name and arity in parentheses).
type IntroductionParser<H> = SmtParenParser<H, SmtPairParser<H, SmtSymbolParser, SmtNumeralParser>>;

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

/// Parser for a datatype.
struct DatatypeParser<H: SmtCommandHandler> {
    state: DatatypeState,
    single_introduction: Option<SmtSymbolBuf>,

    symbols_parser: SmtParenMultipleParser<H, SmtSymbolParser>,
    constructors_parser: SmtClosedMultipleParser<H, ConstructorParser<H>>,
    constructors: Option<Vec<SmtDatatypeConstructor<H>>>,
}

impl<H: SmtCommandHandler> DatatypeParser<H> {
    fn new() -> Self {
        Self {
            state: DatatypeState::Start,
            single_introduction: None,
            symbols_parser: SmtParenMultipleParser::default(),
            constructors_parser: SmtClosedMultipleParser::default(),
            constructors: None,
        }
    }

    /// Switches this datatype to "single datatype mode".
    ///
    /// This mode calls `start_declare_datatypes` as per the definition of
    /// `declare-datatype`, which depends on the form of the single datatype.
    fn set_single_datatype_mode(&mut self, name: SmtSymbolBuf) {
        self.single_introduction = Some(name)
    }

    /// Starts a datatype, taking into account the "single datatype mode".
    fn start_datatype(
        &mut self,
        handler: &mut H,
        params: Vec<SmtSymbolBuf>,
    ) -> Result<(), SmtParseError<H::Error>> {
        if let Some(name) = self.single_introduction.take() {
            // start declare datatypes with the arity equal to the number of parameters
            let arity = SmtNumeralBuf::from_usize(params.len());
            handle_err(handler.start_declare_datatypes(vec![(name, arity)]))?;
        }
        handle_err(handler.start_datatype_declaration(params))
    }
}

impl<H: SmtCommandHandler> Default for DatatypeParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for DatatypeParser<H> {
    type Result = ();

    fn parse<C: SmtProduce>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        parse_by_token(cursor, |cursor, token| {
            self.progress(handler, parse_state, cursor, token)
        })
    }
}

impl<H: SmtCommandHandler> DatatypeParser<H> {
    /// Progresses the parser by one token.
    fn progress<Z: SmtProduce>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &Z,
        token: Z::Token,
    ) -> Result<ControlFlow<()>, SmtParseError<H::Error>> {
        let constructors = match self.state {
            DatatypeState::Start => {
                // expect opening parenthesis and move to deciding the kind
                SmtOpenParenParser::expect(cursor, token)?;
                self.state = DatatypeState::Kind;
                None
            }
            DatatypeState::Kind => match cursor.syntax(&token) {
                SmtSyntaxToken::ParenOpen => {
                    // simple constructors, start the datatype with no parameters
                    self.start_datatype(handler, Vec::new())?;
                    self.state = DatatypeState::SimpleConstructors;
                    // this parenthesis already is the start of the constructor,
                    // so we will forward it
                    let result = self.constructors_parser.parse(
                        handler,
                        parse_state,
                        &mut SingleTokenProducer::new(cursor, token),
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
                    ));
                }
            },
            DatatypeState::SimpleConstructors => {
                // parse the simple constructors
                self.constructors_parser
                    .parse(
                        handler,
                        parse_state,
                        &mut SingleTokenProducer::new(cursor, token),
                    )?
                    .break_value()
            }
            DatatypeState::Parameters => {
                // parse the parameters
                if let ControlFlow::Break(params) = self.symbols_parser.parse(
                    handler,
                    parse_state,
                    &mut SingleTokenProducer::new(cursor, token),
                )? {
                    // there must be at least one parameter
                    if params.is_empty() {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::EmptyDatatypeParameters,
                        ));
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
                        &mut SingleTokenProducer::new(cursor, token),
                    )?
                    .break_value()
            }
            DatatypeState::Close => {
                let Some(constructors) = self.constructors.take() else {
                    panic!("constructors should be present when closing parametric datatype")
                };
                // expect closing parenthesis
                SmtCloseParenParser::expect(cursor, token)?;
                // end the datatype, reset and break
                handle_err(handler.end_datatype_declaration(constructors))?;
                self.state = DatatypeState::Start;
                return Ok(ControlFlow::Break(()));
            }
        };

        if let Some(constructors) = constructors {
            // there must be at least one constructor
            if constructors.is_empty() {
                return Err(SmtParseError::category_error(
                    SmtSyntaxErrorKind::EmptyDatatypeConstructors,
                ));
            }

            // TODO: do not retype the constructors
            let constructors = constructors
                .into_iter()
                .map(|(name, selectors)| SmtDatatypeConstructor { name, selectors })
                .collect();
            if matches!(self.state, DatatypeState::SimpleConstructors) {
                // we have already parsed the closing parenthesis
                // end the datatype declaration, reset and break
                handle_err(handler.end_datatype_declaration(constructors))?;
                self.state = DatatypeState::Start;
                return Ok(ControlFlow::Break(()));
            }
            // we still need to wait for the closing parenthesis,
            // do not end the datatype before it
            self.constructors = Some(constructors);
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
pub(super) struct DeclareDatatypesParser<H: SmtCommandHandler> {
    state: DeclareDatatypesState,

    introductions_parser: SmtParenMultipleParser<H, IntroductionParser<H>>,
    datatypes_parser: SmtParenMaximumParser<H, DatatypeParser<H>>,
}

impl<H: SmtCommandHandler> DeclareDatatypesParser<H> {
    pub fn new() -> Self {
        // the number of maximum elements for datatypes parser will be
        // resized before each parse, it does not matter in the initial state
        Self {
            state: DeclareDatatypesState::Introductions,
            introductions_parser: SmtParenMultipleParser::default(),
            datatypes_parser: SmtParenMaximumParser::new(DatatypeParser::new(), 0),
        }
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for DeclareDatatypesParser<H> {
    type Result = ();

    fn parse<C: SmtProduce>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        parse_by_token(cursor, |cursor, token| {
            self.progress(handler, parse_state, cursor, token)
        })
    }
}

impl<H: SmtCommandHandler> DeclareDatatypesParser<H> {
    /// Progresses the parser by one token.
    fn progress<Z: SmtProduce>(
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
                    &mut SingleTokenProducer::new(cursor, token),
                )? {
                    // introductions must not be empty
                    if introductions.is_empty() {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::EmptyDatatypeIntroductions,
                        ));
                    }
                    // ensure the datatypes parser is expecting the correct number of elements
                    self.datatypes_parser.set_maximum(introductions.len());
                    // start datatype declarations
                    handle_err(handler.start_declare_datatypes(introductions))?;
                    self.state = DeclareDatatypesState::Declarations;
                }
            }
            DeclareDatatypesState::Declarations => {
                // parse datatypes
                if let ControlFlow::Break(datatypes) = self.datatypes_parser.parse(
                    handler,
                    parse_state,
                    &mut SingleTokenProducer::new(cursor, token),
                )? {
                    // there cannot be more datatypes than sort declarations due to the maximum parser
                    // ensure there are not more sort declarations than datatypes
                    if datatypes.len() != self.datatypes_parser.max_elements() {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::ExpectedDatatype,
                        ));
                    }

                    // we are done, reset and break
                    // the datatypes parser can have a changed number of maximum elements,
                    // but it will be changed before it is used next time
                    self.state = DeclareDatatypesState::Introductions;
                    // the call to end datatypes declarations
                    // will be done after the closing parenthesis
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
    type Result = ();

    fn parse<C: SmtProduce>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        parse_by_token(cursor, |cursor, token| {
            self.progress(handler, parse_state, cursor, token)
        })
    }
}

impl<H: SmtCommandHandler> DeclareDatatypeParser<H> {
    /// Progresses the parser by one token.
    fn progress<Z: SmtProduce>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &Z,
        token: Z::Token,
    ) -> Result<ControlFlow<()>, SmtParseError<H::Error>> {
        match self.state {
            DeclareDatatypeState::Name => {
                // parse the datatype name
                let name = SmtSymbolParser::expect::<H, Z>(cursor, token)?;
                self.datatype_parser.set_single_datatype_mode(name);
                self.state = DeclareDatatypeState::Datatype;
            }
            DeclareDatatypeState::Datatype => {
                if let ControlFlow::Break(()) = self.datatype_parser.parse(
                    handler,
                    parse_state,
                    &mut SingleTokenProducer::new(cursor, token),
                )? {
                    // the single declaration ends the command, reset and break
                    // the call to end datatypes declarations
                    // will be done after the closing parenthesis
                    self.state = DeclareDatatypeState::Name;
                    return Ok(ControlFlow::Break(()));
                }
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

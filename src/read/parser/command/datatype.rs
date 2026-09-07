use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtDatatypeConstructor,
    read::parser::{
        CategoryParser, CategoryParserErrorKind, CloseParenParser, ClosedMultipleParser,
        NumeralParser, OpenParenParser, OpenedParser, ParenMaximumParser, ParenMultipleParser,
        ParenParser, ParserError, SortedVarParser, SymbolParser, category::PairParser, handle_err,
    },
    token::{Reserved, Token, TokenKind},
};

/// Parser for a single datatype constructor.
type ConstructorParser<H> =
    OpenedParser<H, PairParser<H, SymbolParser, ClosedMultipleParser<H, SortedVarParser<H>>>>;

type SortDeclarationParser<H> = ParenParser<H, PairParser<H, SymbolParser, NumeralParser>>;

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

    symbols_parser: ParenMultipleParser<H, SymbolParser>,
    constructors_parser: ClosedMultipleParser<H, ConstructorParser<H>>,
}

impl<H: CommandHandler> Default for DatatypeParser<H> {
    fn default() -> Self {
        Self {
            state: DatatypeState::Start,
            symbols_parser: ParenMultipleParser::new(),
            constructors_parser: ClosedMultipleParser::new(),
        }
    }
}

impl<H: CommandHandler> CategoryParser<H> for DatatypeParser<H> {
    type Result = ();

    fn restart(&mut self) {
        self.state = DatatypeState::Start;
        self.symbols_parser.restart();
        self.constructors_parser.restart();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        let span = token.span();
        let constructors = match self.state {
            DatatypeState::Start => {
                // expect opening parenthesis and move to deciding the kind
                OpenParenParser::expect(token)?;
                self.state = DatatypeState::Kind;
                None
            }
            DatatypeState::Kind => match token.kind() {
                TokenKind::ParenOpen => {
                    // simple constructors, start the datatype with no parameters
                    handle_err(handler.start_datatype(Vec::new()), span)?;
                    self.state = DatatypeState::SimpleConstructors;
                    // this parenthesis already is the start of the constructor,
                    // so we will forward it
                    let result = self.constructors_parser.progress(handler, token)?;
                    debug_assert!(
                        matches!(result, ControlFlow::Continue(())),
                        "datatype constructor should continue on opening parenthesis"
                    );
                    None
                }
                TokenKind::Reserved(Reserved::Par) => {
                    // parametric constructors, we need to parse the parameters first
                    self.state = DatatypeState::Parameters;
                    None
                }
                _ => {
                    return Err(ParserError::category_error(
                        CategoryParserErrorKind::ExpectedDatatypeKind,
                        span,
                    ));
                }
            },
            DatatypeState::SimpleConstructors => {
                // parse the simple constructors
                self.constructors_parser
                    .progress(handler, token)?
                    .break_value()
            }
            DatatypeState::Parameters => {
                // parse the parameters
                if let ControlFlow::Break(params) = self.symbols_parser.progress(handler, token)? {
                    // there must be at least one parameter
                    if params.is_empty() {
                        return Err(ParserError::category_error(
                            CategoryParserErrorKind::EmptyDatatypeParameters,
                            span,
                        ));
                    }
                    // start the datatype with the parameters
                    handle_err(handler.start_datatype(params), span)?;
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
                    .progress(handler, token)?
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
                return Err(ParserError::category_error(
                    CategoryParserErrorKind::EmptyDatatypeConstructors,
                    span,
                ));
            }

            // TODO: do not retype the constructors
            let constructors = constructors
                .into_iter()
                .map(|(name, selectors)| SmtDatatypeConstructor { name, selectors })
                .collect();
            // end the datatype
            handle_err(handler.end_datatype(constructors), span)?;
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
enum State {
    /// Parsing the sort declarations.
    SortDeclarations,
    /// Parsing the datatype declarations.
    DatatypeDeclarations,
}

pub(super) struct DeclareDatatypesParser<H: CommandHandler, const SINGLE: bool> {
    state: State,
    num_expected_declarations: usize,

    sort_declarations_parser: ParenMultipleParser<H, SortDeclarationParser<H>>,
    datatypes_parser: ParenMaximumParser<H, DatatypeParser<H>>,
}

impl<H: CommandHandler, const SINGLE: bool> Default for DeclareDatatypesParser<H, SINGLE> {
    fn default() -> Self {
        Self {
            state: State::SortDeclarations,
            num_expected_declarations: 0,

            sort_declarations_parser: ParenMultipleParser::new(),
            datatypes_parser: ParenMaximumParser::new(),
        }
    }
}

impl<H: CommandHandler, const SINGLE: bool> CategoryParser<H>
    for DeclareDatatypesParser<H, SINGLE>
{
    type Result = ();

    fn restart(&mut self) {
        self.state = State::SortDeclarations;
        self.num_expected_declarations = 0;
        self.sort_declarations_parser.restart();
        self.datatypes_parser.start(0);
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        let span = token.span();
        match self.state {
            State::SortDeclarations => {
                // parse sort declarations
                if let ControlFlow::Break(sort_declarations) =
                    self.sort_declarations_parser.progress(handler, token)?
                {
                    // sort declarations must not be empty
                    if sort_declarations.is_empty() {
                        return Err(ParserError::category_error(
                            CategoryParserErrorKind::EmptyDatatypeSortDeclarations,
                            span,
                        ));
                    }
                    // ensure we and the datatypes parser are expecting the correct number of elements
                    self.num_expected_declarations = sort_declarations.len();
                    self.datatypes_parser.start(self.num_expected_declarations);
                    // start datatype declarations
                    handle_err(handler.start_declare_datatypes(sort_declarations), span)?;
                    self.state = State::DatatypeDeclarations;
                }
            }
            State::DatatypeDeclarations => {
                // parse datatypes
                if let ControlFlow::Break(datatypes) =
                    self.datatypes_parser.progress(handler, token)?
                {
                    // there cannot be more datatypes than sort declarations due to the maximum parser
                    // ensure there are not more sort declarations than datatypes
                    if datatypes.len() != self.num_expected_declarations {
                        return Err(ParserError::category_error(
                            CategoryParserErrorKind::ExpectedDatatype,
                            span,
                        ));
                    }

                    // end datatypes declarations, reset, and break
                    handle_err(handler.end_declare_datatypes(), span)?;
                    self.num_expected_declarations = 0;
                    self.state = State::SortDeclarations;
                    return Ok(ControlFlow::Break(()));
                }
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

//! Tests of parsers and command rules written outside the library: the
//! errors such a parser returns reach the reader's caller with their cause
//! and the span of the token it failed at, and a command rule is a value of
//! its own for each command, chosen by the handler from the command's name.
//!
//! They check the Rust interface itself (parsers implementing `SmtParse`,
//! rules implementing `SmtCommandRule`), so they run the Rust library
//! whatever `parse_backend` selects.

use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtAttributeValue, SmtAttributes, SmtBindings, SmtHandler, SmtKeyword, SmtMatchCases,
    SmtPartialCommandError, SmtPartialCommandHandler, SmtPattern, SmtQuantifierKind, SmtSExpr,
    SmtSort, SmtSortedVars, SmtSymbol, SmtSymbolBuf, SmtTerm,
    parser::{
        SmtClosedParser, SmtCommandPayloadParser, SmtCommandRule, SmtParse, SmtParseError,
        SmtParseState, SmtSyntaxErrorKind, SmtSyntaxExpected, SmtTermParser, SmtVersionErrorKind,
    },
    reader::{SmtReadError, SmtReadErrorCause, SmtReader, read_smt},
    token::{SmtCursor, SmtSyntaxToken, SmtVersion},
};

/// The error of the handlers' own.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Refused;

type Error = SmtPartialCommandError<Refused>;

/// Implements `SmtHandler` for a handler with a field `terms`: every term is
/// numbered by the order in which the handler is given it, from one, and
/// every other category is a unit.
macro_rules! numbering_handler {
    ($handler:ty) => {
        impl SmtHandler for $handler {
            type Error = Error;
            type SExpr = ();
            type Attribute = ();
            type Sort = ();
            type Term = u64;
            type Scope = ();

            fn set_version(&mut self, _version: SmtVersion) {}

            fn handle_sort(&mut self, _sort: SmtSort<'_, Self>) -> Result<(), Error> {
                Ok(())
            }
            fn handle_term(&mut self, _term: SmtTerm<'_, Self>) -> Result<u64, Error> {
                self.terms += 1;
                Ok(self.terms)
            }
            fn handle_s_expr(&mut self, _expr: SmtSExpr<'_, Self>) -> Result<(), Error> {
                Ok(())
            }
            fn handle_attribute(
                &mut self,
                _name: SmtKeyword<'_>,
                _value: Option<SmtAttributeValue<'_, Self>>,
            ) -> Result<(), Error> {
                Ok(())
            }
            fn annotate_term(
                &mut self,
                term: u64,
                _attributes: SmtAttributes<'_, Self>,
            ) -> Result<u64, Error> {
                Ok(term)
            }
            fn start_let(&mut self, _bindings: SmtBindings<'_, u64>) -> Result<(), Error> {
                Ok(())
            }
            fn end_let(&mut self, _scope: (), body: u64) -> Result<u64, Error> {
                Ok(body)
            }
            fn start_quantifier(
                &mut self,
                _kind: SmtQuantifierKind,
                _vars: SmtSortedVars<'_, ()>,
            ) -> Result<(), Error> {
                Ok(())
            }
            fn end_quantifier(
                &mut self,
                _kind: SmtQuantifierKind,
                _scope: (),
                body: u64,
            ) -> Result<u64, Error> {
                Ok(body)
            }
            fn start_lambda(&mut self, _vars: SmtSortedVars<'_, ()>) -> Result<(), Error> {
                Ok(())
            }
            fn end_lambda(&mut self, _scope: (), body: u64) -> Result<u64, Error> {
                Ok(body)
            }
            fn start_match(&mut self, _scrutinee: &u64) -> Result<(), Error> {
                Ok(())
            }
            fn start_match_case(
                &mut self,
                _scrutinee: &u64,
                _pattern: SmtPattern<'_>,
            ) -> Result<(), Error> {
                Ok(())
            }
            fn end_match_case(
                &mut self,
                _scope: (),
                _scrutinee: &u64,
                term: u64,
            ) -> Result<u64, Error> {
                Ok(term)
            }
            fn end_match(
                &mut self,
                scrutinee: u64,
                _cases: SmtMatchCases<'_, Self>,
            ) -> Result<u64, Error> {
                Ok(scrutinee)
            }
        }
    };
}

// --- A parser that fails with each cause ---

/// A parser of symbols up to a closing parenthesis or the end of file, one
/// token at a time, that fails at the symbols `syntax`, `handler` and
/// `version` with an error of that cause.
#[derive(Default)]
struct Failing {
    taken: usize,
}

impl<H: SmtHandler<Error = Error>> SmtParse<H> for Failing {
    type Result = usize;

    fn parse<Z: SmtCursor>(
        &mut self,
        _handler: &mut H,
        _parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<usize>, SmtParseError<Error>> {
        while let Some(token) = cursor.next() {
            self.taken += 1;
            match cursor.syntax(&token) {
                SmtSyntaxToken::ParenClose | SmtSyntaxToken::EndOfFile => {
                    return Ok(ControlFlow::Break(std::mem::take(&mut self.taken)));
                }
                SmtSyntaxToken::Symbol(symbol) => match symbol.as_slice() {
                    b"syntax" => {
                        return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Expected(&[
                            SmtSyntaxExpected::Term,
                        ])));
                    }
                    b"handler" => {
                        return Err(SmtParseError::handler(SmtPartialCommandError::Handler(
                            Refused,
                        )));
                    }
                    b"version" => {
                        return Err(SmtParseError::version(SmtVersionErrorKind::Unsupported));
                    }
                    _ => {}
                },
                _ => {
                    return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Expected(&[
                        SmtSyntaxExpected::Symbol,
                    ])));
                }
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// A handler that parses every nonstandard command with `Failing`.
#[derive(Default)]
struct Custom {
    terms: u64,
}

numbering_handler!(Custom);

/// The command payload of `Failing`, whose count of tokens is dropped.
struct Payload(Failing);

impl SmtParse<Custom> for Payload {
    type Result = ();

    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut Custom,
        parse_state: &mut SmtParseState<Custom>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<()>, SmtParseError<Error>> {
        Ok(self
            .0
            .parse(handler, parse_state, cursor)?
            .map_break(|_| ()))
    }
}

impl SmtPartialCommandHandler for Custom {
    type HandlerError = Refused;
    type NonstandardParser = Payload;

    fn nonstandard_command(&mut self, _name: SmtSymbol<'_>) -> Result<Payload, Error> {
        Ok(Payload(Failing::default()))
    }
}

/// Byte offsets of the start and the end of the error's span.
fn offsets<E>(err: &SmtReadError<E>) -> (u64, u64) {
    (err.span().start().offset(), err.span().end().offset())
}

#[test]
fn errors_of_a_parser_read_directly_reach_the_caller_with_their_cause() {
    // without an error, the parser finishes at the end of file
    let mut handler = Custom::default();
    let taken = SmtReader::new(&mut handler, Failing::default(), SmtVersion::V2_7)
        .read_all(&b"a b"[..])
        .unwrap_or_else(|err| panic!("unexpected error {:?}", err.cause()));
    assert_eq!(taken, 3);

    // each error spans the token the parser failed at
    let input = b"a syntax b";
    let err = SmtReader::new(&mut handler, Failing::default(), SmtVersion::V2_7)
        .read_all(&input[..])
        .expect_err("the parser fails at `syntax`");
    assert!(
        matches!(
            err.cause(),
            SmtReadErrorCause::Syntax(kind)
                if *kind == SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Term])
        ),
        "{:?}",
        err.cause()
    );
    assert_eq!(offsets(&err), (2, 8));

    let input = b"a b handler";
    let err = SmtReader::new(&mut handler, Failing::default(), SmtVersion::V2_7)
        .read_all(&input[..])
        .expect_err("the parser fails at `handler`");
    assert!(
        matches!(
            err.cause(),
            SmtReadErrorCause::Handler(SmtPartialCommandError::Handler(Refused))
        ),
        "{:?}",
        err.cause()
    );
    assert_eq!(offsets(&err), (4, 11));

    let input = b"version";
    let err = SmtReader::new(&mut handler, Failing::default(), SmtVersion::V2_7)
        .read_all(&input[..])
        .expect_err("the parser fails at `version`");
    assert!(
        matches!(
            err.cause(),
            SmtReadErrorCause::Version(SmtVersionErrorKind::Unsupported)
        ),
        "{:?}",
        err.cause()
    );
    assert_eq!(offsets(&err), (0, 7));
}

#[test]
fn errors_of_a_nonstandard_command_parser_reach_the_caller_with_their_cause() {
    // without an error, the command ends at its closing parenthesis
    read_smt(&mut Custom::default(), &b"(foo a b) (bar)"[..])
        .unwrap_or_else(|err| panic!("unexpected error {:?}", err.cause()));

    let cases: [(&[u8], (u64, u64)); 3] = [
        (b"(foo) (bar a syntax)", (13, 19)),
        (b"(foo handler)", (5, 12)),
        (b"(foo a)\n(foo version)", (13, 20)),
    ];
    for (input, span) in cases {
        let text = String::from_utf8_lossy(input);
        let err = read_smt(&mut Custom::default(), input)
            .expect_err("the nonstandard command parser fails");
        let cause_matches = match err.cause() {
            SmtReadErrorCause::Syntax(kind) => {
                input.ends_with(b"syntax)")
                    && *kind == SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Term])
            }
            SmtReadErrorCause::Handler(SmtPartialCommandError::Handler(Refused)) => {
                input.ends_with(b"handler)")
            }
            SmtReadErrorCause::Version(kind) => {
                input.ends_with(b"version)") && *kind == SmtVersionErrorKind::Unsupported
            }
            _ => false,
        };
        assert!(cause_matches, "{:?} in {text:?}", err.cause());
        assert_eq!(offsets(&err), span, "in {text:?}");
    }
}

// --- Command rules as values ---

/// Whether an objective is minimised or maximised.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Direction {
    Minimize,
    Maximize,
}

/// The rule of the commands `minimize` and `maximize`: the direction comes
/// from the command's name, and the name is handed over with the term.
struct Objective {
    direction: Direction,
    name: Option<SmtSymbolBuf>,
}

impl SmtCommandRule<Optimizer> for Objective {
    type Parser = SmtClosedParser<Optimizer, SmtTermParser<Optimizer>>;

    fn handle(&mut self, handler: &mut Optimizer, term: u64) -> Result<(), Error> {
        let name = self
            .name
            .take()
            .expect("a rule value handles a single command");
        handler.objectives.push((self.direction, name, term));
        Ok(())
    }
}

/// A handler of the objectives of optimisation, as nonstandard commands.
#[derive(Default)]
struct Optimizer {
    terms: u64,
    objectives: Vec<(Direction, SmtSymbolBuf, u64)>,
}

numbering_handler!(Optimizer);

impl SmtPartialCommandHandler for Optimizer {
    type HandlerError = Refused;
    type NonstandardParser = SmtCommandPayloadParser<Optimizer, Objective>;

    fn nonstandard_command(
        &mut self,
        name: SmtSymbol<'_>,
    ) -> Result<Self::NonstandardParser, Error> {
        let direction = match name.as_slice() {
            b"minimize" => Direction::Minimize,
            b"maximize" => Direction::Maximize,
            _ => {
                return Err(SmtPartialCommandError::UnsupportedNonstandard(
                    name.into_owned(),
                ));
            }
        };
        let rule = Objective {
            direction,
            name: Some(name.into_owned()),
        };
        Ok(SmtCommandPayloadParser::with_rule(rule))
    }
}

#[test]
fn each_command_is_handled_by_its_own_rule_value() {
    let mut handler = Optimizer::default();
    read_smt(
        &mut handler,
        &b"(minimize x) (maximize |y|) (minimize (f z))"[..],
    )
    .unwrap_or_else(|err| panic!("unexpected error {:?}", err.cause()));

    let objectives: Vec<(Direction, &[u8], u64)> = handler
        .objectives
        .iter()
        .map(|(direction, name, term)| (*direction, name.as_slice(), *term))
        .collect();
    // `(f z)` is the fourth term the handler is given, after `z`
    assert_eq!(
        objectives,
        [
            (Direction::Minimize, b"minimize" as &[u8], 1),
            (Direction::Maximize, b"maximize", 2),
            (Direction::Minimize, b"minimize", 4),
        ]
    );

    // a name without a rule is refused by the handler
    let err = read_smt(&mut Optimizer::default(), &b"(minimize x) (optimize y)"[..])
        .expect_err("`optimize` has no rule");
    assert!(
        matches!(
            err.cause(),
            SmtReadErrorCause::Handler(SmtPartialCommandError::UnsupportedNonstandard(name))
                if name.as_slice() == b"optimize"
        ),
        "{:?}",
        err.cause()
    );
    assert_eq!(offsets(&err), (14, 22));
}

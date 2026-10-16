//! The parser and reader that the black-box parser tests run against.
//!
//! By default they are the Rust library's, called directly. When the
//! environment variable `BLAZING_SMTLIB_LEAN_DRIVER` holds the path of the
//! Lean driver executable, the same inputs are sent to that driver instead,
//! which runs the Lean library's parser and reader, so the same tests check
//! the Lean port. The protocol is described in `lean/driver-protocol.md`,
//! section "The parser". The environment variable `BLAZING_SMTLIB_LEAN_LEXER`
//! chooses the Lean lexer under the parser, as for the lexer tests. Under
//! `v`, the naive lexer, which gives a syntax or a handler error a span of
//! its own, the tests that check the span of such an error are reported as
//! not applicable (see `consumer_spans_not_applicable`); every other test
//! runs unchanged.
//!
//! The tests write their handlers against the interface of `nodes`, whose
//! arguments are owned values: the Rust parser calls such a handler through
//! an adapter, the Lean parser through the driver, which asks the Rust side
//! for every handler call, so that the handler and its values stay in Rust.
//! Errors and locations are reported in plain values (`ReadError`,
//! `Location`), as the library's cannot be built from the driver's answer.
//!
//! The tests that run through this module are those of `tests/parser.rs`,
//! `tests/commands.rs`, `tests/read.rs`, `tests/reserved.rs`,
//! `tests/version.rs` and `tests/category`, except the few that check the
//! Rust interface itself; those say so. `tests/nodes.rs`, `tests/plain.rs`,
//! `tests/syntax_checker.rs` (the library's `SmtSyntaxChecker`, for which
//! `SyntaxChecker` below stands in) and the corpus sweeps test the Rust
//! library whatever the variable says.

// Every test file that includes this module uses its own part of it.
#![allow(dead_code)]

mod lean;
pub mod nodes;
mod rust;

use std::io::{BufRead, Write};
use std::marker::PhantomData;
use std::ops::ControlFlow;
use std::path::Path;

use blazing_smtlib::{
    SmtIdentBuf, SmtKeywordBuf, SmtLocation, SmtNonstandardCommandError, SmtNumeralBuf,
    SmtPatternBuf, SmtQuantifierKind, SmtSpan, SmtStringContentBuf, SmtSymbolBuf,
    lexer::{SmtLexErrorCause, SmtLexer, SmtLexicalErrorKind},
    parser::{
        SmtCloseParenParser, SmtClosedAttributeParser, SmtClosedMultipleAttributeParser,
        SmtClosedMultipleParser, SmtClosedParser, SmtCommandOutcome, SmtCommandParser,
        SmtIdentParser, SmtKeywordParser, SmtOpenParenParser, SmtPairParser,
        SmtParenMultipleParser, SmtParenParser, SmtParse, SmtParseError, SmtParseErrorCause,
        SmtParseState, SmtQualifiedIdentParser, SmtSExprParser, SmtScriptParser, SmtSortParser,
        SmtStringParser, SmtSymbolParser, SmtSyntaxErrorKind, SmtTermParser, SmtTuple3Parser,
        SmtTuple4Parser, SmtTuple5Parser, SmtTuple6Parser, SmtTuple7Parser, SmtTuple8Parser,
        SmtVersionErrorKind,
    },
    reader::{SmtReadError, SmtReadErrorCause, SmtReader},
    token::{
        SmtBatchCursor, SmtConsume, SmtConsumeFrom, SmtCursor, SmtTokenCategory, SmtVersion,
        SmtVersionPosture,
    },
};

pub use nodes::*;
pub use rust::Adapt;

/// Whether the tests run against the Lean driver.
pub fn lean_driver() -> Option<std::ffi::OsString> {
    std::env::var_os("BLAZING_SMTLIB_LEAN_DRIVER")
}

/// The Lean lexers that give an error of their consumer (a syntax or a
/// handler error) a span of their own: an empty span at the end of the token
/// the consumer failed on, where the Rust lexer gives the span of the token.
const OWN_CONSUMER_SPAN_LEXERS: [&str; 1] = ["v"];

/// Whether the tests run against a Lean lexer that gives an error of its
/// consumer a span of its own: the one the environment variable
/// `BLAZING_SMTLIB_LEAN_LEXER` selects in the driver is one of
/// `OWN_CONSUMER_SPAN_LEXERS`. The driver answers with the library's lexer
/// when the variable is unset.
pub fn own_consumer_spans() -> bool {
    lean_driver().is_some()
        && std::env::var("BLAZING_SMTLIB_LEAN_LEXER")
            .is_ok_and(|lexer| OWN_CONSUMER_SPAN_LEXERS.contains(&lexer.as_str()))
}

/// Whether the calling test is to end here, as it checks the span of a
/// syntax or a handler error and the lexer under test gives such an error a
/// span of its own (see `own_consumer_spans`). A test that checks such a
/// span calls this first and returns if it is true.
///
/// The test is then reported as not applicable on the standard error, past
/// the output capture of the test harness, so that the report shows in
/// every run.
pub fn consumer_spans_not_applicable() -> bool {
    if !own_consumer_spans() {
        return false;
    }
    let thread = std::thread::current();
    let test = thread.name().unwrap_or("a test");
    let report = format!(
        "{test}: not applicable, the Lean lexer under test gives syntax and handler errors \
         spans of its own\n"
    );
    // one write, so that the line is not split by the output of other tests; a failed write
    // only loses the report, the test itself is not affected
    let _ = std::io::stderr().lock().write_all(report.as_bytes());
    true
}

// --- Locations and errors as plain values ---

/// A location: a byte offset with its zero-based line and column.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
    offset: u64,
    line: u64,
    column: u64,
}

impl Location {
    pub fn new(offset: u64, line: u64, column: u64) -> Self {
        Location {
            offset,
            line,
            column,
        }
    }

    pub fn offset(&self) -> u64 {
        self.offset
    }

    pub fn line(&self) -> u64 {
        self.line
    }

    pub fn column(&self) -> u64 {
        self.column
    }
}

impl From<SmtLocation> for Location {
    fn from(location: SmtLocation) -> Self {
        Location::new(location.offset(), location.line(), location.column())
    }
}

/// The span of an error, from its start to its end.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    start: Location,
    end: Location,
}

impl Span {
    pub fn new(start: Location, end: Location) -> Self {
        Span { start, end }
    }

    pub fn start(&self) -> Location {
        self.start
    }

    pub fn end(&self) -> Location {
        self.end
    }
}

impl From<SmtSpan> for Span {
    fn from(span: SmtSpan) -> Self {
        Span::new(span.start().into(), span.end().into())
    }
}

/// Why reading failed (`SmtReadErrorCause`). An I/O error is reported by its
/// message.
#[derive(Debug)]
pub enum ReadErrorCause<E> {
    Io(String),
    Lexical(SmtLexicalErrorKind),
    Syntax(SmtSyntaxErrorKind),
    Version(SmtVersionErrorKind),
    Handler(E),
}

/// An error that ended reading, with its span (`SmtReadError`).
#[derive(Debug)]
pub struct ReadError<E> {
    cause: ReadErrorCause<E>,
    span: Span,
}

impl<E> ReadError<E> {
    pub fn new(cause: ReadErrorCause<E>, span: Span) -> Self {
        ReadError { cause, span }
    }

    pub fn cause(&self) -> &ReadErrorCause<E> {
        &self.cause
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn into_cause(self) -> ReadErrorCause<E> {
        self.cause
    }
}

impl<E> From<SmtReadError<E>> for ReadError<E> {
    fn from(err: SmtReadError<E>) -> Self {
        let span = err.span().into();
        let cause = match err.into_cause() {
            SmtReadErrorCause::Io(err) => ReadErrorCause::Io(err.to_string()),
            SmtReadErrorCause::Lexical(kind) => ReadErrorCause::Lexical(kind),
            SmtReadErrorCause::Syntax(kind) => ReadErrorCause::Syntax(kind),
            SmtReadErrorCause::Version(kind) => ReadErrorCause::Version(kind),
            SmtReadErrorCause::Handler(err) => ReadErrorCause::Handler(err),
        };
        ReadError::new(cause, span)
    }
}

/// A result with the location where it was finished (`SmtLocated`).
#[derive(Debug)]
pub struct Located<V> {
    value: V,
    location: Location,
}

impl<V> Located<V> {
    pub fn value(&self) -> &V {
        &self.value
    }

    pub fn location(&self) -> Location {
        self.location
    }

    pub fn into_value(self) -> V {
        self.value
    }
}

// --- The handler of the library's syntax checker ---

/// A handler that accepts everything and rejects every nonstandard command,
/// as the library's `SmtSyntaxChecker` does.
#[derive(Debug, Default)]
pub struct SyntaxChecker;

impl Handler for SyntaxChecker {
    type Error = SmtNonstandardCommandError;
    type SExpr = ();
    type Attribute = ();
    type Sort = ();
    type Term = ();
    type Scope = ();

    fn set_version(&mut self, _version: SmtVersion) {}
    fn handle_sort(&mut self, _sort: Sort<()>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn handle_term(&mut self, _term: Term<(), ()>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn handle_s_expr(&mut self, _expr: SExpr<()>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn handle_attribute(
        &mut self,
        _name: SmtKeywordBuf,
        _value: Option<AttributeValue<()>>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn annotate_term(&mut self, _term: (), _attributes: Vec<()>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_let(&mut self, _bindings: Bindings<()>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_let(&mut self, _scope: (), _body: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _vars: SortedVars<()>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _scope: (),
        _body: (),
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_lambda(&mut self, _vars: SortedVars<()>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_lambda(&mut self, _scope: (), _body: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_match(&mut self, _scrutinee: &()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_match_case(
        &mut self,
        _scrutinee: &(),
        _pattern: SmtPatternBuf,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_match_case(
        &mut self,
        _scope: (),
        _scrutinee: &(),
        _term: (),
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_match(&mut self, _scrutinee: (), _cases: MatchCases<()>) -> Result<(), Self::Error> {
        Ok(())
    }
}

impl CommandHandler for SyntaxChecker {
    fn nonstandard_command(
        &mut self,
        name: SmtSymbolBuf,
    ) -> Result<NonstandardPayload, Self::Error> {
        Err(SmtNonstandardCommandError::new(name))
    }
    fn nonstandard_term(&mut self, _term: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_echo(&mut self, _value: SmtStringContentBuf) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_get_option(&mut self, _option: SmtKeywordBuf) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_set_option(&mut self, _option: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_get_info(&mut self, _keyword: SmtKeywordBuf) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_set_info(&mut self, _attribute: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_set_logic(&mut self, _logic: SmtSymbolBuf) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_get_value(&mut self, _terms: Vec<()>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_get_assertions(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_get_assignment(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_get_model(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_get_proof(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_get_unsat_assumptions(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_get_unsat_core(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_declare_sort(
        &mut self,
        _name: SmtSymbolBuf,
        _arity: SmtNumeralBuf,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_declare_sort_parameter(&mut self, _name: SmtSymbolBuf) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_declare_const(&mut self, _name: SmtSymbolBuf, _sort: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_declare_fun(
        &mut self,
        _name: SmtSymbolBuf,
        _param_sorts: Vec<()>,
        _result_sort: (),
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_assert(&mut self, _term: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_check_sat(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_check_sat_assuming(&mut self, _assumptions: Vec<()>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_reset(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_reset_assertions(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_exit(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_push(&mut self, _amount: SmtNumeralBuf) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_pop(&mut self, _amount: SmtNumeralBuf) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_define_sort(
        &mut self,
        _name: SmtSymbolBuf,
        _params: Symbols,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_define_sort(&mut self, _sort: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_define_fun(&mut self, _signature: Signature<'_, ()>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn command_define_const(
        &mut self,
        _name: SmtSymbolBuf,
        _sort: (),
        _body: (),
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_define_fun(&mut self, _term: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_define_fun_rec(&mut self, _signature: Signature<'_, ()>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_define_fun_rec(&mut self, _body: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_define_funs_rec(
        &mut self,
        _signatures: Signatures<'_, ()>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_define_funs_rec(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_recursive_body(&mut self, _signature: Signature<'_, ()>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_recursive_body(&mut self, _term: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_declare_datatype(
        &mut self,
        _name: SmtSymbolBuf,
        _params: Symbols,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_declare_datatype(&mut self, _constructors: Constructors<()>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_declare_datatypes(&mut self, _introductions: SortArities) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_declare_datatypes(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_datatype_declaration(&mut self, _sort_params: Symbols) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_datatype_declaration(
        &mut self,
        _constructors: Constructors<()>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
}

// --- The parsers a reader runs ---

/// A parser that a reader runs over its input: the script parser, or one of
/// the parsers of the categories that a reader may parse alone.
pub trait TopParser<H: CommandHandler> {
    /// What the parser finishes with.
    type Result;
    /// The Rust library's parser.
    type Rust<'h>: SmtParse<Adapt<'h, H>>
    where
        H: 'h;

    fn rust<'h>(&self) -> Self::Rust<'h>
    where
        H: 'h;
    fn from_rust<'h>(result: <Self::Rust<'h> as SmtParse<Adapt<'h, H>>>::Result) -> Self::Result
    where
        H: 'h;
    /// The parser as the driver's `reader` request names it.
    fn lean_name(&self) -> String;
    /// The result from the driver's `<result>` field.
    fn from_lean(result: &str, values: &mut lean::Values<H>) -> Self::Result;
}

/// The parser of a script, under a version posture (`SmtScriptParser`).
pub struct ScriptParser(pub SmtVersionPosture);

/// The parser of one command (`SmtCommandParser`).
#[derive(Default)]
pub struct CommandParser;

/// The parser of one term (`SmtTermParser`).
#[derive(Default)]
pub struct TermParser;

/// The parser of one sort (`SmtSortParser`).
#[derive(Default)]
pub struct SortParser;

/// The parser of one s-expression (`SmtSExprParser`).
#[derive(Default)]
pub struct SExprParser;

fn version_name(version: SmtVersion) -> &'static str {
    std::str::from_utf8(version.as_decimal().as_slice()).expect("a version decimal is ASCII")
}

impl<H: CommandHandler> TopParser<H> for ScriptParser {
    type Result = ();
    type Rust<'h>
        = SmtScriptParser<Adapt<'h, H>>
    where
        H: 'h;

    fn rust<'h>(&self) -> Self::Rust<'h>
    where
        H: 'h,
    {
        SmtScriptParser::new(self.0.clone())
    }
    fn from_rust<'h>(result: ())
    where
        H: 'h,
    {
        result
    }
    fn lean_name(&self) -> String {
        let allowed: Vec<&str> = self.0.allowed().iter().copied().map(version_name).collect();
        let limit = match self.0.max_declarations() {
            Some(limit) => limit.to_string(),
            None => "-".to_string(),
        };
        format!("script:{};{limit}", allowed.join(","))
    }
    fn from_lean(result: &str, _values: &mut lean::Values<H>) {
        assert_eq!(result, "-", "the Lean driver sent a bad script result");
    }
}

impl<H: CommandHandler> TopParser<H> for CommandParser {
    type Result = SmtCommandOutcome;
    type Rust<'h>
        = SmtCommandParser<Adapt<'h, H>>
    where
        H: 'h;

    fn rust<'h>(&self) -> Self::Rust<'h>
    where
        H: 'h,
    {
        SmtCommandParser::new()
    }
    fn from_rust<'h>(result: SmtCommandOutcome) -> SmtCommandOutcome
    where
        H: 'h,
    {
        result
    }
    fn lean_name(&self) -> String {
        "command".into()
    }
    fn from_lean(result: &str, _values: &mut lean::Values<H>) -> SmtCommandOutcome {
        lean::command_outcome(result)
    }
}

impl<H: CommandHandler> TopParser<H> for TermParser {
    type Result = H::Term;
    type Rust<'h>
        = SmtTermParser<Adapt<'h, H>>
    where
        H: 'h;

    fn rust<'h>(&self) -> Self::Rust<'h>
    where
        H: 'h,
    {
        SmtTermParser::new()
    }
    fn from_rust<'h>(result: H::Term) -> H::Term
    where
        H: 'h,
    {
        result
    }
    fn lean_name(&self) -> String {
        "term".into()
    }
    fn from_lean(result: &str, values: &mut lean::Values<H>) -> H::Term {
        values.take_term(lean::value_id(result))
    }
}

impl<H: CommandHandler> TopParser<H> for SortParser {
    type Result = H::Sort;
    type Rust<'h>
        = SmtSortParser<Adapt<'h, H>>
    where
        H: 'h;

    fn rust<'h>(&self) -> Self::Rust<'h>
    where
        H: 'h,
    {
        SmtSortParser::default()
    }
    fn from_rust<'h>(result: H::Sort) -> H::Sort
    where
        H: 'h,
    {
        result
    }
    fn lean_name(&self) -> String {
        "sort".into()
    }
    fn from_lean(result: &str, values: &mut lean::Values<H>) -> H::Sort {
        values.take_sort(lean::value_id(result))
    }
}

impl<H: CommandHandler> TopParser<H> for SExprParser {
    type Result = H::SExpr;
    type Rust<'h>
        = SmtSExprParser<Adapt<'h, H>>
    where
        H: 'h;

    fn rust<'h>(&self) -> Self::Rust<'h>
    where
        H: 'h,
    {
        SmtSExprParser::new()
    }
    fn from_rust<'h>(result: H::SExpr) -> H::SExpr
    where
        H: 'h,
    {
        result
    }
    fn lean_name(&self) -> String {
        "s-expr".into()
    }
    fn from_lean(result: &str, values: &mut lean::Values<H>) -> H::SExpr {
        values.take_s_expr(lean::value_id(result))
    }
}

// --- The reader ---

enum Backend<'h, H: CommandHandler, P: TopParser<H>> {
    Rust(Box<SmtReader<'h, Adapt<'h, H>, P::Rust<'h>>>),
    Lean(lean::Session<'h, H>),
}

/// Streams input to a handler through a parser (`SmtReader`), of the Rust
/// library or of the Lean port.
pub struct Reader<'h, H: CommandHandler, P: TopParser<H>> {
    backend: Backend<'h, H, P>,
    parser: PhantomData<P>,
}

impl<'h, H: CommandHandler> Reader<'h, H, ScriptParser> {
    /// A reader of a script (`SmtReader::script`).
    pub fn script(handler: &'h mut H, posture: SmtVersionPosture, version: SmtVersion) -> Self {
        Reader::new(handler, ScriptParser(posture), version)
    }
}

impl<'h, H: CommandHandler, P: TopParser<H>> Reader<'h, H, P> {
    /// A reader of what the parser accepts (`SmtReader::new`).
    pub fn new(handler: &'h mut H, parser: P, version: SmtVersion) -> Self {
        let backend = match lean_driver() {
            Some(path) => Backend::Lean(lean::Session::open(
                path,
                handler,
                &parser.lean_name(),
                version,
            )),
            None => {
                // the library's reader borrows its handler for as long as it
                // lives, and the adapter it is given must outlive it; it is
                // a pointer to the test's handler, and leaked so that the
                // reader can be returned: one small box for each reader
                let adapter: &'h mut Adapt<'h, H> = Box::leak(Box::new(Adapt(handler)));
                Backend::Rust(Box::new(SmtReader::new(adapter, parser.rust(), version)))
            }
        };
        Reader {
            backend,
            parser: PhantomData,
        }
    }

    /// `SmtReader::read_slice`.
    pub fn read_slice(&mut self, slice: &[u8]) -> Result<(), ReadError<H::Error>> {
        match &mut self.backend {
            Backend::Rust(reader) => reader.read_slice(slice).map_err(ReadError::from),
            Backend::Lean(session) => session.read_slice(slice),
        }
    }

    /// `SmtReader::read_eof`.
    pub fn read_eof(&mut self) -> Result<Located<P::Result>, ReadError<H::Error>> {
        match &mut self.backend {
            Backend::Rust(reader) => reader
                .read_eof()
                .map(|located| Located {
                    location: located.location().into(),
                    value: P::from_rust(located.into_value()),
                })
                .map_err(ReadError::from),
            Backend::Lean(session) => {
                let (result, location) = session.read_eof()?;
                let value = P::from_lean(&result, session.values());
                Ok(Located { value, location })
            }
        }
    }

    /// `SmtReader::read_all`.
    pub fn read_all<R: BufRead>(&mut self, reader: R) -> Result<P::Result, ReadError<H::Error>> {
        match &mut self.backend {
            Backend::Rust(rust) => rust
                .read_all(reader)
                .map(P::from_rust)
                .map_err(ReadError::from),
            Backend::Lean(session) => {
                let result = session.read_all(reader)?;
                Ok(P::from_lean(&result, session.values()))
            }
        }
    }

    /// `SmtReader::read_file`.
    pub fn read_file(&mut self, path: &Path) -> Result<P::Result, ReadError<H::Error>> {
        match &mut self.backend {
            Backend::Rust(rust) => rust
                .read_file(path)
                .map(P::from_rust)
                .map_err(ReadError::from),
            Backend::Lean(session) => {
                let result = session.read_file(path)?;
                Ok(P::from_lean(&result, session.values()))
            }
        }
    }

    /// `SmtReader::discarded_from`.
    pub fn discarded_from(&mut self) -> Option<Location> {
        match &mut self.backend {
            Backend::Rust(reader) => reader.discarded_from().map(Location::from),
            Backend::Lean(session) => session.discarded_from(),
        }
    }

    /// `SmtReader::version`.
    pub fn version(&mut self) -> SmtVersion {
        match &mut self.backend {
            Backend::Rust(reader) => reader.version(),
            Backend::Lean(session) => session.version(),
        }
    }
}

/// `read_smt`: reads a script from the buffered reader under the default
/// posture and version.
pub fn read_smt<H: CommandHandler, R: BufRead>(
    handler: &mut H,
    reader: R,
) -> Result<(), ReadError<H::Error>> {
    match lean_driver() {
        Some(path) => lean::read_smt(path, handler, reader),
        None => {
            blazing_smtlib::reader::read_smt(&mut Adapt(handler), reader).map_err(ReadError::from)
        }
    }
}

/// `read_smt_file`: reads a script from the file under the default posture
/// and version.
pub fn read_smt_file<H: CommandHandler>(
    handler: &mut H,
    path: &Path,
) -> Result<(), ReadError<H::Error>> {
    match lean_driver() {
        Some(driver) => lean::read_smt_file(driver, handler, path),
        None => blazing_smtlib::reader::read_smt_file(&mut Adapt(handler), path)
            .map_err(ReadError::from),
    }
}

// --- The parsers of the categories, driven alone ---

/// A parser of a category, driven alone over the tokens of an input.
pub trait Category<H: Handler> {
    /// What the parser finishes with.
    type Result;
    /// The Rust library's parser.
    type Rust<'h>: SmtParse<Adapt<'h, H>> + Default
    where
        H: 'h;

    fn from_rust<'h>(result: <Self::Rust<'h> as SmtParse<Adapt<'h, H>>>::Result) -> Self::Result
    where
        H: 'h;
    /// The parser as the driver's `drive` request names it.
    fn lean_name() -> String;
    /// The result from the fields of the driver's `result` line.
    fn read_lean(fields: &mut lean::Fields<'_>, values: &mut lean::Values<H>) -> Self::Result;
}

macro_rules! single_token_category {
    ($marker:ident, $rust:ident, $result:ty, $name:literal, |$fields:ident| $read:expr) => {
        #[doc = concat!("`", stringify!($rust), "`.")]
        #[derive(Default)]
        pub struct $marker;

        impl<H: Handler> Category<H> for $marker {
            type Result = $result;
            type Rust<'h>
                = $rust
            where
                H: 'h;

            fn from_rust<'h>(result: $result) -> $result
            where
                H: 'h,
            {
                result
            }
            fn lean_name() -> String {
                $name.into()
            }
            fn read_lean($fields: &mut lean::Fields<'_>, _values: &mut lean::Values<H>) -> $result {
                $read
            }
        }
    };
}

single_token_category!(
    SymbolParser,
    SmtSymbolParser,
    SmtSymbolBuf,
    "symbol",
    |fields| fields.symbol()
);
single_token_category!(
    KeywordParser,
    SmtKeywordParser,
    SmtKeywordBuf,
    "keyword",
    |fields| fields.keyword()
);
single_token_category!(
    StringParser,
    SmtStringParser,
    SmtStringContentBuf,
    "string",
    |fields| fields.string()
);
single_token_category!(
    OpenParenParser,
    SmtOpenParenParser,
    (),
    "open-paren",
    |fields| fields.unit()
);
single_token_category!(
    CloseParenParser,
    SmtCloseParenParser,
    (),
    "close-paren",
    |fields| fields.unit()
);
single_token_category!(
    IdentParser,
    SmtIdentParser,
    SmtIdentBuf,
    "ident",
    |fields| fields.ident()
);

/// `SmtQualifiedIdentParser`.
#[derive(Default)]
pub struct QualifiedIdentParser;

impl<H: Handler> Category<H> for QualifiedIdentParser {
    type Result = QualifiedIdent<H::Sort>;
    type Rust<'h>
        = SmtQualifiedIdentParser<Adapt<'h, H>>
    where
        H: 'h;

    fn from_rust<'h>(
        result: blazing_smtlib::SmtQualifiedIdentBuf<Adapt<'h, H>>,
    ) -> QualifiedIdent<H::Sort>
    where
        H: 'h,
    {
        QualifiedIdent {
            ident: result.ident,
            sort: result.sort,
        }
    }
    fn lean_name() -> String {
        "qualified-ident".into()
    }
    fn read_lean(
        fields: &mut lean::Fields<'_>,
        values: &mut lean::Values<H>,
    ) -> QualifiedIdent<H::Sort> {
        values.qualified_ident(fields)
    }
}

/// `SmtClosedAttributeParser`.
#[derive(Default)]
pub struct ClosedAttributeParser;

impl<H: Handler> Category<H> for ClosedAttributeParser {
    type Result = H::Attribute;
    type Rust<'h>
        = SmtClosedAttributeParser<Adapt<'h, H>>
    where
        H: 'h;

    fn from_rust<'h>(result: H::Attribute) -> H::Attribute
    where
        H: 'h,
    {
        result
    }
    fn lean_name() -> String {
        "closed-attribute".into()
    }
    fn read_lean(fields: &mut lean::Fields<'_>, values: &mut lean::Values<H>) -> H::Attribute {
        values.take_attribute(fields.id())
    }
}

/// `SmtClosedMultipleAttributeParser`.
#[derive(Default)]
pub struct ClosedMultipleAttributeParser;

impl<H: Handler> Category<H> for ClosedMultipleAttributeParser {
    type Result = Vec<H::Attribute>;
    type Rust<'h>
        = SmtClosedMultipleAttributeParser<Adapt<'h, H>>
    where
        H: 'h;

    fn from_rust<'h>(result: Vec<H::Attribute>) -> Vec<H::Attribute>
    where
        H: 'h,
    {
        result
    }
    fn lean_name() -> String {
        "closed-multiple-attribute".into()
    }
    fn read_lean(fields: &mut lean::Fields<'_>, values: &mut lean::Values<H>) -> Vec<H::Attribute> {
        let count = fields.count();
        (0..count)
            .map(|_| values.take_attribute(fields.id()))
            .collect()
    }
}

impl<H: Handler> Category<H> for SortParser {
    type Result = H::Sort;
    type Rust<'h>
        = SmtSortParser<Adapt<'h, H>>
    where
        H: 'h;

    fn from_rust<'h>(result: H::Sort) -> H::Sort
    where
        H: 'h,
    {
        result
    }
    fn lean_name() -> String {
        "sort".into()
    }
    fn read_lean(fields: &mut lean::Fields<'_>, values: &mut lean::Values<H>) -> H::Sort {
        values.take_sort(fields.id())
    }
}

impl<H: Handler> Category<H> for SExprParser {
    type Result = H::SExpr;
    type Rust<'h>
        = SmtSExprParser<Adapt<'h, H>>
    where
        H: 'h;

    fn from_rust<'h>(result: H::SExpr) -> H::SExpr
    where
        H: 'h,
    {
        result
    }
    fn lean_name() -> String {
        "s-expr".into()
    }
    fn read_lean(fields: &mut lean::Fields<'_>, values: &mut lean::Values<H>) -> H::SExpr {
        values.take_s_expr(fields.id())
    }
}

impl<H: Handler> Category<H> for TermParser {
    type Result = H::Term;
    type Rust<'h>
        = SmtTermParser<Adapt<'h, H>>
    where
        H: 'h;

    fn from_rust<'h>(result: H::Term) -> H::Term
    where
        H: 'h,
    {
        result
    }
    fn lean_name() -> String {
        "term".into()
    }
    fn read_lean(fields: &mut lean::Fields<'_>, values: &mut lean::Values<H>) -> H::Term {
        values.take_term(fields.id())
    }
}

/// `SmtPairParser`: the first parser's value, then the second's.
pub struct PairParser<P1, P2>(PhantomData<(P1, P2)>);

impl<H: Handler, P1: Category<H>, P2: Category<H>> Category<H> for PairParser<P1, P2> {
    type Result = (P1::Result, P2::Result);
    type Rust<'h>
        = SmtPairParser<Adapt<'h, H>, P1::Rust<'h>, P2::Rust<'h>>
    where
        H: 'h;

    fn from_rust<'h>(
        (first, second): (
            <P1::Rust<'h> as SmtParse<Adapt<'h, H>>>::Result,
            <P2::Rust<'h> as SmtParse<Adapt<'h, H>>>::Result,
        ),
    ) -> Self::Result
    where
        H: 'h,
    {
        (P1::from_rust(first), P2::from_rust(second))
    }
    fn lean_name() -> String {
        format!("pair({},{})", P1::lean_name(), P2::lean_name())
    }
    fn read_lean(fields: &mut lean::Fields<'_>, values: &mut lean::Values<H>) -> Self::Result {
        let first = P1::read_lean(fields, values);
        (first, P2::read_lean(fields, values))
    }
}

/// The name of the pair parsers nested to the right over the parsers named.
fn nested_pair_name(names: &[String]) -> String {
    let (last, rest) = names
        .split_last()
        .expect("nested pairs are over at least one parser");
    rest.iter().rev().fold(last.clone(), |nested, name| {
        format!("pair({name},{nested})")
    })
}

/// Defines the category of a tuple parser. The Lean port has no tuple
/// parsers: it parses a tuple by the pair parsers nested to the right, whose
/// results the driver writes in order.
macro_rules! tuple_category {
    ($marker:ident, $rust:ident: $($parser:ident $value:ident),+) => {
        #[doc = concat!("`", stringify!($rust), "`: the values of the parsers in turn.")]
        pub struct $marker<$($parser),+>(PhantomData<($($parser,)+)>);

        impl<H: Handler, $($parser: Category<H>),+> Category<H> for $marker<$($parser),+> {
            type Result = ($($parser::Result,)+);
            type Rust<'h>
                = $rust<Adapt<'h, H>, $($parser::Rust<'h>),+>
            where
                H: 'h;

            fn from_rust<'h>(
                ($($value,)+): <Self::Rust<'h> as SmtParse<Adapt<'h, H>>>::Result,
            ) -> Self::Result
            where
                H: 'h,
            {
                ($($parser::from_rust($value),)+)
            }
            fn lean_name() -> String {
                nested_pair_name(&[$($parser::lean_name()),+])
            }
            fn read_lean(fields: &mut lean::Fields<'_>, values: &mut lean::Values<H>) -> Self::Result {
                // the elements of a tuple expression are evaluated in order
                ($($parser::read_lean(fields, values),)+)
            }
        }
    };
}

tuple_category!(Tuple3Parser, SmtTuple3Parser: P1 p1, P2 p2, P3 p3);
tuple_category!(Tuple4Parser, SmtTuple4Parser: P1 p1, P2 p2, P3 p3, P4 p4);
tuple_category!(Tuple5Parser, SmtTuple5Parser: P1 p1, P2 p2, P3 p3, P4 p4, P5 p5);
tuple_category!(Tuple6Parser, SmtTuple6Parser: P1 p1, P2 p2, P3 p3, P4 p4, P5 p5, P6 p6);
tuple_category!(Tuple7Parser, SmtTuple7Parser: P1 p1, P2 p2, P3 p3, P4 p4, P5 p5, P6 p6, P7 p7);
tuple_category!(
    Tuple8Parser,
    SmtTuple8Parser: P1 p1, P2 p2, P3 p3, P4 p4, P5 p5, P6 p6, P7 p7, P8 p8
);

macro_rules! wrapping_category {
    ($marker:ident, $rust:ident, $name:literal, single) => {
        wrapping_category!(
            @define $marker, $rust, $name, P::Result, result, P::from_rust(result),
            |fields, values| P::read_lean(fields, values)
        );
    };
    ($marker:ident, $rust:ident, $name:literal, multiple) => {
        wrapping_category!(
            @define $marker, $rust, $name, Vec<P::Result>, results,
            results.into_iter().map(P::from_rust).collect(),
            |fields, values| {
                let count = fields.count();
                (0..count).map(|_| P::read_lean(fields, values)).collect()
            }
        );
    };
    (
        @define $marker:ident, $rust:ident, $name:literal, $result:ty, $bound:ident,
        $convert:expr, |$fields:ident, $values:ident| $read:expr
    ) => {
        #[doc = concat!("`", stringify!($rust), "` over the parser `P`.")]
        pub struct $marker<P>(PhantomData<P>);

        impl<H: Handler, P: Category<H>> Category<H> for $marker<P> {
            type Result = $result;
            type Rust<'h>
                = $rust<Adapt<'h, H>, P::Rust<'h>>
            where
                H: 'h;

            fn from_rust<'h>(
                $bound: <Self::Rust<'h> as SmtParse<Adapt<'h, H>>>::Result,
            ) -> Self::Result
            where
                H: 'h,
            {
                $convert
            }
            fn lean_name() -> String {
                format!("{}({})", $name, P::lean_name())
            }
            fn read_lean(
                $fields: &mut lean::Fields<'_>,
                $values: &mut lean::Values<H>,
            ) -> Self::Result {
                $read
            }
        }
    };
}

wrapping_category!(ClosedParser, SmtClosedParser, "closed", single);
wrapping_category!(ParenParser, SmtParenParser, "paren", single);
wrapping_category!(
    ClosedMultipleParser,
    SmtClosedMultipleParser,
    "closed-multiple",
    multiple
);
wrapping_category!(
    ParenMultipleParser,
    SmtParenMultipleParser,
    "paren-multiple",
    multiple
);

/// A parse that failed with a syntax error, by its kind and span.
pub type ParseFailure = (SmtSyntaxErrorKind, Span);

/// The token consumer that drives a category parser of the Rust library: it
/// collects a wanted number of consecutive results, then counts the tokens
/// left over after the last one.
///
/// The parser instance is reused for every result in turn, so driving with a
/// wanted count above one exercises the self-reset contract.
struct Drive<'d, 'h, H: Handler, P: SmtParse<Adapt<'h, H>>> {
    handler: &'d mut Adapt<'h, H>,
    parse_state: SmtParseState<Adapt<'h, H>>,
    parser: P,
    remaining: usize,
    results: Vec<P::Result>,
    unconsumed: usize,
}

impl<'h, H: Handler, P: SmtParse<Adapt<'h, H>>> SmtConsume for Drive<'_, 'h, H, P> {
    type Result = ();
    type Error = SmtParseError<H::Error>;
    const IS_CONCRETE: bool = false;
}

impl<'a, 'h, H: Handler, P: SmtParse<Adapt<'h, H>>> SmtConsumeFrom<SmtBatchCursor<'a>>
    for Drive<'_, 'h, H, P>
{
    fn consume(&mut self, cursor: &mut SmtBatchCursor<'a>) -> Result<ControlFlow<()>, Self::Error> {
        while !cursor.is_empty() {
            if self.remaining == 0 {
                // count the tokens left after the wanted results, and break at
                // the end of the input, as every consumer must
                while let Some(token) = cursor.next() {
                    if token.category() == SmtTokenCategory::EndOfFile {
                        return Ok(ControlFlow::Break(()));
                    }
                    self.unconsumed += 1;
                }
                return Ok(ControlFlow::Continue(()));
            }
            if let ControlFlow::Break(result) =
                self.parser
                    .parse(self.handler, &mut self.parse_state, cursor)?
            {
                self.results.push(result);
                self.remaining -= 1;
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Lexes the input in 2.7 and drives a fresh parser `P` over the handler
/// through `count` consecutive parses.
///
/// Returns the results and the number of tokens left unconsumed (not
/// counting the end-of-file token); a syntax error is returned as its kind
/// and span. Panics if the input does not lex, if the handler fails, or if
/// the parser did not finish `count` times before the end of the input.
pub fn drive<H: Handler, P: Category<H>>(
    handler: &mut H,
    input: &[u8],
    count: usize,
) -> Result<(Vec<P::Result>, usize), ParseFailure> {
    let text = String::from_utf8_lossy(input).into_owned();
    let (results, unconsumed) = match lean_driver() {
        Some(path) => lean::drive::<H, P>(path, handler, input, count)?,
        None => {
            let mut adapter = Adapt(handler);
            let mut drive = Drive {
                handler: &mut adapter,
                parse_state: SmtParseState::new(),
                parser: P::Rust::default(),
                remaining: count,
                results: Vec::new(),
                unconsumed: 0,
            };
            let mut lexer = SmtLexer::new(&mut drive, SmtVersion::V2_7);
            match lexer
                .lex_all(input)
                .map_err(|err| (err.span(), err.into_cause()))
            {
                Ok(_) => {}
                Err((span, SmtLexErrorCause::Consumer(err))) => match err.into_cause() {
                    SmtParseErrorCause::Syntax(kind) => return Err((kind, span.into())),
                    SmtParseErrorCause::Version(kind) => {
                        panic!("a category parser cannot fail on the version, got {kind:?}")
                    }
                    SmtParseErrorCause::Handler(_) => {
                        panic!("the handler must not fail on {text:?}")
                    }
                },
                Err((_, SmtLexErrorCause::Lexical(kind))) => {
                    panic!("test input {text:?} must lex, got {kind:?}")
                }
            }
            drop(lexer);
            let results = drive.results.into_iter().map(P::from_rust).collect();
            (results, drive.unconsumed)
        }
    };
    assert!(
        results.len() == count,
        "parser finished {} of {count} times before the end of input {text:?}",
        results.len(),
    );
    Ok((results, unconsumed))
}

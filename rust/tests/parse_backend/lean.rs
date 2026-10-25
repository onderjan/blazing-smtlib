//! The Lean backend: the Lean driver runs the Lean parser and asks for every
//! handler call, which this side answers with the test's handler. The
//! protocol is described in `lean/driver-protocol.md`, section "The parser".

use std::cell::{Cell, RefCell};
use std::ffi::{OsStr, OsString};
use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use blazing_smtlib::{
    SmtVersion,
    grammar::{
        SmtIdentBuf, SmtIndexBuf, SmtIndicesBuf, SmtPatternApplicationBuf, SmtPatternBuf,
        SmtQuantifierKind, SmtSimplePatternBuf, SmtSimplePatternsBuf, SmtSpecialConstantBuf,
    },
    lexer::{SmtLexicalErrorKind, SmtLexicalExpected},
    lexicon::{
        SmtBinDigitsBuf, SmtDecimalBuf, SmtHexDigitsBuf, SmtKeywordBuf, SmtNumeralBuf,
        SmtStringContentBuf, SmtSymbolBuf,
    },
    parser::{
        SmtCommandOutcome, SmtMissingItem, SmtNonEmptyList, SmtSyntaxErrorKind, SmtSyntaxExpected,
        SmtVersionErrorKind,
    },
    token::{SmtGeneralReserved, SmtReserved, SmtTokenCategory},
};

use super::nodes::{
    Application, AttributeValue, CommandHandler, Constructors, Handler, NonstandardPayload,
    QualifiedIdent, SExpr, Signature, Sort, Term,
};
use super::{Category, Location, ParseFailure, ReadError, ReadErrorCause, Span, version_name};

// --- The driver process ---

/// A running driver. One serves all the requests of a test thread.
struct Driver {
    child: Child,
    requests: Option<ChildStdin>,
    responses: BufReader<ChildStdout>,
    /// Whether a request is being answered. A request that a panic left
    /// unfinished leaves the driver waiting in the middle of it, so such a
    /// driver is replaced.
    busy: bool,
}

impl Drop for Driver {
    fn drop(&mut self) {
        if self.busy {
            // it waits for an answer that never comes
            let _ = self.child.kill();
        }
        // the driver exits when its input ends
        self.requests = None;
        let _ = self.child.wait();
    }
}

thread_local! {
    static DRIVER: RefCell<Option<Driver>> = const { RefCell::new(None) };
    /// The number of the reader the driver holds, and of the next reader.
    static CURRENT_READER: Cell<u64> = const { Cell::new(0) };
    static NEXT_READER: Cell<u64> = const { Cell::new(1) };
}

fn start_driver(path: &OsStr) -> Driver {
    let mut child = Command::new(path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap_or_else(|err| panic!("cannot start the Lean driver {path:?}: {err}"));
    let requests = child.stdin.take().expect("the driver's input is piped");
    let responses = BufReader::new(child.stdout.take().expect("the driver's output is piped"));
    Driver {
        child,
        requests: Some(requests),
        responses,
        busy: false,
    }
}

impl Driver {
    fn send(&mut self, line: &str) {
        let requests = self
            .requests
            .as_mut()
            .expect("a running driver has its input open");
        requests
            .write_all(line.as_bytes())
            .and_then(|()| requests.write_all(b"\n"))
            .and_then(|()| requests.flush())
            .unwrap_or_else(|err| panic!("cannot send {line:?} to the Lean driver: {err}"));
    }

    fn receive(&mut self, request: &str) -> String {
        let mut line = String::new();
        let read = self
            .responses
            .read_line(&mut line)
            .unwrap_or_else(|err| panic!("cannot read the Lean driver's response: {err}"));
        assert!(
            read > 0,
            "the Lean driver ended in the middle of its response to {request:?}"
        );
        line.trim_end_matches('\n').to_string()
    }
}

/// Sends the request and answers the calls the driver makes while it
/// responds: `calls` gives the answer to a call, by its method and the
/// fields after it. Returns the other lines of the response, up to the
/// first one that is not a `result` line, which is the last. A `fail` line
/// is a refusal of the request, on which this panics.
fn converse(
    path: &OsStr,
    request: &str,
    calls: &mut dyn FnMut(&str, &mut Fields<'_>) -> String,
) -> Vec<String> {
    let mut lines = Vec::new();
    DRIVER.with(|slot| {
        let mut slot = slot.borrow_mut();
        if slot.as_ref().is_some_and(|driver| driver.busy) {
            // a panic left the last request unfinished, and the reader with it
            *slot = None;
            CURRENT_READER.with(|current| current.set(0));
        }
        let driver = slot.get_or_insert_with(|| start_driver(path));
        driver.busy = true;
        driver.send(request);
        loop {
            let line = driver.receive(request);
            if let Some(call) = line.strip_prefix("call ") {
                let mut fields = Fields::new(call);
                let method = fields.next();
                let answer = calls(method, &mut fields);
                fields.end();
                driver.send(&answer);
                continue;
            }
            if line.starts_with("fail") {
                panic!("the Lean driver refused {request:?}: {line:?}");
            }
            let last = !line.starts_with("result ");
            lines.push(line);
            if last {
                break;
            }
        }
        driver.busy = false;
    });
    lines
}

// --- Fields ---

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn unhex(digits: &str, line: &str) -> Vec<u8> {
    assert!(
        digits.len().is_multiple_of(2),
        "the Lean driver sent an odd number of hexadecimal digits: {line:?}"
    );
    (0..digits.len())
        .step_by(2)
        .map(|at| {
            digits
                .get(at..at + 2)
                .and_then(|pair| u8::from_str_radix(pair, 16).ok())
                .unwrap_or_else(|| panic!("the Lean driver sent bad hexadecimal digits: {line:?}"))
        })
        .collect()
}

/// The fields of a line, read in order.
pub struct Fields<'l> {
    fields: std::str::Split<'l, char>,
    line: &'l str,
}

impl<'l> Fields<'l> {
    fn new(line: &'l str) -> Self {
        Fields {
            fields: line.split(' '),
            line,
        }
    }

    fn next(&mut self) -> &'l str {
        self.fields
            .next()
            .unwrap_or_else(|| panic!("the Lean driver sent too few fields: {:?}", self.line))
    }

    fn end(&mut self) {
        assert!(
            self.fields.next().is_none(),
            "the Lean driver sent too many fields: {:?}",
            self.line
        );
    }

    fn bad(&self, what: &str) -> ! {
        panic!("the Lean driver sent a bad {what}: {:?}", self.line)
    }

    fn number(&mut self, what: &str) -> usize {
        let field = self.next();
        field.parse().unwrap_or_else(|_| self.bad(what))
    }

    pub fn count(&mut self) -> usize {
        self.number("count")
    }

    pub fn id(&mut self) -> usize {
        self.number("value number")
    }

    /// The field `-` of a result that carries nothing.
    pub fn unit(&mut self) {
        if self.next() != "-" {
            self.bad("empty result");
        }
    }

    fn opt_id(&mut self) -> Option<usize> {
        match self.next() {
            "-" => None,
            field => Some(field.parse().unwrap_or_else(|_| self.bad("value number"))),
        }
    }

    fn prefixed(&mut self, prefix: char, what: &str) -> Vec<u8> {
        let field = self.next();
        match field.strip_prefix(prefix) {
            Some(digits) => unhex(digits, self.line),
            None => self.bad(what),
        }
    }

    fn bytes(&mut self) -> Vec<u8> {
        self.prefixed('x', "bytes field")
    }

    pub fn keyword(&mut self) -> SmtKeywordBuf {
        SmtKeywordBuf::new(self.bytes()).unwrap_or_else(|_| self.bad("keyword"))
    }

    fn numeral(&mut self) -> SmtNumeralBuf {
        SmtNumeralBuf::new(self.bytes()).unwrap_or_else(|_| self.bad("numeral"))
    }

    pub fn string(&mut self) -> SmtStringContentBuf {
        SmtStringContentBuf::new(self.bytes()).unwrap_or_else(|_| self.bad("string"))
    }

    fn symbol_of(&self, field: &str) -> Option<SmtSymbolBuf> {
        let symbol = match field.split_at_checked(1) {
            Some(("u", digits)) => SmtSymbolBuf::new_unquoted(unhex(digits, self.line)),
            Some(("q", digits)) => SmtSymbolBuf::new_quoted(unhex(digits, self.line)),
            _ => return None,
        };
        Some(symbol.unwrap_or_else(|_| self.bad("symbol")))
    }

    pub fn symbol(&mut self) -> SmtSymbolBuf {
        let field = self.next();
        self.symbol_of(field).unwrap_or_else(|| self.bad("symbol"))
    }

    fn symbols(&mut self) -> Vec<SmtSymbolBuf> {
        let count = self.count();
        (0..count).map(|_| self.symbol()).collect()
    }

    fn constant(&mut self) -> SmtSpecialConstantBuf {
        let field = self.next();
        let Some((kind, digits)) = field.split_at_checked(1) else {
            self.bad("constant")
        };
        let bytes = unhex(digits, self.line);
        let constant = match kind {
            "N" => SmtNumeralBuf::new(bytes).map(SmtSpecialConstantBuf::Numeral),
            "D" => SmtDecimalBuf::new(bytes).map(SmtSpecialConstantBuf::Decimal),
            "X" => SmtHexDigitsBuf::new(bytes).map(SmtSpecialConstantBuf::Hexadecimal),
            "B" => SmtBinDigitsBuf::new(bytes).map(SmtSpecialConstantBuf::Binary),
            "S" => SmtStringContentBuf::new(bytes).map(SmtSpecialConstantBuf::String),
            _ => self.bad("constant"),
        };
        constant.unwrap_or_else(|_| self.bad("constant"))
    }

    pub fn ident(&mut self) -> SmtIdentBuf {
        let name = self.symbol();
        let count = self.count();
        let mut indices = SmtIndicesBuf::new();
        for _ in 0..count {
            let field = self.next();
            let index = match field.strip_prefix('n') {
                Some(digits) => SmtIndexBuf::Numeral(
                    SmtNumeralBuf::new(unhex(digits, self.line))
                        .unwrap_or_else(|_| self.bad("index")),
                ),
                None => {
                    SmtIndexBuf::Symbol(self.symbol_of(field).unwrap_or_else(|| self.bad("index")))
                }
            };
            indices.push(index.view());
        }
        SmtIdentBuf { name, indices }
    }

    fn simple_pattern(&mut self) -> SmtSimplePatternBuf {
        match self.next() {
            "_" => SmtSimplePatternBuf::Wildcard,
            field => SmtSimplePatternBuf::Symbol(
                self.symbol_of(field).unwrap_or_else(|| self.bad("pattern")),
            ),
        }
    }

    fn pattern(&mut self) -> SmtPatternBuf {
        match self.next() {
            "p" => SmtPatternBuf::Simple(self.simple_pattern()),
            "c" => {
                let constructor = self.symbol();
                let count = self.count();
                let mut args = SmtSimplePatternsBuf::new();
                for _ in 0..count {
                    args.push(self.simple_pattern().view());
                }
                let application = SmtPatternApplicationBuf::new(constructor, args)
                    .unwrap_or_else(|_| self.bad("pattern"));
                SmtPatternBuf::Application(application)
            }
            _ => self.bad("pattern"),
        }
    }

    fn quantifier(&mut self) -> SmtQuantifierKind {
        match self.next() {
            "forall" => SmtQuantifierKind::Forall,
            "exists" => SmtQuantifierKind::Exists,
            _ => self.bad("quantifier"),
        }
    }

    fn version(&mut self) -> SmtVersion {
        let field = self.next();
        SmtVersion::from_decimal(field.as_bytes()).unwrap_or_else(|| self.bad("version"))
    }

    fn location(&mut self) -> Location {
        let field = self.next();
        let numbers: Vec<u64> = field
            .split(':')
            .map(|number| number.parse().unwrap_or_else(|_| self.bad("location")))
            .collect();
        match numbers[..] {
            [offset, line, column] => Location::new(offset, line, column),
            _ => self.bad("location"),
        }
    }

    fn reserved(&mut self) -> SmtReserved {
        let word = self.next();
        // the word is reserved in the version of the parse, which the call
        // does not say: it is looked up in the latest version it is one in
        [
            SmtVersion::V2_7,
            SmtVersion::V2_6,
            SmtVersion::V2_5,
            SmtVersion::V2_0,
        ]
        .into_iter()
        .find_map(|version| SmtReserved::from_bytes(word.as_bytes(), version))
        .unwrap_or_else(|| self.bad("reserved word"))
    }
}

// --- Values ---

/// The values a handler made in a conversation with the driver, which the
/// driver names by their numbers, and the errors it failed with.
pub struct Values<H: Handler> {
    sorts: Vec<Option<H::Sort>>,
    terms: Vec<Option<H::Term>>,
    s_exprs: Vec<Option<H::SExpr>>,
    attributes: Vec<Option<H::Attribute>>,
    scopes: Vec<Option<H::Scope>>,
    errors: Vec<Option<H::Error>>,
}

fn put<T>(values: &mut Vec<Option<T>>, value: T) -> usize {
    values.push(Some(value));
    values.len() - 1
}

fn take<T>(values: &mut [Option<T>], id: usize, what: &str) -> T {
    values
        .get_mut(id)
        .and_then(Option::take)
        .unwrap_or_else(|| {
            panic!("the Lean driver handed over {what} {id}, which it does not hold")
        })
}

fn lend<'v, T>(values: &'v [Option<T>], id: usize, what: &str) -> &'v T {
    values
        .get(id)
        .and_then(Option::as_ref)
        .unwrap_or_else(|| panic!("the Lean driver lent {what} {id}, which it does not hold"))
}

impl<H: Handler> Values<H> {
    pub fn new() -> Self {
        Values {
            sorts: Vec::new(),
            terms: Vec::new(),
            s_exprs: Vec::new(),
            attributes: Vec::new(),
            scopes: Vec::new(),
            errors: Vec::new(),
        }
    }

    pub fn take_sort(&mut self, id: usize) -> H::Sort {
        take(&mut self.sorts, id, "sort")
    }

    pub fn take_term(&mut self, id: usize) -> H::Term {
        take(&mut self.terms, id, "term")
    }

    pub fn take_s_expr(&mut self, id: usize) -> H::SExpr {
        take(&mut self.s_exprs, id, "s-expression")
    }

    pub fn take_attribute(&mut self, id: usize) -> H::Attribute {
        take(&mut self.attributes, id, "attribute")
    }

    fn take_scope(&mut self, id: usize) -> H::Scope {
        take(&mut self.scopes, id, "scope")
    }

    fn take_error(&mut self, id: usize) -> H::Error {
        take(&mut self.errors, id, "error")
    }

    fn sorts(&mut self, fields: &mut Fields<'_>) -> Vec<H::Sort> {
        let count = fields.count();
        (0..count).map(|_| self.take_sort(fields.id())).collect()
    }

    fn terms(&mut self, fields: &mut Fields<'_>) -> Vec<H::Term> {
        let count = fields.count();
        (0..count).map(|_| self.take_term(fields.id())).collect()
    }

    fn s_exprs(&mut self, fields: &mut Fields<'_>) -> Vec<H::SExpr> {
        let count = fields.count();
        (0..count).map(|_| self.take_s_expr(fields.id())).collect()
    }

    fn sorted_vars(&mut self, fields: &mut Fields<'_>) -> Vec<(SmtSymbolBuf, H::Sort)> {
        let count = fields.count();
        (0..count)
            .map(|_| (fields.symbol(), self.take_sort(fields.id())))
            .collect()
    }

    fn constructors(&mut self, fields: &mut Fields<'_>) -> Constructors<H::Sort> {
        let count = fields.count();
        (0..count)
            .map(|_| (fields.symbol(), self.sorted_vars(fields)))
            .collect()
    }

    fn signature(&self, fields: &mut Fields<'_>) -> Signature<'_, H::Sort> {
        let name = fields.symbol();
        let count = fields.count();
        let params = (0..count)
            .map(|_| (fields.symbol(), lend(&self.sorts, fields.id(), "sort")))
            .collect();
        let result_sort = lend(&self.sorts, fields.id(), "sort");
        Signature {
            name,
            params,
            result_sort,
        }
    }

    pub fn qualified_ident(&mut self, fields: &mut Fields<'_>) -> QualifiedIdent<H::Sort> {
        let ident = fields.ident();
        let sort = fields.opt_id().map(|id| self.take_sort(id));
        QualifiedIdent { ident, sort }
    }

    /// The answer to a call that makes a value, which `put` keeps.
    fn made<T>(
        &mut self,
        result: Result<T, H::Error>,
        put_value: impl FnOnce(&mut Self, T) -> usize,
    ) -> String {
        match result {
            Ok(value) => format!("ok {}", put_value(self, value)),
            Err(err) => format!("err {}", put(&mut self.errors, err)),
        }
    }

    /// The answer to a call that makes no value.
    fn done(&mut self, result: Result<(), H::Error>) -> String {
        match result {
            Ok(()) => "ok".into(),
            Err(err) => format!("err {}", put(&mut self.errors, err)),
        }
    }
}

impl<H: Handler> Default for Values<H> {
    fn default() -> Self {
        Self::new()
    }
}

/// A value's number from a `<result>` field.
pub fn value_id(field: &str) -> usize {
    field
        .parse()
        .unwrap_or_else(|_| panic!("the Lean driver sent a bad result {field:?}"))
}

/// The outcome of the command parser from its `<result>` fields.
pub fn command_outcome(result: &str) -> SmtCommandOutcome {
    match result.split(' ').collect::<Vec<_>>()[..] {
        ["command"] => SmtCommandOutcome::Command,
        ["exit"] => SmtCommandOutcome::Exit,
        ["end"] => SmtCommandOutcome::EndOfFile,
        ["set-version", version] => SmtCommandOutcome::SetVersion(
            SmtVersion::from_decimal(version.as_bytes())
                .unwrap_or_else(|| panic!("the Lean driver sent a bad command outcome {result:?}")),
        ),
        _ => panic!("the Lean driver sent a bad command outcome {result:?}"),
    }
}

// --- Calls ---

/// Answers a call of the handler of the categories, or returns `None` if the
/// method is none of them.
fn handler_call<H: Handler>(
    handler: &mut H,
    values: &mut Values<H>,
    method: &str,
    fields: &mut Fields<'_>,
) -> Option<String> {
    let answer = match method {
        "set_version" => {
            handler.set_version(fields.version());
            "ok".into()
        }
        "handle_sort" => {
            let ident = fields.ident();
            let applied = values.sorts(fields);
            let result = handler.handle_sort(Sort { ident, applied });
            values.made(result, |values, sort| put(&mut values.sorts, sort))
        }
        "handle_term" => {
            let term = match fields.next() {
                "c" => Term::SpecialConstant(fields.constant()),
                "i" => Term::QualifiedIdent(values.qualified_ident(fields)),
                "a" => {
                    let function = values.qualified_ident(fields);
                    let args = values.terms(fields);
                    Term::Application(Application { function, args })
                }
                _ => fields.bad("term"),
            };
            let result = handler.handle_term(term);
            values.made(result, |values, term| put(&mut values.terms, term))
        }
        "handle_s_expr" => {
            let expr = match fields.next() {
                "c" => SExpr::SpecialConstant(fields.constant()),
                "s" => SExpr::Symbol(fields.symbol()),
                "r" => SExpr::Reserved(fields.reserved()),
                "k" => SExpr::Keyword(fields.keyword()),
                "l" => SExpr::SExprs(values.s_exprs(fields)),
                _ => fields.bad("s-expression"),
            };
            let result = handler.handle_s_expr(expr);
            values.made(result, |values, expr| put(&mut values.s_exprs, expr))
        }
        "handle_attribute" => {
            let name = fields.keyword();
            let value = match fields.next() {
                "-" => None,
                "c" => Some(AttributeValue::SpecialConstant(fields.constant())),
                "s" => Some(AttributeValue::Symbol(fields.symbol())),
                "l" => Some(AttributeValue::SExprs(values.s_exprs(fields))),
                _ => fields.bad("attribute value"),
            };
            let result = handler.handle_attribute(name, value);
            values.made(result, |values, attribute| {
                put(&mut values.attributes, attribute)
            })
        }
        "annotate_term" => {
            let term = values.take_term(fields.id());
            let count = fields.count();
            let attributes = (0..count)
                .map(|_| values.take_attribute(fields.id()))
                .collect();
            let result = handler.annotate_term(term, attributes);
            values.made(result, |values, term| put(&mut values.terms, term))
        }
        "start_let" => {
            let count = fields.count();
            let bindings = (0..count)
                .map(|_| (fields.symbol(), values.take_term(fields.id())))
                .collect();
            let result = handler.start_let(bindings);
            values.made(result, |values, scope| put(&mut values.scopes, scope))
        }
        "end_let" => {
            let scope = values.take_scope(fields.id());
            let body = values.take_term(fields.id());
            let result = handler.end_let(scope, body);
            values.made(result, |values, term| put(&mut values.terms, term))
        }
        "start_quantifier" => {
            let kind = fields.quantifier();
            let vars = values.sorted_vars(fields);
            let result = handler.start_quantifier(kind, vars);
            values.made(result, |values, scope| put(&mut values.scopes, scope))
        }
        "end_quantifier" => {
            let kind = fields.quantifier();
            let scope = values.take_scope(fields.id());
            let body = values.take_term(fields.id());
            let result = handler.end_quantifier(kind, scope, body);
            values.made(result, |values, term| put(&mut values.terms, term))
        }
        "start_lambda" => {
            let vars = values.sorted_vars(fields);
            let result = handler.start_lambda(vars);
            values.made(result, |values, scope| put(&mut values.scopes, scope))
        }
        "end_lambda" => {
            let scope = values.take_scope(fields.id());
            let body = values.take_term(fields.id());
            let result = handler.end_lambda(scope, body);
            values.made(result, |values, term| put(&mut values.terms, term))
        }
        "start_match" => {
            let scrutinee = lend(&values.terms, fields.id(), "term");
            let result = handler.start_match(scrutinee);
            values.done(result)
        }
        "start_match_case" => {
            let scrutinee = fields.id();
            let pattern = fields.pattern();
            let result = handler.start_match_case(lend(&values.terms, scrutinee, "term"), pattern);
            values.made(result, |values, scope| put(&mut values.scopes, scope))
        }
        "end_match_case" => {
            let scope = values.take_scope(fields.id());
            let scrutinee = fields.id();
            let body = values.take_term(fields.id());
            let result =
                handler.end_match_case(scope, lend(&values.terms, scrutinee, "term"), body);
            values.made(result, |values, term| put(&mut values.terms, term))
        }
        "end_match" => {
            let scrutinee = values.take_term(fields.id());
            let count = fields.count();
            let cases = (0..count)
                .map(|_| (fields.pattern(), values.take_term(fields.id())))
                .collect();
            let result = handler.end_match(scrutinee, cases);
            values.made(result, |values, term| put(&mut values.terms, term))
        }
        _ => return None,
    };
    Some(answer)
}

/// Answers a call of the handler of commands, or of the handler of the
/// categories it extends.
fn command_call<H: CommandHandler>(
    handler: &mut H,
    values: &mut Values<H>,
    method: &str,
    fields: &mut Fields<'_>,
) -> Option<String> {
    let result = match method {
        "nonstandard_command" => {
            // the payload's parser is told by the answer
            let answer = match handler.nonstandard_command(fields.symbol()) {
                Ok(NonstandardPayload::Term) => "ok".into(),
                Ok(NonstandardPayload::SwitchVersion(version)) => {
                    format!("ok switch {}", version_name(version))
                }
                Ok(NonstandardPayload::DiscardRest) => "ok discard".into(),
                Err(err) => values.done(Err(err)),
            };
            return Some(answer);
        }
        "nonstandard_term" => {
            let term = values.take_term(fields.id());
            handler.nonstandard_term(term)
        }
        "command_assert" => {
            let term = values.take_term(fields.id());
            handler.command_assert(term)
        }
        "command_check_sat" => handler.command_check_sat(),
        "command_check_sat_assuming" => {
            let terms = values.terms(fields);
            handler.command_check_sat_assuming(terms)
        }
        "command_declare_const" => {
            let name = fields.symbol();
            let sort = values.take_sort(fields.id());
            handler.command_declare_const(name, sort)
        }
        "start_declare_datatype" => {
            let name = fields.symbol();
            let params = fields.symbols();
            handler.start_declare_datatype(name, params)
        }
        "end_declare_datatype" => {
            let constructors = values.constructors(fields);
            handler.end_declare_datatype(constructors)
        }
        "start_declare_datatypes" => {
            let count = fields.count();
            let introductions = (0..count)
                .map(|_| (fields.symbol(), fields.numeral()))
                .collect();
            handler.start_declare_datatypes(introductions)
        }
        "start_datatype_declaration" => {
            let params = fields.symbols();
            handler.start_datatype_declaration(params)
        }
        "end_datatype_declaration" => {
            let constructors = values.constructors(fields);
            handler.end_datatype_declaration(constructors)
        }
        "end_declare_datatypes" => handler.end_declare_datatypes(),
        "command_declare_fun" => {
            let name = fields.symbol();
            let params = values.sorts(fields);
            let result = values.take_sort(fields.id());
            handler.command_declare_fun(name, params, result)
        }
        "command_declare_sort" => {
            let name = fields.symbol();
            let arity = fields.numeral();
            handler.command_declare_sort(name, arity)
        }
        "command_declare_sort_parameter" => {
            let name = fields.symbol();
            handler.command_declare_sort_parameter(name)
        }
        "command_define_const" => {
            let name = fields.symbol();
            let sort = values.take_sort(fields.id());
            let body = values.take_term(fields.id());
            handler.command_define_const(name, sort, body)
        }
        "start_define_fun" => handler.start_define_fun(values.signature(fields)),
        "end_define_fun" => {
            let term = values.take_term(fields.id());
            handler.end_define_fun(term)
        }
        "start_define_fun_rec" => handler.start_define_fun_rec(values.signature(fields)),
        "end_define_fun_rec" => {
            let term = values.take_term(fields.id());
            handler.end_define_fun_rec(term)
        }
        "start_define_funs_rec" => {
            let count = fields.count();
            let signatures = (0..count).map(|_| values.signature(fields)).collect();
            handler.start_define_funs_rec(signatures)
        }
        "start_recursive_body" => handler.start_recursive_body(values.signature(fields)),
        "end_recursive_body" => {
            let term = values.take_term(fields.id());
            handler.end_recursive_body(term)
        }
        "end_define_funs_rec" => handler.end_define_funs_rec(),
        "start_define_sort" => {
            let name = fields.symbol();
            let params = fields.symbols();
            handler.start_define_sort(name, params)
        }
        "end_define_sort" => {
            let sort = values.take_sort(fields.id());
            handler.end_define_sort(sort)
        }
        "command_echo" => handler.command_echo(fields.string()),
        "command_exit" => handler.command_exit(),
        "command_get_assertions" => handler.command_get_assertions(),
        "command_get_assignment" => handler.command_get_assignment(),
        "command_get_info" => handler.command_get_info(fields.keyword()),
        "command_get_model" => handler.command_get_model(),
        "command_get_option" => handler.command_get_option(fields.keyword()),
        "command_get_proof" => handler.command_get_proof(),
        "command_get_unsat_assumptions" => handler.command_get_unsat_assumptions(),
        "command_get_unsat_core" => handler.command_get_unsat_core(),
        "command_get_value" => {
            let terms = values.terms(fields);
            handler.command_get_value(terms)
        }
        "command_pop" => handler.command_pop(fields.numeral()),
        "command_push" => handler.command_push(fields.numeral()),
        "command_reset" => handler.command_reset(),
        "command_reset_assertions" => handler.command_reset_assertions(),
        "command_set_info" => {
            let attribute = values.take_attribute(fields.id());
            handler.command_set_info(attribute)
        }
        "command_set_logic" => handler.command_set_logic(fields.symbol()),
        "command_set_option" => {
            let attribute = values.take_attribute(fields.id());
            handler.command_set_option(attribute)
        }
        _ => return handler_call(handler, values, method, fields),
    };
    Some(values.done(result))
}

/// Answers a call of the buffered reader, or returns `None` if the method is
/// none of its.
fn buffered_call(
    reader: &mut dyn BufRead,
    method: &str,
    fields: &mut Fields<'_>,
) -> Option<String> {
    let answer = match method {
        "fill" => match reader.fill_buf() {
            Ok(bytes) => format!("bytes {}", hex(bytes)),
            Err(err) => format!("ioerr {}", hex(err.to_string().as_bytes())),
        },
        "consume" => {
            reader.consume(fields.count());
            "ok".into()
        }
        _ => return None,
    };
    Some(answer)
}

fn unknown_call(method: &str) -> ! {
    panic!("the Lean driver made a call that is not understood: {method:?}")
}

// --- Errors ---

const ERROR_KINDS: [SmtLexicalErrorKind; 14] = [
    SmtLexicalErrorKind::UnexpectedCharacter,
    SmtLexicalErrorKind::Expected(SmtLexicalExpected::FractionDigit),
    SmtLexicalErrorKind::Expected(SmtLexicalExpected::HexadecimalDigit),
    SmtLexicalErrorKind::Expected(SmtLexicalExpected::BinaryDigit),
    SmtLexicalErrorKind::Expected(SmtLexicalExpected::Base),
    SmtLexicalErrorKind::UnclosedStringLiteral,
    SmtLexicalErrorKind::ForbiddenCharInString,
    SmtLexicalErrorKind::EmptyKeyword,
    SmtLexicalErrorKind::BackslashInQuotedSymbol,
    SmtLexicalErrorKind::ForbiddenCharInQuotedSymbol,
    SmtLexicalErrorKind::UnclosedQuotedSymbol,
    SmtLexicalErrorKind::NumeralLeadingZero,
    SmtLexicalErrorKind::MissingDelimiter,
    SmtLexicalErrorKind::UnexpectedTrailingToken,
];

const TOKEN_TYPES: [SmtTokenCategory; 13] = [
    SmtTokenCategory::ParenOpen,
    SmtTokenCategory::ParenClose,
    SmtTokenCategory::Numeral,
    SmtTokenCategory::Decimal,
    SmtTokenCategory::Hexadecimal,
    SmtTokenCategory::Binary,
    SmtTokenCategory::String,
    SmtTokenCategory::Keyword,
    SmtTokenCategory::UnquotedSymbol,
    SmtTokenCategory::QuotedSymbol,
    SmtTokenCategory::Whitespace,
    SmtTokenCategory::Comment,
    SmtTokenCategory::EndOfFile,
];

/// The items a syntax error may expect but tokens: the reserved words that
/// the parsers expect, and the categories.
const EXPECTED_ITEMS: [SmtSyntaxExpected; 13] = [
    SmtSyntaxExpected::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore)),
    SmtSyntaxExpected::Reserved(SmtReserved::General(SmtGeneralReserved::As)),
    SmtSyntaxExpected::Reserved(SmtReserved::General(SmtGeneralReserved::Par)),
    SmtSyntaxExpected::Symbol,
    SmtSyntaxExpected::Index,
    SmtSyntaxExpected::Ident,
    SmtSyntaxExpected::Sort,
    SmtSyntaxExpected::Term,
    SmtSyntaxExpected::SExpr,
    SmtSyntaxExpected::Attribute,
    SmtSyntaxExpected::Operator,
    SmtSyntaxExpected::CommandName,
    SmtSyntaxExpected::PropositionalLiteral,
];

const NON_EMPTY_LISTS: [SmtNonEmptyList; 14] = [
    SmtNonEmptyList::IdentIndices,
    SmtNonEmptyList::SortApplication,
    SmtNonEmptyList::TermApplication,
    SmtNonEmptyList::LetBindings,
    SmtNonEmptyList::Annotation,
    SmtNonEmptyList::QuantifierBindings,
    SmtNonEmptyList::LambdaBindings,
    SmtNonEmptyList::FunctionSignatures,
    SmtNonEmptyList::DatatypeIntroductions,
    SmtNonEmptyList::DatatypeParameters,
    SmtNonEmptyList::DatatypeConstructors,
    SmtNonEmptyList::PatternArguments,
    SmtNonEmptyList::MatchCases,
    SmtNonEmptyList::GetValueTerms,
];

const MISSING_ITEMS: [SmtMissingItem; 2] = [SmtMissingItem::FunctionBody, SmtMissingItem::Datatype];

/// Finds the value whose debug spelling is the name.
fn by_name<T: Clone + std::fmt::Debug>(values: &[T], name: &str, line: &str) -> T {
    values
        .iter()
        .find(|value| format!("{value:?}") == name)
        .cloned()
        .unwrap_or_else(|| panic!("the Lean driver sent an unknown name {name:?}: {line:?}"))
}

/// The argument of a spelling `<variant>(<argument>)`, if the spelling is of
/// the variant.
fn argument<'a>(spelling: &'a str, variant: &str) -> Option<&'a str> {
    spelling
        .strip_prefix(variant)?
        .strip_prefix('(')?
        .strip_suffix(')')
}

/// The item of a syntax error, spelled as its debug form.
fn syntax_expected(name: &str, line: &str) -> SmtSyntaxExpected {
    match argument(name, "Token") {
        Some(ty) => SmtSyntaxExpected::Token(by_name(&TOKEN_TYPES, ty, line)),
        None => by_name(&EXPECTED_ITEMS, name, line),
    }
}

/// The kind of a `syntax` error, spelled as its debug form without spaces.
fn syntax_kind(name: &str, line: &str) -> SmtSyntaxErrorKind {
    if let Some(items) = argument(name, "Expected") {
        let expected: Vec<SmtSyntaxExpected> = items
            .strip_prefix('[')
            .and_then(|items| items.strip_suffix(']'))
            .unwrap_or_else(|| panic!("the Lean driver sent an unknown name {name:?}: {line:?}"))
            .split(',')
            .map(|item| syntax_expected(item, line))
            .collect();
        // the kind holds a static list; the few that the tests see are
        // kept for the rest of the run
        SmtSyntaxErrorKind::Expected(Vec::leak(expected))
    } else if let Some(list) = argument(name, "Empty") {
        SmtSyntaxErrorKind::Empty(by_name(&NON_EMPTY_LISTS, list, line))
    } else if let Some(item) = argument(name, "Missing") {
        SmtSyntaxErrorKind::Missing(by_name(&MISSING_ITEMS, item, line))
    } else {
        panic!("the Lean driver sent an unknown name {name:?}: {line:?}")
    }
}

/// The kind of a `version` error, spelled as its debug form.
fn version_kind(name: &str, line: &str) -> SmtVersionErrorKind {
    match argument(name, "TooManyDeclarations") {
        Some(limit) => {
            SmtVersionErrorKind::TooManyDeclarations(limit.parse().unwrap_or_else(|_| {
                panic!("the Lean driver sent an unknown name {name:?}: {line:?}")
            }))
        }
        None => by_name(&[SmtVersionErrorKind::Unsupported], name, line),
    }
}

/// The error of an `error` line, whose fields after `error` are given.
fn read_error<H: Handler>(fields: &mut Fields<'_>, values: &mut Values<H>) -> ReadError<H::Error> {
    let start = fields.location();
    let end = fields.location();
    let line = fields.line;
    let cause = match fields.next() {
        "lexical" => ReadErrorCause::Lexical(by_name(&ERROR_KINDS, fields.next(), line)),
        "syntax" => ReadErrorCause::Syntax(syntax_kind(fields.next(), line)),
        "version" => ReadErrorCause::Version(version_kind(fields.next(), line)),
        "handler" => ReadErrorCause::Handler(values.take_error(fields.id())),
        "io" => {
            let message = unhex(fields.next(), line);
            ReadErrorCause::Io(String::from_utf8_lossy(&message).into_owned())
        }
        _ => fields.bad("error cause"),
    };
    fields.end();
    ReadError::new(cause, Span::new(start, end))
}

// --- Readers ---

/// The ending line of a response, or the error it reports.
fn ending<H: CommandHandler>(
    lines: Vec<String>,
    request: &str,
    values: &mut Values<H>,
) -> Result<String, ReadError<H::Error>> {
    let [line] = &lines[..] else {
        panic!("the Lean driver answered {request:?} with {lines:?}")
    };
    match line.strip_prefix("error ") {
        Some(error) => Err(read_error(&mut Fields::new(error), values)),
        None => Ok(line.clone()),
    }
}

/// Sends a request that reads, answering the calls of the handler and, if
/// there is a buffered reader, of the buffered reader. Returns the ending
/// line of the response, or the error it reports.
fn read_request<H: CommandHandler>(
    path: &OsStr,
    request: &str,
    handler: &mut H,
    values: &mut Values<H>,
    mut reader: Option<&mut dyn BufRead>,
) -> Result<String, ReadError<H::Error>> {
    let lines = converse(path, request, &mut |method, fields| {
        if let Some(reader) = reader.as_deref_mut()
            && let Some(answer) = buffered_call(reader, method, fields)
        {
            return answer;
        }
        command_call(handler, values, method, fields).unwrap_or_else(|| unknown_call(method))
    });
    ending(lines, request, values)
}

/// The result of a `done <result>` line, with its fields joined.
fn done(line: &str, request: &str) -> String {
    match line.strip_prefix("done ") {
        Some(result) => result.to_string(),
        None if line == "none" => {
            panic!("the Lean reader reports that its parser continued on the end of the input")
        }
        None => panic!("the Lean driver answered {request:?} with {line:?}"),
    }
}

/// A reader of the Lean driver, over a test handler.
pub struct Session<'h, H: CommandHandler> {
    path: OsString,
    handler: &'h mut H,
    values: Values<H>,
    /// The number of the reader, which the driver holds while it is the last
    /// one opened on the thread.
    number: u64,
}

impl<'h, H: CommandHandler> Session<'h, H> {
    pub fn open(path: OsString, handler: &'h mut H, parser: &str, version: SmtVersion) -> Self {
        let number = NEXT_READER.with(|next| {
            let number = next.get();
            next.set(number + 1);
            number
        });
        let mut values = Values::new();
        let request = format!("reader {parser} {}", version_name(version));
        match read_request(&path, &request, handler, &mut values, None) {
            Ok(line) if line == "ready" => {}
            Ok(line) => panic!("the Lean driver answered {request:?} with {line:?}"),
            Err(err) => panic!(
                "the Lean driver answered {request:?} with an error at {:?}",
                err.span()
            ),
        }
        CURRENT_READER.with(|current| current.set(number));
        Session {
            path,
            handler,
            values,
            number,
        }
    }

    pub fn values(&mut self) -> &mut Values<H> {
        &mut self.values
    }

    fn request(
        &mut self,
        request: &str,
        reader: Option<&mut dyn BufRead>,
    ) -> Result<String, ReadError<H::Error>> {
        assert_eq!(
            CURRENT_READER.with(Cell::get),
            self.number,
            "another Lean reader was opened on this thread since this one, \
             and the driver holds one reader at a time"
        );
        read_request(&self.path, request, self.handler, &mut self.values, reader)
    }

    /// A request that cannot fail.
    fn query(&mut self, request: &str) -> String {
        self.request(request, None).unwrap_or_else(|err| {
            panic!(
                "the Lean driver answered {request:?} with an error at {:?}",
                err.span()
            )
        })
    }

    pub fn read_slice(&mut self, slice: &[u8]) -> Result<(), ReadError<H::Error>> {
        let request = format!("slice {}", hex(slice));
        let line = self.request(&request, None)?;
        assert_eq!(
            line, "ok",
            "the Lean driver answered {request:?} with {line:?}"
        );
        Ok(())
    }

    /// The result fields of the parser and where it finished.
    pub fn read_eof(&mut self) -> Result<(String, Location), ReadError<H::Error>> {
        let line = self.request("eof", None)?;
        let result = done(&line, "eof");
        let (result, location) = result
            .rsplit_once(' ')
            .unwrap_or_else(|| panic!("the Lean driver answered eof with {line:?}"));
        let location = Fields::new(location).location();
        Ok((result.to_string(), location))
    }

    pub fn read_all<R: BufRead>(&mut self, mut reader: R) -> Result<String, ReadError<H::Error>> {
        let line = self.request("all", Some(&mut reader))?;
        Ok(done(&line, "all"))
    }

    pub fn read_file(&mut self, path: &Path) -> Result<String, ReadError<H::Error>> {
        let request = format!("file {}", hex(path.as_os_str().as_encoded_bytes()));
        let line = self.request(&request, None)?;
        Ok(done(&line, &request))
    }

    pub fn discarded_from(&mut self) -> Option<Location> {
        let line = self.query("discarded");
        match line.strip_prefix("at ") {
            Some("-") => None,
            Some(location) => Some(Fields::new(location).location()),
            None => panic!("the Lean driver answered discarded with {line:?}"),
        }
    }

    pub fn version(&mut self) -> SmtVersion {
        let line = self.query("version");
        match line.strip_prefix("version ") {
            Some(version) => Fields::new(version).version(),
            None => panic!("the Lean driver answered version with {line:?}"),
        }
    }
}

/// Sends a request that reads a whole script with a handler of its own.
fn read_whole<H: CommandHandler>(
    path: OsString,
    handler: &mut H,
    request: &str,
    reader: Option<&mut dyn BufRead>,
) -> Result<(), ReadError<H::Error>> {
    let line = read_request(&path, request, handler, &mut Values::new(), reader)?;
    assert_eq!(
        line, "ok",
        "the Lean driver answered {request:?} with {line:?}"
    );
    Ok(())
}

pub fn read_smt<H: CommandHandler, R: BufRead>(
    path: OsString,
    handler: &mut H,
    mut reader: R,
) -> Result<(), ReadError<H::Error>> {
    read_whole(path, handler, "read-smt", Some(&mut reader))
}

pub fn read_smt_file<H: CommandHandler>(
    driver: OsString,
    handler: &mut H,
    path: &Path,
) -> Result<(), ReadError<H::Error>> {
    let request = format!("read-smt-file {}", hex(path.as_os_str().as_encoded_bytes()));
    read_whole(driver, handler, &request, None)
}

// --- Category parsers ---

pub fn drive<H: Handler, P: Category<H>>(
    path: OsString,
    handler: &mut H,
    input: &[u8],
    count: usize,
) -> Result<(Vec<P::Result>, usize), ParseFailure> {
    let text = String::from_utf8_lossy(input).into_owned();
    let request = format!("drive {} 2.7 {count} s{} e", P::lean_name(), hex(input));
    let mut values = Values::<H>::new();
    let lines = converse(&path, &request, &mut |method, fields| {
        handler_call(handler, &mut values, method, fields).unwrap_or_else(|| unknown_call(method))
    });
    let mut results = Vec::new();
    for line in &lines {
        let mut fields = Fields::new(line);
        match fields.next() {
            "result" => {
                results.push(P::read_lean(&mut fields, &mut values));
                fields.end();
            }
            "ok" => {
                let unconsumed = fields.count();
                fields.end();
                return Ok((results, unconsumed));
            }
            "error" => {
                let err = read_error(&mut fields, &mut values);
                let span = err.span();
                return match err.into_cause() {
                    ReadErrorCause::Syntax(kind) => Err((kind, span)),
                    ReadErrorCause::Lexical(kind) => {
                        panic!("test input {text:?} must lex, got {kind:?}")
                    }
                    _ => panic!("the handler must not fail on {text:?}"),
                };
            }
            _ => panic!("the Lean driver answered {request:?} with {line:?}"),
        }
    }
    panic!("the Lean driver's response to {request:?} has no ending line: {lines:?}")
}

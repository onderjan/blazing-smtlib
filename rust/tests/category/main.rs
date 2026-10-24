//! Public-API tests of the category parsers: the single-token parsers, the
//! generic combinators, and the ident, qualified-ident, sort, term, s-expression
//! and attribute parsers, each driven in isolation through `SmtParse`.
//!
//! This file holds the shared test handler and driver; the tests themselves
//! live in the submodules under `category/`.
//!
//! The parsers run against the backend that `parse_backend` selects: the Rust
//! library's, or the Lean port's through the Lean driver, which has the
//! parsers of sorts, s-expressions and terms. Tokens cannot be constructed
//! outside the crate, so the driver feeds the parser under test by pushing
//! the input through a lexer whose token consumer advances the parser.

#[path = "../parse_backend/mod.rs"]
mod parse_backend;

mod attribute;
mod combinator;
mod ident;
mod qualified_ident;
mod quoted;
mod reserved;
mod reuse;
mod s_expr;
mod single_token;
mod sort;
mod term;

use std::convert::Infallible;

use parse_backend::{
    AttributeValue, Bindings, Category, CloseParenParser, ClosedAttributeParser,
    ClosedMultipleAttributeParser, ClosedMultipleParser, ClosedParser, Handler, IdentParser,
    KeywordParser, MatchCases, OpenParenParser, PairParser, ParenMultipleParser, ParenParser,
    ParseFailure, QualifiedIdent, QualifiedIdentParser, SExpr, SExprParser, Sort, SortParser,
    SortedVars, StringParser, SymbolParser, Term, TermParser,
};

use blazing_smtlib::{
    SmtIdentBuf, SmtIndex, SmtKeywordBuf, SmtPatternBuf, SmtQuantifierKind, SmtSimplePattern,
    SmtSpecialConstantBuf, SmtSymbol, SmtSymbolBuf, parser::SmtSyntaxErrorKind, token::SmtVersion,
};

// --- Test handler rendering everything it receives back into text ---

/// Handler that renders every sort, term, s-expression and attribute
/// it is given back into SMT-LIB text, so parser results can be checked as strings.
///
/// A binder's scope value is its rendered opening, given back at its end.
/// The scrutinees of the matches open are kept to check that each case and
/// each match end is given back the scrutinee of its own match.
#[derive(Default)]
struct Printing {
    /// Scrutinees of the matches currently open, innermost last.
    scrutinees: Vec<String>,
}

fn render_simple_pattern(pattern: SmtSimplePattern<'_>) -> String {
    match pattern {
        SmtSimplePattern::Symbol(symbol) => render_symbol(&symbol),
        SmtSimplePattern::Wildcard => "_".into(),
    }
}

fn render_pattern(pattern: &SmtPatternBuf) -> String {
    match pattern {
        SmtPatternBuf::Simple(simple) => render_simple_pattern(simple.view()),
        SmtPatternBuf::Application(application) => {
            let mut items = vec![render_symbol(application.constructor())];
            items.extend(application.args().iter().map(render_simple_pattern));
            render_list(&items)
        }
    }
}

/// Renders sorted variables as written, `((x Int) (y Bool))`.
fn render_sorted_vars(vars: &SortedVars<String>) -> String {
    let vars: Vec<String> = vars
        .iter()
        .map(|(name, sort)| format!("({} {})", render_symbol(&name), sort))
        .collect();
    render_list(&vars)
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).expect("test inputs are ASCII")
}

/// A symbol, by reference or not, as the handler is given it.
trait SymbolText {
    fn is_quoted(&self) -> bool;
    fn as_slice(&self) -> &[u8];
}

impl<T: SymbolText> SymbolText for &T {
    fn is_quoted(&self) -> bool {
        T::is_quoted(self)
    }
    fn as_slice(&self) -> &[u8] {
        T::as_slice(self)
    }
}

impl SymbolText for SmtSymbolBuf {
    fn is_quoted(&self) -> bool {
        SmtSymbolBuf::is_quoted(self)
    }
    fn as_slice(&self) -> &[u8] {
        SmtSymbolBuf::as_slice(self)
    }
}

impl SymbolText for SmtSymbol<'_> {
    fn is_quoted(&self) -> bool {
        SmtSymbol::is_quoted(self)
    }
    fn as_slice(&self) -> &[u8] {
        SmtSymbol::as_slice(self)
    }
}

/// Renders a symbol as it was written: in pipes when it was quoted, so that
/// the rendering also shows that the quoting reached the handler.
fn render_symbol(symbol: &impl SymbolText) -> String {
    let bytes = text(symbol.as_slice());
    if symbol.is_quoted() {
        format!("|{bytes}|")
    } else {
        bytes
    }
}

fn render_ident(ident: &SmtIdentBuf) -> String {
    let name = render_symbol(&ident.name);
    if ident.indices.is_empty() {
        return name;
    }
    let mut out = format!("(_ {name}");
    for index in ident.indices.iter() {
        out.push(' ');
        match index {
            SmtIndex::Numeral(numeral) => out.push_str(&text(numeral.as_slice())),
            SmtIndex::Symbol(symbol) => out.push_str(&render_symbol(&symbol)),
        }
    }
    out.push(')');
    out
}

fn render_qualified_ident(qualified_ident: &QualifiedIdent<String>) -> String {
    let ident = render_ident(&qualified_ident.ident);
    match &qualified_ident.sort {
        Some(sort) => format!("(as {ident} {sort})"),
        None => ident,
    }
}

fn render_constant(constant: &SmtSpecialConstantBuf) -> String {
    match constant {
        SmtSpecialConstantBuf::Numeral(n) => text(n.as_slice()),
        SmtSpecialConstantBuf::Decimal(d) => text(d.as_slice()),
        SmtSpecialConstantBuf::Hexadecimal(h) => format!("#x{}", text(h.as_slice())),
        SmtSpecialConstantBuf::Binary(b) => format!("#b{}", text(b.as_slice())),
        SmtSpecialConstantBuf::String(s) => format!("\"{}\"", text(s.as_slice())),
    }
}

fn render_list(items: &[String]) -> String {
    format!("({})", items.join(" "))
}

impl Handler for Printing {
    type Error = Infallible;
    type SExpr = String;
    type Attribute = String;
    type Sort = String;
    type Term = String;
    type Scope = String;

    fn set_version(&mut self, _version: SmtVersion) {}

    fn handle_sort(&mut self, sort: Sort<Self::Sort>) -> Result<String, Infallible> {
        let ident = render_ident(&sort.ident);
        Ok(if sort.applied.is_empty() {
            ident
        } else {
            let mut items = vec![ident];
            items.extend(sort.applied);
            render_list(&items)
        })
    }

    fn handle_term(&mut self, term: Term<Self::Sort, Self::Term>) -> Result<String, Infallible> {
        Ok(match term {
            Term::SpecialConstant(constant) => render_constant(&constant),
            Term::QualifiedIdent(qualified_ident) => render_qualified_ident(&qualified_ident),
            Term::Application(application) => {
                let mut items = vec![render_qualified_ident(&application.function)];
                items.extend(application.args);
                render_list(&items)
            }
        })
    }

    fn start_let(&mut self, bindings: Bindings<Self::Term>) -> Result<String, Infallible> {
        let bindings: Vec<String> = bindings
            .into_iter()
            .map(|(name, term)| format!("({} {})", render_symbol(&name), term))
            .collect();
        Ok(format!("(let {}", render_list(&bindings)))
    }

    fn end_let(&mut self, scope: String, body: String) -> Result<String, Infallible> {
        Ok(format!("{scope} {body})"))
    }

    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        vars: SortedVars<Self::Sort>,
    ) -> Result<String, Infallible> {
        // the keyword is rendered at the end, from the kind given back there
        Ok(render_sorted_vars(&vars))
    }

    fn end_quantifier(
        &mut self,
        kind: SmtQuantifierKind,
        scope: String,
        body: String,
    ) -> Result<String, Infallible> {
        let keyword = match kind {
            SmtQuantifierKind::Forall => "forall",
            SmtQuantifierKind::Exists => "exists",
        };
        Ok(format!("({keyword} {scope} {body})"))
    }

    fn start_lambda(&mut self, vars: SortedVars<Self::Sort>) -> Result<String, Infallible> {
        Ok(format!("(lambda {}", render_sorted_vars(&vars)))
    }

    fn end_lambda(&mut self, scope: String, body: String) -> Result<String, Infallible> {
        Ok(format!("{scope} {body})"))
    }

    fn start_match(&mut self, scrutinee: &String) -> Result<(), Infallible> {
        self.scrutinees.push(scrutinee.clone());
        Ok(())
    }

    fn start_match_case(
        &mut self,
        scrutinee: &String,
        pattern: SmtPatternBuf,
    ) -> Result<String, Infallible> {
        assert_eq!(
            self.scrutinees.last(),
            Some(scrutinee),
            "start_match_case is given the scrutinee of its own match"
        );
        Ok(render_pattern(&pattern))
    }

    fn end_match_case(
        &mut self,
        scope: String,
        scrutinee: &String,
        body: String,
    ) -> Result<String, Infallible> {
        assert_eq!(
            self.scrutinees.last(),
            Some(scrutinee),
            "end_match_case is given the scrutinee of its own match"
        );
        Ok(format!("({scope} {body})"))
    }

    fn end_match(
        &mut self,
        scrutinee: String,
        cases: MatchCases<Self::Term>,
    ) -> Result<String, Infallible> {
        let open = self
            .scrutinees
            .pop()
            .expect("end_match without start_match");
        assert_eq!(
            open, scrutinee,
            "end_match is given the scrutinee of its own match"
        );
        // each case term was rendered with the pattern its case started with,
        // which must be the pattern handed over with it
        let cases: Vec<String> = cases
            .into_iter()
            .map(|(pattern, term)| {
                let pattern = render_pattern(&pattern);
                assert!(
                    term.starts_with(&format!("({pattern} ")),
                    "case {term} is handed over with the pattern {pattern}"
                );
                term
            })
            .collect();
        Ok(format!("(match {scrutinee} {})", render_list(&cases)))
    }

    fn handle_s_expr(&mut self, expr: SExpr<Self::SExpr>) -> Result<String, Infallible> {
        Ok(match expr {
            SExpr::SpecialConstant(constant) => render_constant(&constant),
            SExpr::Symbol(symbol) => render_symbol(&symbol),
            SExpr::Reserved(reserved) => reserved.as_str().to_string(),
            SExpr::Keyword(keyword) => format!(":{}", text(keyword.as_slice())),
            SExpr::SExprs(exprs) => render_list(exprs.as_slice()),
        })
    }

    fn handle_attribute(
        &mut self,
        name: SmtKeywordBuf,
        value: Option<AttributeValue<Self::SExpr>>,
    ) -> Result<String, Infallible> {
        let name = format!(":{}", text(name.as_slice()));
        Ok(match value {
            None => name,
            Some(AttributeValue::SpecialConstant(constant)) => {
                format!("{name} {}", render_constant(&constant))
            }
            Some(AttributeValue::Symbol(symbol)) => {
                format!("{name} {}", render_symbol(&symbol))
            }
            Some(AttributeValue::SExprs(exprs)) => {
                format!("{name} {}", render_list(exprs.as_slice()))
            }
        })
    }

    fn annotate_term(
        &mut self,
        term: String,
        attributes: Vec<Self::Attribute>,
    ) -> Result<String, Infallible> {
        Ok(format!("(! {term} {})", attributes.as_slice().join(" ")))
    }
}

// --- Test handler recording the calls of binders, matches and attributes ---

/// Handler that records the calls of the binders, matches and attributes, by name.
#[derive(Default)]
struct Calls {
    calls: Vec<&'static str>,
}

impl Handler for Calls {
    type Error = Infallible;
    type SExpr = ();
    type Attribute = ();
    type Sort = ();
    type Term = ();
    type Scope = ();

    fn set_version(&mut self, _version: SmtVersion) {}

    fn handle_sort(&mut self, _sort: Sort<Self::Sort>) -> Result<(), Infallible> {
        Ok(())
    }
    fn handle_term(&mut self, _term: Term<Self::Sort, Self::Term>) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_let(&mut self, _bindings: Bindings<Self::Term>) -> Result<(), Infallible> {
        self.calls.push("start-let");
        Ok(())
    }
    fn end_let(&mut self, _scope: (), _body: ()) -> Result<(), Infallible> {
        self.calls.push("end-let");
        Ok(())
    }
    fn handle_s_expr(&mut self, _expr: SExpr<Self::SExpr>) -> Result<(), Infallible> {
        Ok(())
    }
    fn handle_attribute(
        &mut self,
        _name: SmtKeywordBuf,
        _value: Option<AttributeValue<Self::SExpr>>,
    ) -> Result<(), Infallible> {
        self.calls.push("handle-attribute");
        Ok(())
    }
    fn annotate_term(
        &mut self,
        _term: (),
        _attributes: Vec<Self::Attribute>,
    ) -> Result<(), Infallible> {
        self.calls.push("annotate-term");
        Ok(())
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _vars: SortedVars<Self::Sort>,
    ) -> Result<(), Infallible> {
        self.calls.push("start-quantifier");
        Ok(())
    }
    fn end_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _scope: (),
        _body: (),
    ) -> Result<(), Infallible> {
        self.calls.push("end-quantifier");
        Ok(())
    }
    fn start_lambda(&mut self, _vars: SortedVars<Self::Sort>) -> Result<(), Infallible> {
        self.calls.push("start-lambda");
        Ok(())
    }
    fn end_lambda(&mut self, _scope: (), _body: ()) -> Result<(), Infallible> {
        self.calls.push("end-lambda");
        Ok(())
    }
    fn start_match(&mut self, _scrutinee: &()) -> Result<(), Infallible> {
        self.calls.push("start-match");
        Ok(())
    }
    fn start_match_case(
        &mut self,
        _scrutinee: &(),
        _pattern: SmtPatternBuf,
    ) -> Result<(), Infallible> {
        self.calls.push("start-match-case");
        Ok(())
    }
    fn end_match_case(&mut self, _scope: (), _scrutinee: &(), _body: ()) -> Result<(), Infallible> {
        self.calls.push("end-match-case");
        Ok(())
    }
    fn end_match(
        &mut self,
        _scrutinee: (),
        _cases: MatchCases<Self::Term>,
    ) -> Result<(), Infallible> {
        self.calls.push("end-match");
        Ok(())
    }
}

// --- Driver ---

/// Lexes the input and drives a fresh parser `P` over the given handler
/// through `count` consecutive parses, the same parser instance each time,
/// with the backend that `parse_backend` selects.
///
/// Returns the parser results and the number of tokens left unconsumed
/// (not counting the end-of-file token), so tests can check where the parser stopped;
/// a parser error is returned as its kind and span.
/// Panics if the parser did not finish `count` times before the end of the input.
fn run_count_from<H: Handler<Error = Infallible>, P: Category<H>>(
    handler: &mut H,
    input: &[u8],
    count: usize,
) -> Result<(Vec<P::Result>, usize), ParseFailure> {
    parse_backend::drive::<H, P>(handler, input, count)
}

/// Lexes the input and feeds the tokens to a fresh parser `P` over the given handler.
///
/// Returns the parser result and the number of tokens left unconsumed
/// (not counting the end-of-file token), so tests can check where the parser stopped;
/// a parser error is returned as its kind and span.
/// Panics if the parser did not finish before the end of the input.
fn run_with<H: Handler<Error = Infallible>, P: Category<H>>(
    handler: &mut H,
    input: &[u8],
) -> Result<(P::Result, usize), ParseFailure> {
    let (results, unconsumed) = run_count_from::<H, P>(handler, input, 1)?;
    let result = results
        .into_iter()
        .next()
        .expect("a successful single-parse run has one result");
    Ok((result, unconsumed))
}

/// Runs the parser over a fresh `Printing` handler.
fn run<P: Category<Printing>>(input: &[u8]) -> Result<(P::Result, usize), ParseFailure> {
    run_with::<Printing, P>(&mut Printing::default(), input)
}

/// Runs one parser instance through two consecutive elements of its category,
/// requires success with no unconsumed tokens, and returns both results.
///
/// This exercises the self-reset contract: after `progress` returns Break,
/// the parser instance must be back in the default state.
#[track_caller]
fn parse_two<P: Category<Printing>>(input: &[u8]) -> (P::Result, P::Result) {
    match run_count_from::<Printing, P>(&mut Printing::default(), input, 2) {
        Ok((results, 0)) => {
            let mut results = results.into_iter();
            let first = results.next().expect("a two-parse run has two results");
            let second = results.next().expect("a two-parse run has two results");
            (first, second)
        }
        Ok((_, left)) => panic!("{left} tokens left unconsumed in {:?}", text(input)),
        Err((kind, span)) => {
            panic!("unexpected error {kind:?} at {span:?} in {:?}", text(input))
        }
    }
}

/// Runs the parser, requires success with no unconsumed tokens, and returns the result.
#[track_caller]
fn parse_all<P: Category<Printing>>(input: &[u8]) -> P::Result {
    match run::<P>(input) {
        Ok((result, 0)) => result,
        Ok((_, left)) => panic!("{left} tokens left unconsumed in {:?}", text(input)),
        Err((kind, span)) => {
            panic!("unexpected error {kind:?} at {span:?} in {:?}", text(input))
        }
    }
}

/// Runs the parser, requires a parser error, checks the byte span the error carries,
/// and returns its kind so that the caller can inspect the variant.
#[track_caller]
fn assert_error<P: Category<Printing>>(input: &[u8], start: u64, end: u64) -> SmtSyntaxErrorKind {
    match run::<P>(input) {
        Ok(_) => panic!("expected a parser error in {:?}, got Ok", text(input)),
        Err((kind, span)) => {
            assert_eq!(
                (span.start().offset(), span.end().offset()),
                (start, end),
                "error span mismatch (start, end) as byte offsets for {kind:?} in {:?}",
                text(input)
            );
            kind
        }
    }
}

//! Public-API tests of the category parsers: the single-token parsers, the
//! generic combinators, and the ident, qualified-ident, sort, term, s-expression
//! and attribute parsers, each driven in isolation through `SmtParse`.
//!
//! This file holds the shared test handler and driver; the tests themselves
//! live in the submodules under `category/`.
//!
//! Tokens cannot be constructed outside the crate, so the driver feeds the
//! parser under test by pushing the input through a `SmtLexer` whose token consumer
//! advances the parser.

mod attribute;
mod combinator;
mod ident;
mod qualified_ident;
mod reserved;
mod reuse;
mod s_expr;
mod single_token;
mod sort;
mod term;

use std::convert::Infallible;
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtAttributeValue, SmtAttributes, SmtBindings, SmtHandler, SmtIdent, SmtIdentView, SmtIndex,
    SmtIndexView, SmtKeywordView, SmtPatternView, SmtQualifiedIdent, SmtQualifiedIdentView,
    SmtQuantifierKind, SmtSExpr, SmtSimplePatternView, SmtSort, SmtSpan, SmtSpecialConstantView,
    SmtSymbolView, SmtTerm,
    lexer::{SmtLexErrorCause, SmtLexer},
    parser::{
        SmtCloseParenParser, SmtClosedAttributeParser, SmtClosedMultipleAttributeParser,
        SmtClosedMultipleParser, SmtClosedParser, SmtIdentParser, SmtKeywordParser,
        SmtOpenParenParser, SmtPairParser, SmtParenMultipleParser, SmtParenParser, SmtParse,
        SmtParseError, SmtParseErrorCause, SmtParseState, SmtQualifiedIdentParser, SmtSExprParser,
        SmtSortParser, SmtStringParser, SmtSymbolParser, SmtSyntaxErrorKind, SmtTermParser,
    },
    token::{SmtBatchCursor, SmtConsume, SmtReserved, SmtTokenCategory, SmtVersion},
};

// --- Test handler rendering everything it receives back into text ---

/// Handler that renders every sort, term, s-expression and attribute
/// it is given back into SMT-LIB text, so parser results can be checked as strings.
#[derive(Default)]
struct Printing {
    /// Rendered binding lists of the lets currently being parsed, innermost last.
    let_bindings: Vec<String>,
    /// Rendered prefixes of the quantifiers currently open, innermost last.
    quantifier_binders: Vec<String>,
    /// Rendered prefixes of the lambdas currently open, innermost last.
    lambda_binders: Vec<String>,
    /// Matches currently open, innermost last.
    matches: Vec<PrintingMatch>,
}

/// A match being rendered: its scrutinee, the finished cases,
/// and the pattern of the case in progress.
struct PrintingMatch {
    scrutinee: String,
    cases: Vec<String>,
    pattern: Option<String>,
}

fn render_simple_pattern(pattern: SmtSimplePatternView<'_>) -> String {
    match pattern {
        SmtSimplePatternView::Symbol(symbol) => render_symbol(symbol.as_slice()),
        SmtSimplePatternView::Wildcard => "_".into(),
    }
}

fn render_pattern(pattern: SmtPatternView<'_>) -> String {
    match pattern {
        SmtPatternView::Simple(simple) => render_simple_pattern(simple),
        SmtPatternView::Application { constructor, args } => {
            let mut items = vec![render_symbol(constructor.as_slice())];
            items.extend(args.iter().map(render_simple_pattern));
            render_list(&items)
        }
    }
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).expect("test inputs are ASCII")
}

/// Renders a symbol, quoting it when it is spelled like a reserved word,
/// so that the rendering tells such a symbol apart from the reserved word.
fn render_symbol(bytes: &[u8]) -> String {
    if SmtReserved::from_bytes_opt(bytes, SmtVersion::V2_7).is_some() {
        format!("|{}|", text(bytes))
    } else {
        text(bytes)
    }
}

fn render_ident(ident: &SmtIdent) -> String {
    let name = render_symbol(ident.name.as_slice());
    if ident.indices.is_empty() {
        return name;
    }
    let mut out = format!("(_ {name}");
    for index in &ident.indices {
        out.push(' ');
        match index {
            SmtIndex::Numeral(numeral) => out.push_str(&text(numeral.as_slice())),
            SmtIndex::Symbol(symbol) => out.push_str(&render_symbol(symbol.as_slice())),
        }
    }
    out.push(')');
    out
}

fn render_ident_view(ident: &SmtIdentView) -> String {
    let name = render_symbol(ident.name.as_slice());
    if ident.indices.is_empty() {
        return name;
    }
    let mut out = format!("(_ {name}");
    for index in ident.indices.iter() {
        out.push(' ');
        match index {
            SmtIndexView::Numeral(numeral) => out.push_str(&text(numeral.as_slice())),
            SmtIndexView::Symbol(symbol) => out.push_str(&render_symbol(symbol.as_slice())),
        }
    }
    out.push(')');
    out
}

fn render_qualified_ident_view(qualified_ident: &SmtQualifiedIdentView<Printing>) -> String {
    let ident = render_ident_view(&qualified_ident.ident);
    match &qualified_ident.sort {
        Some(sort) => format!("(as {ident} {sort})"),
        None => ident,
    }
}

fn render_qualified_ident(qualified_ident: &SmtQualifiedIdent<Printing>) -> String {
    let ident = render_ident(&qualified_ident.ident);
    match &qualified_ident.sort {
        Some(sort) => format!("(as {ident} {sort})"),
        None => ident,
    }
}

fn render_constant(constant: SmtSpecialConstantView<'_>) -> String {
    match constant {
        SmtSpecialConstantView::Numeral(n) => text(n.as_slice()),
        SmtSpecialConstantView::Decimal(d) => text(d.as_slice()),
        SmtSpecialConstantView::Hexadecimal(h) => format!("#x{}", text(h.as_slice())),
        SmtSpecialConstantView::Binary(b) => format!("#b{}", text(b.as_slice())),
        SmtSpecialConstantView::String(s) => format!("\"{}\"", text(s.as_slice())),
    }
}

fn render_list(items: &[String]) -> String {
    format!("({})", items.join(" "))
}

impl SmtHandler for Printing {
    type Error = Infallible;
    type SExpr = String;
    type Attribute = String;
    type Sort = String;
    type Term = String;

    fn handle_sort(&mut self, sort: SmtSort<'_, Self>) -> Result<String, Infallible> {
        let ident = render_ident_view(&sort.ident);
        Ok(if sort.applied.is_empty() {
            ident
        } else {
            let mut items = vec![ident];
            items.extend(sort.applied);
            render_list(&items)
        })
    }

    fn handle_term(&mut self, term: SmtTerm<'_, Self>) -> Result<String, Infallible> {
        Ok(match term {
            SmtTerm::SpecialConstant(constant) => render_constant(constant),
            SmtTerm::QualifiedIdent(qualified_ident) => {
                render_qualified_ident_view(&qualified_ident)
            }
            SmtTerm::Application(application) => {
                let mut items = vec![render_qualified_ident_view(&application.function)];
                items.extend(application.args);
                render_list(&items)
            }
        })
    }

    fn start_let(&mut self, bindings: SmtBindings<'_, Self>) -> Result<(), Infallible> {
        let bindings: Vec<String> = bindings
            .into_iter()
            .map(|(name, term)| format!("({} {})", render_symbol(name.as_slice()), term))
            .collect();
        self.let_bindings.push(render_list(&bindings));
        Ok(())
    }

    fn end_let(&mut self, term: String) -> Result<String, Infallible> {
        let bindings = self.let_bindings.pop().expect("end_let without start_let");
        Ok(format!("(let {bindings} {term})"))
    }

    fn start_quantifier(
        &mut self,
        kind: SmtQuantifierKind,
        name: SmtSymbolView<'_>,
        sort: String,
    ) -> Result<(), Infallible> {
        let keyword = match kind {
            SmtQuantifierKind::Forall => "forall",
            SmtQuantifierKind::Exists => "exists",
        };
        self.quantifier_binders.push(format!(
            "({} (({} {}))",
            keyword,
            render_symbol(name.as_slice()),
            sort
        ));
        Ok(())
    }

    fn end_quantifier(&mut self, term: String) -> Result<String, Infallible> {
        let prefix = self
            .quantifier_binders
            .pop()
            .expect("end_quantifier without matching start_quantifier");
        Ok(format!("{prefix} {term})"))
    }

    fn start_lambda(&mut self, name: SmtSymbolView<'_>, sort: String) -> Result<(), Infallible> {
        self.lambda_binders.push(format!(
            "(lambda (({} {}))",
            render_symbol(name.as_slice()),
            sort
        ));
        Ok(())
    }

    fn end_lambda(&mut self, term: String) -> Result<String, Infallible> {
        let prefix = self
            .lambda_binders
            .pop()
            .expect("end_lambda without matching start_lambda");
        Ok(format!("{prefix} {term})"))
    }

    fn start_match(&mut self, scrutinee: String) -> Result<(), Infallible> {
        self.matches.push(PrintingMatch {
            scrutinee,
            cases: Vec::new(),
            pattern: None,
        });
        Ok(())
    }

    fn start_match_case(&mut self, pattern: SmtPatternView<'_>) -> Result<(), Infallible> {
        let current = self
            .matches
            .last_mut()
            .expect("start_match_case without start_match");
        assert!(
            current.pattern.is_none(),
            "start_match_case while a case is still open"
        );
        current.pattern = Some(render_pattern(pattern));
        Ok(())
    }

    fn end_match_case(&mut self, term: String) -> Result<(), Infallible> {
        let current = self
            .matches
            .last_mut()
            .expect("end_match_case without start_match");
        let pattern = current
            .pattern
            .take()
            .expect("end_match_case without start_match_case");
        current.cases.push(format!("({pattern} {term})"));
        Ok(())
    }

    fn end_match(&mut self) -> Result<String, Infallible> {
        let current = self.matches.pop().expect("end_match without start_match");
        assert!(
            current.pattern.is_none(),
            "end_match while a case is still open"
        );
        Ok(format!(
            "(match {} {})",
            current.scrutinee,
            render_list(&current.cases)
        ))
    }

    fn handle_s_expr(&mut self, expr: SmtSExpr<'_, Self>) -> Result<String, Infallible> {
        Ok(match expr {
            SmtSExpr::SpecialConstant(constant) => render_constant(constant),
            SmtSExpr::Symbol(symbol) => render_symbol(symbol.as_slice()),
            SmtSExpr::Reserved(reserved) => reserved.as_str().to_string(),
            SmtSExpr::Keyword(keyword) => format!(":{}", text(keyword.as_slice())),
            SmtSExpr::SExprs(exprs) => render_list(exprs.as_slice()),
        })
    }

    fn handle_attribute(
        &mut self,
        name: SmtKeywordView<'_>,
        value: Option<SmtAttributeValue<'_, Self>>,
    ) -> Result<String, Infallible> {
        let name = format!(":{}", text(name.as_slice()));
        Ok(match value {
            None => name,
            Some(SmtAttributeValue::SpecialConstant(constant)) => {
                format!("{name} {}", render_constant(constant))
            }
            Some(SmtAttributeValue::Symbol(symbol)) => {
                format!("{name} {}", render_symbol(symbol.as_slice()))
            }
            Some(SmtAttributeValue::SExprs(exprs)) => {
                format!("{name} {}", render_list(exprs.as_slice()))
            }
        })
    }

    fn annotate_term(
        &mut self,
        term: String,
        attributes: SmtAttributes<'_, Self>,
    ) -> Result<String, Infallible> {
        Ok(format!("(! {term} {})", attributes.as_slice().join(" ")))
    }
}

// --- Driver ---

/// A parse failure, as the error kind and the span it carries.
type ParseFailure = (SmtSyntaxErrorKind, SmtSpan);

/// Token consumer that advances a category parser with each lexed token,
/// collecting a wanted number of consecutive parser results, and counts
/// the tokens left over after the last one.
///
/// The parser instance is reused for every result in turn, so driving with
/// a wanted count above one exercises the self-reset contract.
struct Drive<'h, H: SmtHandler, P: SmtParse<H>> {
    handler: &'h mut H,
    /// The parser resources, shared by every parser in a run.
    parse_state: SmtParseState<H>,
    /// The parser under test, reused across parses.
    parser: P,
    /// How many more results to parse before tokens count as unconsumed.
    remaining: usize,
    /// The results of the finished parses.
    results: Vec<P::Result>,
    /// The number of unconsumed tokens after the last wanted result.
    unconsumed: usize,
}

impl<H: SmtHandler, P: SmtParse<H>> SmtConsume for Drive<'_, H, P> {
    type Result = ();
    type Error = SmtParseError<H::Error>;
    const IS_CONCRETE: bool = false;

    fn consume(&mut self, cursor: &mut SmtBatchCursor<'_>) -> Result<ControlFlow<()>, Self::Error> {
        while !cursor.is_empty() {
            if self.remaining == 0 {
                // count the tokens left after the wanted results, except the end of the input
                while let Some(token) = cursor.next() {
                    if token.category() != SmtTokenCategory::EndOfFile {
                        self.unconsumed += 1;
                    }
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

/// Lexes the input and feeds the tokens to the given parser over the given handler,
/// driving the same parser instance through `count` consecutive parses.
///
/// Returns the parser results and the number of tokens left unconsumed
/// (not counting the end-of-file token), so tests can check where the parser stopped;
/// a parser error is returned as its kind and span.
/// Panics if the parser did not finish `count` times before the end of the input.
fn run_count_from<H: SmtHandler<Error = Infallible>, P: SmtParse<H>>(
    parser: P,
    handler: &mut H,
    input: &[u8],
    count: usize,
) -> Result<(Vec<P::Result>, usize), ParseFailure> {
    let mut drive = Drive {
        handler,
        parse_state: SmtParseState::new(),
        parser,
        remaining: count,
        results: Vec::new(),
        unconsumed: 0,
    };
    let mut lexer = SmtLexer::new(&mut drive, SmtVersion::V2_7);
    match lexer.lex_all(input).map_err(|err| err.into_cause()) {
        Ok(_) => {}
        Err(SmtLexErrorCause::Consumer(err)) => {
            let span = err.span();
            return Err(match err.into_cause() {
                SmtParseErrorCause::Syntax(kind) => (kind, span),
                // the handler never fails
                SmtParseErrorCause::Handler(err) => match err {},
            });
        }
        Err(SmtLexErrorCause::Lexical(err)) => {
            panic!(
                "test input {:?} must lex, got {:?}",
                text(input),
                err.kind()
            )
        }
    }
    drop(lexer);
    assert!(
        drive.results.len() == count,
        "parser finished {} of {count} times before the end of input {:?}",
        drive.results.len(),
        text(input)
    );
    Ok((drive.results, drive.unconsumed))
}

/// Lexes the input and feeds the tokens to a fresh parser `P` over the given handler.
///
/// Returns the parser result and the number of tokens left unconsumed
/// (not counting the end-of-file token), so tests can check where the parser stopped;
/// a parser error is returned as its kind and span.
/// Panics if the parser did not finish before the end of the input.
fn run_with<H: SmtHandler<Error = Infallible>, P: SmtParse<H> + Default>(
    handler: &mut H,
    input: &[u8],
) -> Result<(P::Result, usize), ParseFailure> {
    let (results, unconsumed) = run_count_from(P::default(), handler, input, 1)?;
    let result = results
        .into_iter()
        .next()
        .expect("a successful single-parse run has one result");
    Ok((result, unconsumed))
}

/// Runs the parser over a fresh `Printing` handler.
fn run<P: SmtParse<Printing> + Default>(input: &[u8]) -> Result<(P::Result, usize), ParseFailure> {
    run_with::<Printing, P>(&mut Printing::default(), input)
}

/// Runs one parser instance through two consecutive elements of its category,
/// requires success with no unconsumed tokens, and returns both results.
///
/// This exercises the self-reset contract: after `progress` returns Break,
/// the parser instance must be back in the default state.
#[track_caller]
fn parse_two<P: SmtParse<Printing> + Default>(input: &[u8]) -> (P::Result, P::Result) {
    match run_count_from(P::default(), &mut Printing::default(), input, 2) {
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
fn parse_all<P: SmtParse<Printing> + Default>(input: &[u8]) -> P::Result {
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
fn assert_error<P: SmtParse<Printing> + Default>(
    input: &[u8],
    start: u64,
    end: u64,
) -> SmtSyntaxErrorKind {
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

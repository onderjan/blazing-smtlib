//! Public-API tests of the category parsers: the single-token parsers, the
//! generic combinators, and the ident, qualified-ident, sort, term, s-expression
//! and attribute parsers, each driven in isolation through `CategoryParser`.
//!
//! This file holds the shared test handler and driver; the tests themselves
//! live in the submodules under `category/`.
//!
//! Tokens cannot be constructed outside the crate, so the driver feeds the
//! parser under test by pushing the input through a `Lexer` whose token handler
//! advances the parser.

mod attribute;
mod combinator;
mod ident;
mod qualified_ident;
mod s_expr;
mod single_token;
mod sort;
mod term;

use std::convert::Infallible;
use std::ops::ControlFlow;

use smt_parser_rs::{
    SmtAttributeValue, SmtHandler, SmtIdent, SmtIndex, SmtKeyword, SmtQualifiedIdent, SmtSExpr,
    SmtSort, SmtSpan, SmtSpecialConstant, SmtSymbol, SmtTerm,
    read::{
        lexer::{LexError, Lexer, TokenHandler},
        parser::{
            CategoryParser, CategoryParserErrorKind, CloseParenParser, ClosedAttributeParser,
            ClosedParser, IdentParser, KeywordParser, MultipleParser, OpenClosedParser,
            OpenParenParser, PairParser, ParserError, ParserErrorKind, QualifiedIdentParser,
            SExprParser, SortParser, StringParser, SymbolParser, TermParser,
        },
    },
    token::{Reserved, Token, TokenType},
};

// --- Test handler rendering everything it receives back into text ---

/// Handler that renders every sort, term, s-expression and attribute
/// it is given back into SMT-LIB text, so parser results can be checked as strings.
#[derive(Default)]
struct Printing {
    /// Rendered binding lists of the lets currently being parsed, innermost last.
    let_bindings: Vec<String>,
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).expect("test inputs are ASCII")
}

fn render_ident(ident: &SmtIdent) -> String {
    let name = text(ident.name.as_slice());
    if ident.indices.is_empty() {
        return name;
    }
    let mut out = format!("(_ {name}");
    for index in &ident.indices {
        out.push(' ');
        match index {
            SmtIndex::Numeral(numeral) => out.push_str(&text(numeral.as_slice())),
            SmtIndex::Symbol(symbol) => out.push_str(&text(symbol.as_slice())),
        }
    }
    out.push(')');
    out
}

fn render_qualified_ident(qualified_ident: &SmtQualifiedIdent<Printing>) -> String {
    let ident = render_ident(&qualified_ident.ident);
    match &qualified_ident.sort {
        Some(sort) => format!("(as {ident} {sort})"),
        None => ident,
    }
}

fn render_constant(constant: &SmtSpecialConstant) -> String {
    match constant {
        SmtSpecialConstant::Numeral(n) => text(n.as_slice()),
        SmtSpecialConstant::Decimal(d) => text(d.as_slice()),
        SmtSpecialConstant::Hexadecimal(h) => format!("#x{}", text(h.as_slice())),
        SmtSpecialConstant::Binary(b) => format!("#b{}", text(b.as_slice())),
        SmtSpecialConstant::String(s) => format!("\"{}\"", text(s.as_slice())),
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

    fn handle_sort(&mut self, sort: SmtSort<Self>) -> Result<String, Infallible> {
        let ident = render_ident(&sort.ident);
        Ok(if sort.applied.is_empty() {
            ident
        } else {
            let mut items = vec![ident];
            items.extend(sort.applied);
            render_list(&items)
        })
    }

    fn handle_term(&mut self, term: SmtTerm<Self>) -> Result<String, Infallible> {
        Ok(match term {
            SmtTerm::SpecialConstant(constant) => render_constant(&constant),
            SmtTerm::QualifiedIdent(qualified_ident) => render_qualified_ident(&qualified_ident),
            SmtTerm::Application(application) => {
                let mut items = vec![render_qualified_ident(&application.function)];
                items.extend(application.args);
                render_list(&items)
            }
        })
    }

    fn start_let(&mut self, bindings: Vec<(SmtSymbol, String)>) -> Result<(), Infallible> {
        let bindings: Vec<String> = bindings
            .into_iter()
            .map(|(name, term)| format!("({} {})", text(name.as_slice()), term))
            .collect();
        self.let_bindings.push(render_list(&bindings));
        Ok(())
    }

    fn end_let(&mut self, term: String) -> Result<String, Infallible> {
        let bindings = self.let_bindings.pop().expect("end_let without start_let");
        Ok(format!("(let {bindings} {term})"))
    }

    fn handle_s_expr(&mut self, expr: SmtSExpr<Self>) -> Result<String, Infallible> {
        Ok(match expr {
            SmtSExpr::SpecialConstant(constant) => render_constant(&constant),
            SmtSExpr::Symbol(symbol) => text(symbol.as_slice()),
            SmtSExpr::Reserved(reserved) => reserved.as_str().to_string(),
            SmtSExpr::Keyword(keyword) => format!(":{}", text(keyword.as_slice())),
            SmtSExpr::SExprs(exprs) => render_list(&exprs),
        })
    }

    fn handle_attribute(
        &mut self,
        name: SmtKeyword,
        value: Option<SmtAttributeValue<Self>>,
    ) -> Result<String, Infallible> {
        let name = format!(":{}", text(name.as_slice()));
        Ok(match value {
            None => name,
            Some(SmtAttributeValue::SpecialConstant(constant)) => {
                format!("{name} {}", render_constant(&constant))
            }
            Some(SmtAttributeValue::Symbol(symbol)) => {
                format!("{name} {}", text(symbol.as_slice()))
            }
            Some(SmtAttributeValue::SExprs(exprs)) => format!("{name} {}", render_list(&exprs)),
        })
    }
}

// --- Driver ---

/// Token handler that advances a category parser with each lexed token
/// and counts the tokens left over after the parser finishes.
struct Drive<'h, H: SmtHandler, P: CategoryParser<H>> {
    handler: &'h mut H,
    /// The parser under test; `None` once it has finished.
    parser: Option<P>,
    /// The parser result and the number of unconsumed tokens after it.
    finished: Option<(P::Result, usize)>,
}

impl<H: SmtHandler, P: CategoryParser<H>> TokenHandler for Drive<'_, H, P> {
    type Error = ParserError<H>;

    fn handle_token(&mut self, token: Token) -> Result<(), Self::Error> {
        if let Some((_, unconsumed)) = &mut self.finished {
            if token.kind().ty() != TokenType::EndOfFile {
                *unconsumed += 1;
            }
            return Ok(());
        }
        let parser = self
            .parser
            .take()
            .expect("the parser must be present until it finishes");
        match parser.progress(self.handler, token)? {
            ControlFlow::Continue(next) => self.parser = Some(next),
            ControlFlow::Break(result) => self.finished = Some((result, 0)),
        }
        Ok(())
    }
}

/// Lexes the input and feeds the tokens to a fresh parser `P` over the given handler.
///
/// Returns the parser result and the number of tokens left unconsumed
/// (not counting the end-of-file token), so tests can check where the parser stopped;
/// a parser error is returned as its kind and span.
/// Panics if the parser did not finish before the end of the input.
fn run_with<H: SmtHandler<Error = Infallible>, P: CategoryParser<H>>(
    handler: &mut H,
    input: &[u8],
) -> Result<(P::Result, usize), (CategoryParserErrorKind, SmtSpan)> {
    let mut drive = Drive {
        handler,
        parser: Some(P::default()),
        finished: None,
    };
    let mut lexer = Lexer::new(&mut drive);
    match lexer.lex_all(input) {
        Ok(()) => {}
        Err(LexError::Handler(err)) => {
            let span = err.span();
            return Err(match err.into_kind() {
                ParserErrorKind::Category(kind) => (kind, span),
                // the handler never fails
                ParserErrorKind::Handler(err) => match err {},
            });
        }
        Err(LexError::Lexer(err)) => {
            panic!(
                "test input {:?} must lex, got {:?}",
                text(input),
                err.kind()
            )
        }
    }
    drop(lexer);
    Ok(drive.finished.unwrap_or_else(|| {
        panic!(
            "parser did not finish before the end of input {:?}",
            text(input)
        )
    }))
}

/// Runs the parser over a fresh `Printing` handler.
fn run<P: CategoryParser<Printing>>(
    input: &[u8],
) -> Result<(P::Result, usize), (CategoryParserErrorKind, SmtSpan)> {
    run_with::<Printing, P>(&mut Printing::default(), input)
}

/// Runs the parser, requires success with no unconsumed tokens, and returns the result.
#[track_caller]
fn parse_all<P: CategoryParser<Printing>>(input: &[u8]) -> P::Result {
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
fn assert_error<P: CategoryParser<Printing>>(
    input: &[u8],
    start: u64,
    end: u64,
) -> CategoryParserErrorKind {
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

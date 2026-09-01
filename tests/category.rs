//! Public-API tests of the category parsers: the single-token parsers, the
//! generic combinators, and the ident, qualified-ident, sort, term, s-expression
//! and attribute parsers, each driven in isolation through `CategoryParser`.
//!
//! Tokens cannot be constructed outside the crate, so the driver feeds the
//! parser under test by pushing the input through a `Lexer` whose token handler
//! advances the parser.

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

// --- Tests of the generic combinators ---

mod combinator {
    use super::*;

    #[test]
    fn pair_parser() {
        let (first, second) = parse_all::<PairParser<Printing, SymbolParser, SymbolParser>>(b"a b");
        assert_eq!(first.as_slice(), b"a");
        assert_eq!(second.as_slice(), b"b");

        // the error of the second element points at its token
        let err = assert_error::<PairParser<Printing, SymbolParser, SymbolParser>>(b"a 1", 2, 3);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
            ),
            "{err:?}"
        );
    }

    #[test]
    fn closed_parser() {
        let symbol = parse_all::<ClosedParser<Printing, SymbolParser>>(b"a)");
        assert_eq!(symbol.as_slice(), b"a");

        let err = assert_error::<ClosedParser<Printing, SymbolParser>>(b"a b", 2, 3);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
        // EOF instead of the closing parenthesis
        let err = assert_error::<ClosedParser<Printing, SymbolParser>>(b"a", 1, 1);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
    }

    #[test]
    fn open_closed_parser() {
        let symbol = parse_all::<OpenClosedParser<Printing, SymbolParser>>(b"(a)");
        assert_eq!(symbol.as_slice(), b"a");

        let err = assert_error::<OpenClosedParser<Printing, SymbolParser>>(b"a)", 0, 1);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
            ),
            "{err:?}"
        );
        let err = assert_error::<OpenClosedParser<Printing, SymbolParser>>(b"(a", 2, 2);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
    }

    #[test]
    fn multiple_parser() {
        let symbols = parse_all::<MultipleParser<Printing, SymbolParser>>(b"(a b c)");
        let symbols: Vec<&[u8]> = symbols.iter().map(|s| s.as_slice()).collect();
        assert_eq!(symbols, [b"a" as &[u8], b"b", b"c"]);

        // zero elements are allowed
        let symbols = parse_all::<MultipleParser<Printing, SymbolParser>>(b"()");
        assert!(symbols.is_empty());

        let err = assert_error::<MultipleParser<Printing, SymbolParser>>(b"a", 0, 1);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
            ),
            "{err:?}"
        );
        // the element parser's error is reported for a bad element
        let err = assert_error::<MultipleParser<Printing, SymbolParser>>(b"(a 1)", 3, 4);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
            ),
            "{err:?}"
        );
        // unclosed list ends at EOF inside the element parser
        let err = assert_error::<MultipleParser<Printing, SymbolParser>>(b"(a", 2, 2);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
            ),
            "{err:?}"
        );
    }

    #[test]
    fn nested_combinators() {
        // the shape used for define-fun parameters: ((x S) (y T))
        type Params = MultipleParser<
            Printing,
            OpenClosedParser<Printing, PairParser<Printing, SymbolParser, SymbolParser>>,
        >;
        let params = parse_all::<Params>(b"((x Int) (y Bool))");
        let params: Vec<(&[u8], &[u8])> = params
            .iter()
            .map(|(name, sort)| (name.as_slice(), sort.as_slice()))
            .collect();
        assert_eq!(params, [(b"x" as &[u8], b"Int" as &[u8]), (b"y", b"Bool")]);

        let err = assert_error::<Params>(b"((x Int) (y))", 11, 12);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
            ),
            "{err:?}"
        );
    }
}

// --- Tests of the single-token parsers ---

mod token {
    use super::*;

    #[test]
    fn symbol_parser() {
        let symbol = parse_all::<SymbolParser>(b"abc");
        assert_eq!(symbol.as_slice(), b"abc");
        let symbol = parse_all::<SymbolParser>(b"|quoted symbol|");
        assert_eq!(symbol.as_slice(), b"quoted symbol");

        let err = assert_error::<SymbolParser>(b"1", 0, 1);
        let expected_symbol = CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol]);
        assert_eq!(err, expected_symbol, "{err:?}");
        let err = assert_error::<SymbolParser>(b"(", 0, 1);
        assert_eq!(err, expected_symbol, "{err:?}");
        // reserved words are not symbols
        let err = assert_error::<SymbolParser>(b"let", 0, 3);
        assert_eq!(err, expected_symbol, "{err:?}");
    }

    #[test]
    fn symbol_parser_consumes_one_token() {
        let (symbol, left) = run::<SymbolParser>(b"a b c").expect("valid");
        assert_eq!(symbol.as_slice(), b"a");
        assert_eq!(left, 2);
    }

    #[test]
    fn open_paren_parser() {
        parse_all::<OpenParenParser>(b"(");

        let expected_open = CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen]);
        let err = assert_error::<OpenParenParser>(b")", 0, 1);
        assert_eq!(err, expected_open, "{err:?}");
        let err = assert_error::<OpenParenParser>(b"x", 0, 1);
        assert_eq!(err, expected_open, "{err:?}");
    }

    #[test]
    fn close_paren_parser() {
        parse_all::<CloseParenParser>(b")");

        let expected_close = CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose]);
        let err = assert_error::<CloseParenParser>(b"x", 0, 1);
        assert_eq!(err, expected_close, "{err:?}");
        // the end-of-file token does not match either; its span is zero-width
        let err = assert_error::<CloseParenParser>(b"", 0, 0);
        assert_eq!(err, expected_close, "{err:?}");
    }

    #[test]
    fn keyword_parser() {
        // the keyword content is stored without the leading colon
        let keyword = parse_all::<KeywordParser>(b":status");
        assert_eq!(keyword.as_slice(), b"status");

        let expected_keyword = CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword]);
        // a bare symbol is not a keyword
        let err = assert_error::<KeywordParser>(b"status", 0, 6);
        assert_eq!(err, expected_keyword, "{err:?}");
        let err = assert_error::<KeywordParser>(b"(", 0, 1);
        assert_eq!(err, expected_keyword, "{err:?}");
    }

    #[test]
    fn string_parser() {
        // the string content is stored without the enclosing quotes
        let string = parse_all::<StringParser>(b"\"hello world\"");
        assert_eq!(string.as_slice(), b"hello world");
        // a doubled quote is the escape for a single quote
        let string = parse_all::<StringParser>(b"\"a\"\"b\"");
        assert_eq!(string.as_slice(), b"a\"b");

        let expected_string = CategoryParserErrorKind::ExpectedToken(&[TokenType::String]);
        // neither a quoted symbol nor a numeral is a string literal
        let err = assert_error::<StringParser>(b"|hello|", 0, 7);
        assert_eq!(err, expected_string, "{err:?}");
        let err = assert_error::<StringParser>(b"1", 0, 1);
        assert_eq!(err, expected_string, "{err:?}");
    }
}

// --- Tests of the identifier parser ---

mod ident {
    use super::*;

    fn indices(ident: &SmtIdent) -> Vec<String> {
        ident
            .indices
            .iter()
            .map(|index| match index {
                SmtIndex::Numeral(n) => String::from_utf8(n.as_slice().to_vec()).unwrap(),
                SmtIndex::Symbol(s) => {
                    format!("'{}", String::from_utf8(s.as_slice().to_vec()).unwrap())
                }
            })
            .collect()
    }

    #[test]
    fn plain_symbol() {
        let ident = parse_all::<IdentParser>(b"x");
        assert_eq!(ident.name.as_slice(), b"x");
        assert!(ident.indices.is_empty());

        // a plain symbol is a single token; the rest is left for the caller
        let (ident, left) = run::<IdentParser>(b"x y").expect("valid");
        assert_eq!(ident.name.as_slice(), b"x");
        assert_eq!(left, 1);
    }

    #[test]
    fn indexed_with_numerals() {
        let ident = parse_all::<IdentParser>(b"(_ extract 7 0)");
        assert_eq!(ident.name.as_slice(), b"extract");
        assert_eq!(indices(&ident), ["7", "0"]);
    }

    #[test]
    fn indexed_with_symbols_and_numerals() {
        let ident = parse_all::<IdentParser>(b"(_ f a 1 b)");
        assert_eq!(ident.name.as_slice(), b"f");
        assert_eq!(indices(&ident), ["'a", "1", "'b"]);
    }

    #[test]
    fn indexed_over_lines() {
        let ident = parse_all::<IdentParser>(b"(_\n  bv42\n  8)");
        assert_eq!(ident.name.as_slice(), b"bv42");
        assert_eq!(indices(&ident), ["8"]);
    }

    #[test]
    fn continuations_after_open_paren_and_underscore() {
        // the callers that already consumed `(` or `( _` start in the corresponding state
        let ident = parse_all::<IdentParser>(b"(_ f 1)");
        let after_open = IdentParser::after_open_paren();
        let after_underscore = IdentParser::after_underscore();
        assert!(matches!(after_open, IdentParser::Open));
        assert!(matches!(after_underscore, IdentParser::AfterUnderscore));
        assert_eq!(ident.name.as_slice(), b"f");
    }

    #[test]
    fn errors() {
        let err = assert_error::<IdentParser>(b"1", 0, 1);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIdent),
            "{err:?}"
        );

        let err = assert_error::<IdentParser>(b")", 0, 1);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIdent),
            "{err:?}"
        );

        // after `(` only an underscore may follow
        let err = assert_error::<IdentParser>(b"(f 1)", 1, 2);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Reserved(
                    Reserved::Underscore
                )])
            ),
            "{err:?}"
        );

        // the name must be a symbol
        let err = assert_error::<IdentParser>(b"(_ 1 2)", 3, 4);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
            ),
            "{err:?}"
        );

        // at least one index is required
        let err = assert_error::<IdentParser>(b"(_ f)", 4, 5);
        assert!(
            matches!(err, CategoryParserErrorKind::EmptyIdentIndices),
            "{err:?}"
        );

        // indices are numerals or symbols only
        let err = assert_error::<IdentParser>(b"(_ f \"s\")", 5, 8);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIndexOrCloseParen),
            "{err:?}"
        );
        let err = assert_error::<IdentParser>(b"(_ f (a))", 5, 6);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIndexOrCloseParen),
            "{err:?}"
        );

        // EOF inside the indexed identifier
        let err = assert_error::<IdentParser>(b"(_ f 1", 6, 6);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIndexOrCloseParen),
            "{err:?}"
        );
    }
}

// --- Tests of the qualified-identifier parser ---

mod qualified_ident {
    use super::*;

    fn name(qualified_ident: &SmtQualifiedIdent<Printing>) -> &[u8] {
        qualified_ident.ident.name.as_slice()
    }

    #[test]
    fn simple_symbol() {
        let qi = parse_all::<QualifiedIdentParser<Printing>>(b"x");
        assert_eq!(name(&qi), b"x");
        assert!(qi.ident.indices.is_empty());
        assert_eq!(qi.sort, None);

        // a plain symbol is a single token; the rest is left for the caller
        let (qi, left) = run::<QualifiedIdentParser<Printing>>(b"x y").expect("valid");
        assert_eq!(name(&qi), b"x");
        assert_eq!(left, 1);
    }

    #[test]
    fn unqualified_indexed() {
        let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(_ extract 7 0)");
        assert_eq!(name(&qi), b"extract");
        assert_eq!(qi.ident.indices.len(), 2);
        assert_eq!(qi.sort, None);

        // the ident's own closing parenthesis ends the qualified ident;
        // the parser must not wait for another token after it
        let (qi, left) = run::<QualifiedIdentParser<Printing>>(b"(_ bv5 8) y").expect("valid");
        assert_eq!(name(&qi), b"bv5");
        assert_eq!(left, 1);
    }

    #[test]
    fn qualified_simple_ident() {
        let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(as x Bool)");
        assert_eq!(name(&qi), b"x");
        assert!(qi.ident.indices.is_empty());
        assert_eq!(qi.sort.as_deref(), Some("Bool"));
    }

    #[test]
    fn qualified_indexed_ident() {
        // the inner ident parser continues over multiple tokens
        let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(as (_ f 1) Bool)");
        assert_eq!(name(&qi), b"f");
        assert_eq!(qi.ident.indices.len(), 1);
        assert_eq!(qi.sort.as_deref(), Some("Bool"));
    }

    #[test]
    fn qualified_indexed_sort() {
        let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(as x (_ BitVec 8))");
        assert_eq!(name(&qi), b"x");
        assert_eq!(qi.sort.as_deref(), Some("(_ BitVec 8)"));
    }

    #[test]
    fn qualified_applied_sort() {
        // the sort parser handles applied sorts inside `as` as well
        let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(as x (Array Int Int))");
        assert_eq!(name(&qi), b"x");
        assert_eq!(qi.sort.as_deref(), Some("(Array Int Int)"));
    }

    #[test]
    fn entry_points() {
        // the callers that already consumed `(`, `( _` or `( as`
        // start in the corresponding state
        assert!(matches!(
            QualifiedIdentParser::<Printing>::new(),
            QualifiedIdentParser::Start
        ));
        assert!(matches!(
            QualifiedIdentParser::<Printing>::after_open_paren(),
            QualifiedIdentParser::Open
        ));
        assert!(matches!(
            QualifiedIdentParser::<Printing>::after_underscore(),
            QualifiedIdentParser::UnqualifiedIndexed(_)
        ));
        assert!(matches!(
            QualifiedIdentParser::<Printing>::after_as(),
            QualifiedIdentParser::QualifiedIdent(_)
        ));
    }

    #[test]
    fn errors() {
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"1", 0, 1);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIdent),
            "{err:?}"
        );

        // after `(` only `_` or `as` may follow
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"(f 1)", 1, 2);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[
                    TokenType::Reserved(Reserved::Underscore),
                    TokenType::Reserved(Reserved::As)
                ])
            ),
            "{err:?}"
        );

        // `as` must be followed by an identifier
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as)", 3, 4);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIdent),
            "{err:?}"
        );
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as 1 Bool)", 4, 5);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIdent),
            "{err:?}"
        );

        // ... and a sort
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as x)", 5, 6);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedSort),
            "{err:?}"
        );

        // ... and the closing parenthesis
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as x Bool z)", 11, 12);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );

        // EOF while waiting for the closing parenthesis
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as x Bool", 10, 10);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
    }
}

// --- Tests of the s-expression parser ---

mod s_expr {
    use super::*;

    type P = SExprParser<Printing>;

    #[test]
    fn atoms() {
        // special constants
        assert_eq!(parse_all::<P>(b"42"), "42");
        assert_eq!(parse_all::<P>(b"0.5"), "0.5");
        assert_eq!(parse_all::<P>(b"#xff"), "#xff");
        assert_eq!(parse_all::<P>(b"#b01"), "#b01");
        assert_eq!(parse_all::<P>(b"\"str\""), "\"str\"");
        // symbols
        assert_eq!(parse_all::<P>(b"sym"), "sym");
        assert_eq!(parse_all::<P>(b"|quoted sym|"), "quoted sym");
        // reserved words are ordinary atoms in an s-expression
        assert_eq!(parse_all::<P>(b"let"), "let");
        assert_eq!(parse_all::<P>(b"_"), "_");
        assert_eq!(parse_all::<P>(b"!"), "!");
        assert_eq!(parse_all::<P>(b"BINARY"), "BINARY");
        // keywords
        assert_eq!(parse_all::<P>(b":kw"), ":kw");
    }

    #[test]
    fn lists() {
        // the empty list is a valid s-expression
        assert_eq!(parse_all::<P>(b"()"), "()");
        assert_eq!(parse_all::<P>(b"(a b c)"), "(a b c)");
        // lists nest in any position
        assert_eq!(parse_all::<P>(b"((a) (b c) () 1)"), "((a) (b c) () 1)");
        // reserved words and keywords need no special treatment inside lists
        assert_eq!(parse_all::<P>(b"(let ((x 1)) x)"), "(let ((x 1)) x)");
        assert_eq!(
            parse_all::<P>(b"(as x (_ BitVec 8))"),
            "(as x (_ BitVec 8))"
        );
        assert_eq!(parse_all::<P>(b"(:status sat)"), "(:status sat)");
    }

    #[test]
    fn stops_after_root_s_expr() {
        let (s_expr, left) = run::<P>(b"a b").expect("valid");
        assert_eq!(s_expr, "a");
        assert_eq!(left, 1);

        let (s_expr, left) = run::<P>(b"(a b) c").expect("valid");
        assert_eq!(s_expr, "(a b)");
        assert_eq!(left, 1);

        // the leftover count is in tokens: `(` and `)`
        let (s_expr, left) = run::<P>(b"() ()").expect("valid");
        assert_eq!(s_expr, "()");
        assert_eq!(left, 2);
    }

    #[test]
    fn errors() {
        let expected_s_expr = CategoryParserErrorKind::ExpectedSExpr;

        // the only invalid tokens are the end of input...
        assert_eq!(assert_error::<P>(b"", 0, 0), expected_s_expr);
        assert_eq!(assert_error::<P>(b"(", 1, 1), expected_s_expr);
        assert_eq!(assert_error::<P>(b"(a", 2, 2), expected_s_expr);
        assert_eq!(assert_error::<P>(b"((a b)", 6, 6), expected_s_expr);
        // ...and a stray top-level closing parenthesis
        assert_eq!(assert_error::<P>(b")", 0, 1), expected_s_expr);
    }

    /// Handler that only counts s-expressions, so deep nesting does not build huge strings.
    #[derive(Default)]
    struct Counting {
        s_exprs: usize,
    }

    impl SmtHandler for Counting {
        type Error = Infallible;
        type SExpr = ();
        type Attribute = ();
        type Sort = ();
        type Term = ();

        fn handle_sort(&mut self, _sort: SmtSort<Self>) -> Result<(), Infallible> {
            Ok(())
        }
        fn handle_term(&mut self, _term: SmtTerm<Self>) -> Result<(), Infallible> {
            Ok(())
        }
        fn start_let(&mut self, _bindings: Vec<(SmtSymbol, ())>) -> Result<(), Infallible> {
            Ok(())
        }
        fn end_let(&mut self, _term: ()) -> Result<(), Infallible> {
            Ok(())
        }
        fn handle_s_expr(&mut self, _expr: SmtSExpr<Self>) -> Result<(), Infallible> {
            self.s_exprs += 1;
            Ok(())
        }
        fn handle_attribute(
            &mut self,
            _name: SmtKeyword,
            _value: Option<SmtAttributeValue<Self>>,
        ) -> Result<(), Infallible> {
            Ok(())
        }
    }

    #[test]
    fn deep_nesting_does_not_overflow_the_stack() {
        // ((( ... x ... ))) with a depth far beyond what recursion would survive
        const DEPTH: usize = 200_000;
        let mut input = Vec::with_capacity(2 * DEPTH + 1);
        input.extend(std::iter::repeat_n(b'(', DEPTH));
        input.push(b'x');
        input.extend(std::iter::repeat_n(b')', DEPTH));

        let mut handler = Counting::default();
        let ((), left) = run_with::<Counting, SExprParser<Counting>>(&mut handler, &input)
            .unwrap_or_else(|(kind, span)| panic!("{kind:?} at {span:?}"));
        assert_eq!(left, 0);
        // every list level plus the single atom
        assert_eq!(handler.s_exprs, DEPTH + 1);
    }
}

// --- Tests of the sort parser ---

mod sort {
    use super::*;

    #[test]
    fn simple_sort() {
        assert_eq!(parse_all::<SortParser<Printing>>(b"Bool"), "Bool");
        assert_eq!(parse_all::<SortParser<Printing>>(b"|my sort|"), "my sort");

        let (sort, left) = run::<SortParser<Printing>>(b"Int Bool").expect("valid");
        assert_eq!(sort, "Int");
        assert_eq!(left, 1);
    }

    #[test]
    fn indexed_sort() {
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"(_ BitVec 8)"),
            "(_ BitVec 8)"
        );
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"(_ FloatingPoint 8 24)"),
            "(_ FloatingPoint 8 24)"
        );
    }

    #[test]
    fn applied_sort() {
        assert_eq!(parse_all::<SortParser<Printing>>(b"(Set Int)"), "(Set Int)");
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"(Array Int Int)"),
            "(Array Int Int)"
        );

        // sorts nest in any argument position
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"(Array (Array Int Int) Int)"),
            "(Array (Array Int Int) Int)"
        );
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"(Array Int (Array Int Int))"),
            "(Array Int (Array Int Int))"
        );

        // the closing parenthesis ends the sort; the rest is left for the caller
        let (sort, left) = run::<SortParser<Printing>>(b"(Set Int) Bool").expect("valid");
        assert_eq!(sort, "(Set Int)");
        assert_eq!(left, 1);
    }

    #[test]
    fn applied_indexed_sort() {
        // indexed identifier as an argument sort
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"(Array (_ BitVec 8) Int)"),
            "(Array (_ BitVec 8) Int)"
        );

        // indexed identifier as the applied head
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"((_ FixedSizeList 4) Real)"),
            "((_ FixedSizeList 4) Real)"
        );

        // both at once
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"((_ Tuple 2) (_ BitVec 8) (Set Int))"),
            "((_ Tuple 2) (_ BitVec 8) (Set Int))"
        );
    }

    #[test]
    fn errors() {
        let expected_sort = CategoryParserErrorKind::ExpectedSort;
        assert_eq!(
            assert_error::<SortParser<Printing>>(b"1", 0, 1),
            expected_sort
        );
        assert_eq!(
            assert_error::<SortParser<Printing>>(b")", 0, 1),
            expected_sort
        );
        assert_eq!(
            assert_error::<SortParser<Printing>>(b"", 0, 0),
            expected_sort
        );

        // unterminated applied sort runs into the end of input
        assert_eq!(
            assert_error::<SortParser<Printing>>(b"(Array Int", 10, 10),
            expected_sort
        );

        // after `(`, only `_`, a symbol, or `(` may follow
        let err = assert_error::<SortParser<Printing>>(b"(as x Bool)", 1, 3);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedSortInner),
            "{err:?}"
        );
        let err = assert_error::<SortParser<Printing>>(b"(1 2)", 1, 2);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedSortInner),
            "{err:?}"
        );
        let err = assert_error::<SortParser<Printing>>(b"()", 1, 2);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedSortInner),
            "{err:?}"
        );

        // an applied identifier must be applied to at least one sort
        let err = assert_error::<SortParser<Printing>>(b"(Int)", 4, 5);
        assert!(
            matches!(err, CategoryParserErrorKind::EmptySortApplication),
            "{err:?}"
        );
        let err = assert_error::<SortParser<Printing>>(b"((_ BitVec 8))", 13, 14);
        assert!(
            matches!(err, CategoryParserErrorKind::EmptySortApplication),
            "{err:?}"
        );

        // a parenthesized applied head must be an indexed identifier
        let err = assert_error::<SortParser<Printing>>(b"((Array) Int)", 2, 7);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Reserved(
                    Reserved::Underscore
                )])
            ),
            "{err:?}"
        );

        // errors inside the indexed identifier are reported by the identifier parser
        let err = assert_error::<SortParser<Printing>>(b"(_ BitVec)", 9, 10);
        assert!(
            matches!(err, CategoryParserErrorKind::EmptyIdentIndices),
            "{err:?}"
        );
    }

    /// Handler that only counts sorts, so deep nesting does not build huge strings.
    #[derive(Default)]
    struct Counting {
        sorts: usize,
    }

    impl SmtHandler for Counting {
        type Error = Infallible;
        type SExpr = ();
        type Attribute = ();
        type Sort = ();
        type Term = ();

        fn handle_sort(&mut self, _sort: SmtSort<Self>) -> Result<(), Infallible> {
            self.sorts += 1;
            Ok(())
        }
        fn handle_term(&mut self, _term: SmtTerm<Self>) -> Result<(), Infallible> {
            Ok(())
        }
        fn start_let(&mut self, _bindings: Vec<(SmtSymbol, ())>) -> Result<(), Infallible> {
            Ok(())
        }
        fn end_let(&mut self, _term: ()) -> Result<(), Infallible> {
            Ok(())
        }
        fn handle_s_expr(&mut self, _expr: SmtSExpr<Self>) -> Result<(), Infallible> {
            Ok(())
        }
        fn handle_attribute(
            &mut self,
            _name: SmtKeyword,
            _value: Option<SmtAttributeValue<Self>>,
        ) -> Result<(), Infallible> {
            Ok(())
        }
    }

    #[test]
    fn deep_nesting_does_not_overflow_the_stack() {
        // (Array (Array ... Int ... Int) Int) with a depth far beyond what recursion would survive
        const DEPTH: usize = 200_000;
        let mut input = Vec::with_capacity(DEPTH * 12 + 3);
        for _ in 0..DEPTH {
            input.extend_from_slice(b"(Array ");
        }
        input.extend_from_slice(b"Int");
        for _ in 0..DEPTH {
            input.extend_from_slice(b" Int)");
        }

        let mut handler = Counting::default();
        let ((), left) = run_with::<Counting, SortParser<Counting>>(&mut handler, &input)
            .unwrap_or_else(|(kind, span)| panic!("{kind:?} at {span:?}"));
        assert_eq!(left, 0);
        // every applied `Array` sort plus every `Int` leaf
        assert_eq!(handler.sorts, 2 * DEPTH + 1);
    }
}

// --- Tests of the term parser ---

mod term {
    use super::*;

    #[test]
    fn special_constants() {
        assert_eq!(parse_all::<TermParser<Printing>>(b"42"), "42");
        assert_eq!(parse_all::<TermParser<Printing>>(b"0"), "0");
        assert_eq!(parse_all::<TermParser<Printing>>(b"3.25"), "3.25");
        assert_eq!(parse_all::<TermParser<Printing>>(b"#xdead"), "#xdead");
        assert_eq!(parse_all::<TermParser<Printing>>(b"#b101"), "#b101");
        assert_eq!(parse_all::<TermParser<Printing>>(b"\"str\""), "\"str\"");
    }

    #[test]
    fn identifiers() {
        assert_eq!(parse_all::<TermParser<Printing>>(b"x"), "x");
        assert_eq!(parse_all::<TermParser<Printing>>(b"|x y|"), "x y");
        assert_eq!(parse_all::<TermParser<Printing>>(b"(_ bv5 8)"), "(_ bv5 8)");
    }

    #[test]
    fn term_consumes_exactly_one_term() {
        let (term, left) = run::<TermParser<Printing>>(b"x y").expect("valid");
        assert_eq!(term, "x");
        assert_eq!(left, 1);

        let (term, left) = run::<TermParser<Printing>>(b"(f x) )").expect("valid");
        assert_eq!(term, "(f x)");
        assert_eq!(left, 1);
    }

    #[test]
    fn applications() {
        assert_eq!(parse_all::<TermParser<Printing>>(b"(f x)"), "(f x)");
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(f x 1 \"s\")"),
            "(f x 1 \"s\")"
        );
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(f (g x) (h y z))"),
            "(f (g x) (h y z))"
        );
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(+ (* 2 x) (- y))"),
            "(+ (* 2 x) (- y))"
        );
    }

    #[test]
    fn application_of_indexed_function() {
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"((_ extract 7 0) x)"),
            "((_ extract 7 0) x)"
        );
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(f ((_ zero_extend 8) y) (_ bv1 8))"),
            "(f ((_ zero_extend 8) y) (_ bv1 8))"
        );
    }

    #[test]
    fn qualified_identifiers() {
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(as x Bool)"),
            "(as x Bool)"
        );
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(as (_ bv5 8) (_ BitVec 8))"),
            "(as (_ bv5 8) (_ BitVec 8))"
        );
        // qualified identifier as an application argument
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(f (as x Bool) 1)"),
            "(f (as x Bool) 1)"
        );
    }

    #[test]
    fn application_of_qualified_function() {
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"((as f Bool) x)"),
            "((as f Bool) x)"
        );
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"((as (_ f 2) (_ BitVec 8)) x y)"),
            "((as (_ f 2) (_ BitVec 8)) x y)"
        );
    }

    #[test]
    fn empty_application_is_rejected() {
        // an application must have at least one argument
        let err = assert_error::<TermParser<Printing>>(b"(f)", 2, 3);
        assert!(
            matches!(err, CategoryParserErrorKind::EmptyTermApplication),
            "{err:?}"
        );
    }

    #[test]
    fn lets() {
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(let ((x 1)) x)"),
            "(let ((x 1)) x)"
        );
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(let ((x 1) (y (f 2))) (g x y))"),
            "(let ((x 1) (y (f 2))) (g x y))"
        );
        // nested lets in the bindings and in the body
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(let ((x (let ((z 0)) z))) (let ((y x)) (f x y)))"),
            "(let ((x (let ((z 0)) z))) (let ((y x)) (f x y)))"
        );
        // let as an application argument
        assert_eq!(
            parse_all::<TermParser<Printing>>(b"(f (let ((x 1)) x) 2)"),
            "(f (let ((x 1)) x) 2)"
        );
    }

    #[test]
    fn let_errors() {
        let err = assert_error::<TermParser<Printing>>(b"(let () x)", 6, 7);
        assert!(
            matches!(err, CategoryParserErrorKind::EmptyLetBindings),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"(let x x)", 5, 6);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
            ),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"(let (x) x)", 6, 7);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[
                    TokenType::ParenOpen,
                    TokenType::ParenClose
                ])
            ),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"(let ((1 x)) x)", 7, 8);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
            ),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"(let ((x 1 2)) x)", 11, 12);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"(let ((x 1)) x y)", 15, 16);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
    }

    #[test]
    fn errors() {
        let err = assert_error::<TermParser<Printing>>(b")", 0, 1);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedTerm),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b":kw", 0, 3);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedTerm),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"", 0, 0);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedTerm),
            "{err:?}"
        );

        // the operator position takes a symbol, a reserved binder, `_` or `(`
        let err = assert_error::<TermParser<Printing>>(b"(1 x)", 1, 2);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedOperator),
            "{err:?}"
        );

        let err = assert_error::<TermParser<Printing>>(b"()", 1, 2);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedOperator),
            "{err:?}"
        );

        // bad argument
        let err = assert_error::<TermParser<Printing>>(b"(f x :kw)", 5, 8);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedTerm),
            "{err:?}"
        );

        // EOF inside an application is a missing term
        let err = assert_error::<TermParser<Printing>>(b"(f x", 4, 4);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedTerm),
            "{err:?}"
        );

        // bad indexed identifier in a term
        let err = assert_error::<TermParser<Printing>>(b"(_ f)", 4, 5);
        assert!(
            matches!(err, CategoryParserErrorKind::EmptyIdentIndices),
            "{err:?}"
        );
    }

    /// Handler that only counts terms, so deep nesting does not build huge strings.
    #[derive(Default)]
    struct Counting {
        terms: usize,
    }

    impl SmtHandler for Counting {
        type Error = Infallible;
        type SExpr = ();
        type Attribute = ();
        type Sort = ();
        type Term = ();

        fn handle_sort(&mut self, _sort: SmtSort<Self>) -> Result<(), Infallible> {
            Ok(())
        }
        fn handle_term(&mut self, _term: SmtTerm<Self>) -> Result<(), Infallible> {
            self.terms += 1;
            Ok(())
        }
        fn start_let(&mut self, _bindings: Vec<(SmtSymbol, ())>) -> Result<(), Infallible> {
            Ok(())
        }
        fn end_let(&mut self, _term: ()) -> Result<(), Infallible> {
            Ok(())
        }
        fn handle_s_expr(&mut self, _expr: SmtSExpr<Self>) -> Result<(), Infallible> {
            Ok(())
        }
        fn handle_attribute(
            &mut self,
            _name: SmtKeyword,
            _value: Option<SmtAttributeValue<Self>>,
        ) -> Result<(), Infallible> {
            Ok(())
        }
    }

    #[test]
    fn deep_nesting_does_not_overflow_the_stack() {
        // (f (f (f ... x ...))) with a depth far beyond what recursion would survive
        const DEPTH: usize = 200_000;
        let mut input = Vec::with_capacity(DEPTH * 4);
        for _ in 0..DEPTH {
            input.extend_from_slice(b"(f ");
        }
        input.push(b'x');
        input.extend(std::iter::repeat_n(b')', DEPTH));

        let mut handler = Counting::default();
        let ((), left) = run_with::<Counting, TermParser<Counting>>(&mut handler, &input)
            .unwrap_or_else(|(kind, span)| panic!("{kind:?} at {span:?}"));
        assert_eq!(left, 0);
        // every application plus the innermost x
        assert_eq!(handler.terms, DEPTH + 1);
    }
}

// --- Tests of the closed attribute parser ---

mod attribute {
    use super::*;

    type P = ClosedAttributeParser<Printing>;

    #[test]
    fn attribute_without_value() {
        assert_eq!(parse_all::<P>(b":produce-models)"), ":produce-models");
    }

    #[test]
    fn attribute_with_value() {
        assert_eq!(parse_all::<P>(b":status sat)"), ":status sat");
        assert_eq!(parse_all::<P>(b":timeout 1000)"), ":timeout 1000");
        assert_eq!(parse_all::<P>(b":ratio 0.5)"), ":ratio 0.5");
        assert_eq!(parse_all::<P>(b":mask #xff)"), ":mask #xff");
        assert_eq!(parse_all::<P>(b":bits #b01)"), ":bits #b01");
        assert_eq!(parse_all::<P>(b":source \"me\")"), ":source \"me\"");
        assert_eq!(parse_all::<P>(b":name |a b|)"), ":name a b");
    }

    #[test]
    fn stops_after_closing_paren() {
        let (attribute, left) = run::<P>(b":status sat) x").expect("valid");
        assert_eq!(attribute, ":status sat");
        assert_eq!(left, 1);
    }

    #[test]
    fn errors() {
        let err = assert_error::<P>(b"status sat)", 0, 6);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword])
            ),
            "{err:?}"
        );

        let err = assert_error::<P>(b"", 0, 0);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword])
            ),
            "{err:?}"
        );

        // a keyword is not a valid value
        let err = assert_error::<P>(b":a :b)", 3, 5);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedAttribute),
            "{err:?}"
        );

        // only one value
        let err = assert_error::<P>(b":a 1 2)", 5, 6);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );

        // EOF after the value
        let err = assert_error::<P>(b":a 1", 4, 4);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
    }

    #[test]
    fn attribute_with_s_expr_list_value() {
        assert_eq!(parse_all::<P>(b":pattern ((f x)))"), ":pattern ((f x))");
        // the empty list is a valid value
        assert_eq!(parse_all::<P>(b":a ())"), ":a ()");
        // every atom kind, including reserved words, is a valid element
        assert_eq!(
            parse_all::<P>(b":a (1 0.5 #xff #b01 \"s\" sym :kw let _ ()))"),
            ":a (1 0.5 #xff #b01 \"s\" sym :kw let _ ())"
        );
        assert_eq!(
            parse_all::<P>(b":a ((nested (deeper ())) atom))"),
            ":a ((nested (deeper ())) atom)"
        );
    }

    #[test]
    fn s_expr_list_value_stops_after_closing_paren() {
        let (attribute, left) = run::<P>(b":a (x)) y").expect("valid");
        assert_eq!(attribute, ":a (x)");
        assert_eq!(left, 1);
    }

    #[test]
    fn s_expr_list_value_errors() {
        // EOF inside the value list
        let err = assert_error::<P>(b":a (1", 5, 5);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedSExpr),
            "{err:?}"
        );

        // EOF after the value list, before the enclosing closing parenthesis
        let err = assert_error::<P>(b":a ()", 5, 5);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );

        // a second value after the list
        let err = assert_error::<P>(b":a () x)", 6, 7);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
    }
}

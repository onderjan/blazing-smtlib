use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSpan, SmtSpecialConstant, SmtSymbol,
    read::parser::ParserError,
    token::{Token, TokenKind, TokenType},
};

mod attribute;
mod ident;
mod qualified_ident;
mod s_expr;
mod sort;
mod term;
mod token;

pub use {
    attribute::ClosedAttributeParser,
    ident::IdentParser,
    qualified_ident::QualifiedIdentParser,
    s_expr::SExprParser,
    sort::SortParser,
    term::TermParser,
    token::{CloseParenParser, KeywordParser, OpenParenParser, StringParser, SymbolParser},
};

pub trait CategoryParser<H: SmtHandler>: Default {
    type Result;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserError<H>>;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CategoryParserErrorKind {
    ExpectedToken(&'static [TokenType]),
    EmptyIdentIndices,
    EmptySortApplication,
    EmptyTermApplication,
    EmptyLetBindings,
    ExpectedIndexOrCloseParen,
    ExpectedOperator,
    ExpectedSExpr,
    ExpectedIdent,
    ExpectedSort,
    ExpectedSortInner,
    ExpectedTerm,
    ExpectedAttribute,
    ExpectedCommand,
    ExpectedCommandName,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CategoryParserError {
    kind: CategoryParserErrorKind,
    span: SmtSpan,
}

impl CategoryParserError {
    pub(crate) fn new(kind: CategoryParserErrorKind, span: SmtSpan) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &CategoryParserErrorKind {
        &self.kind
    }

    pub fn span(&self) -> SmtSpan {
        self.span
    }

    pub fn into_kind(self) -> CategoryParserErrorKind {
        self.kind
    }
}

pub enum PairParser<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> {
    First(P1),
    Second(P1::Result, P2),
}

impl<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> PairParser<H, P1, P2> {
    pub fn new() -> Self {
        Self::First(P1::default())
    }
}

impl<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> Default
    for PairParser<H, P1, P2>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> CategoryParser<H>
    for PairParser<H, P1, P2>
{
    type Result = (P1::Result, P2::Result);

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserError<H>> {
        let result = match self {
            PairParser::First(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => Self::First(parser),
                ControlFlow::Break(first) => Self::Second(first, P2::default()),
            },
            PairParser::Second(first, parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => Self::Second(first, parser),
                ControlFlow::Break(second) => return Ok(ControlFlow::Break((first, second))),
            },
        };
        Ok(ControlFlow::Continue(result))
    }
}

pub enum ClosedParser<H: SmtHandler, P: CategoryParser<H>> {
    Inner(P),
    BeforeClose(P::Result),
}

impl<H: SmtHandler, P: CategoryParser<H>> ClosedParser<H, P> {
    pub fn new() -> Self {
        Self::Inner(P::default())
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> Default for ClosedParser<H, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for ClosedParser<H, P> {
    type Result = P::Result;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserError<H>> {
        let span = token.span();
        let result = match self {
            Self::Inner(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => Self::Inner(parser),
                ControlFlow::Break(result) => Self::BeforeClose(result),
            },
            Self::BeforeClose(result) => {
                if matches!(token.kind(), TokenKind::ParenClose) {
                    return Ok(ControlFlow::Break(result));
                } else {
                    let kind = CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose]);
                    return Err(CategoryParserError::new(kind, span).into());
                }
            }
        };
        Ok(ControlFlow::Continue(result))
    }
}

pub enum OpenClosedParser<H: SmtHandler, P: CategoryParser<H>> {
    BeforeOpen,
    AfterOpen(ClosedParser<H, P>),
}

impl<H: SmtHandler, P: CategoryParser<H>> OpenClosedParser<H, P> {
    pub fn new() -> Self {
        Self::BeforeOpen
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> Default for OpenClosedParser<H, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for OpenClosedParser<H, P> {
    type Result = P::Result;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserError<H>> {
        let span = token.span();
        let result = match self {
            OpenClosedParser::BeforeOpen => {
                if matches!(token.kind(), TokenKind::ParenOpen) {
                    Self::AfterOpen(ClosedParser::default())
                } else {
                    return Err(ParserError::category_error(
                        CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen]),
                        span,
                    ));
                }
            }
            OpenClosedParser::AfterOpen(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => Self::AfterOpen(parser),
                ControlFlow::Break(result) => return Ok(ControlFlow::Break(result)),
            },
        };
        Ok(ControlFlow::Continue(result))
    }
}

pub enum MultipleParser<H: SmtHandler, P: CategoryParser<H>> {
    BeforeOpen,
    Normal {
        results: Vec<P::Result>,
        parser: Option<P>,
    },
}

impl<H: SmtHandler, P: CategoryParser<H>> MultipleParser<H, P> {
    pub fn new() -> Self {
        Self::BeforeOpen
    }

    pub fn after_open_paren() -> Self {
        Self::Normal {
            results: Vec::new(),
            parser: None,
        }
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> Default for MultipleParser<H, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for MultipleParser<H, P> {
    type Result = Vec<P::Result>;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Vec<P::Result>, Self>, ParserError<H>> {
        let span = token.span();
        match self {
            MultipleParser::BeforeOpen => {
                if matches!(token.kind(), TokenKind::ParenOpen) {
                    Ok(ControlFlow::Continue(Self::Normal {
                        results: Vec::new(),
                        parser: None,
                    }))
                } else {
                    Err(ParserError::category_error(
                        CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen]),
                        span,
                    ))
                }
            }
            MultipleParser::Normal {
                mut results,
                parser,
            } => {
                let parser = match parser {
                    Some(parser) => parser,
                    None => {
                        // close parenthesis ends processing
                        if matches!(token.kind(), TokenKind::ParenClose) {
                            return Ok(ControlFlow::Break(results));
                        } else {
                            P::default()
                        }
                    }
                };

                match parser.progress(handler, token)? {
                    ControlFlow::Continue(parser) => Ok(ControlFlow::Continue(Self::Normal {
                        results,
                        parser: Some(parser),
                    })),
                    ControlFlow::Break(result) => {
                        results.push(result);
                        Ok(ControlFlow::Continue(Self::Normal {
                            results,
                            parser: None,
                        }))
                    }
                }
            }
        }
    }
}

fn expect_close_paren<H: SmtHandler>(token: Token) -> Result<(), ParserError<H>> {
    let span = token.span();
    if matches!(token.kind(), TokenKind::ParenClose) {
        Ok(())
    } else {
        Err(ParserError::category_error(
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose]),
            span,
        ))
    }
}

fn expect_open_paren<H: SmtHandler>(token: Token) -> Result<(), ParserError<H>> {
    if matches!(token.kind(), TokenKind::ParenOpen) {
        Ok(())
    } else {
        Err(ParserError::category_error(
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen]),
            token.span(),
        ))
    }
}

fn expect_symbol<H: SmtHandler>(token: Token) -> Result<SmtSymbol, ParserError<H>> {
    let span = token.span();
    if let TokenKind::Symbol(symbol) = token.into_kind() {
        Ok(symbol)
    } else {
        Err(ParserError::category_error(
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol]),
            span,
        ))
    }
}

fn parse_special_constant(kind: TokenKind) -> Result<SmtSpecialConstant, TokenKind> {
    let constant = match kind {
        TokenKind::Numeral(value) => SmtSpecialConstant::Numeral(value),
        TokenKind::Decimal(decimal) => SmtSpecialConstant::Decimal(decimal),
        TokenKind::Hexadecimal(value) => SmtSpecialConstant::Hexadecimal(value),
        TokenKind::Binary(value) => SmtSpecialConstant::Binary(value),
        TokenKind::String(string) => SmtSpecialConstant::String(string),
        kind => return Err(kind),
    };
    Ok(constant)
}

#[cfg(test)]
pub(super) mod tests {
    use std::convert::Infallible;

    use super::*;
    use crate::{
        SmtAttributeValue, SmtIdent, SmtIndex, SmtKeyword, SmtQualifiedIdent, SmtSExpr, SmtSort,
        SmtSpecialConstant, SmtTerm,
        read::{lexer::Lexer, parser::ParserErrorKind},
    };

    // --- Test handler rendering everything it receives back into text ---

    /// Handler that renders every sort, term, s-expression and attribute
    /// it is given back into SMT-LIB text, so parser results can be checked as strings.
    #[derive(Default)]
    pub(in crate::read::parser::category) struct Printing {
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
            SmtSpecialConstant::Decimal(d) => format!(
                "{}.{}",
                text(d.whole_part.as_slice()),
                text(d.fractional_part.as_slice())
            ),
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
                SmtTerm::QualifiedIdent(qualified_ident) => {
                    render_qualified_ident(&qualified_ident)
                }
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

    /// Lexes the input and feeds it to a fresh parser `P` over a `Printing` handler.
    ///
    /// Returns the parser result and the number of tokens left unconsumed
    /// (not counting the end-of-file token), so tests can check where the parser stopped.
    /// Panics if the parser did not finish before the end of the input.
    pub(in crate::read::parser::category) fn run<P: CategoryParser<Printing>>(
        input: &[u8],
    ) -> Result<(P::Result, usize), CategoryParserError> {
        run_with::<P>(&mut Printing::default(), input)
    }

    pub(in crate::read::parser::category) fn run_with<P: CategoryParser<Printing>>(
        handler: &mut Printing,
        input: &[u8],
    ) -> Result<(P::Result, usize), CategoryParserError> {
        let mut tokens = Lexer::lex_all(input)
            .expect("test input must lex")
            .into_iter();
        let mut parser = P::default();
        for token in tokens.by_ref() {
            match parser.progress(handler, token) {
                Ok(ControlFlow::Continue(next)) => parser = next,
                Ok(ControlFlow::Break(result)) => {
                    let left = tokens
                        .filter(|token| !matches!(token.kind(), TokenKind::EndOfFile))
                        .count();
                    return Ok((result, left));
                }
                Err(err) => {
                    let span = err.span();
                    return Err(match err.into_kind() {
                        ParserErrorKind::Category(kind) => CategoryParserError::new(kind, span),
                        // the `Printing` handler never fails
                        ParserErrorKind::Handler(err) => match err {},
                    });
                }
            }
        }
        panic!(
            "parser did not finish before the end of input {:?}",
            text(input)
        );
    }

    /// Runs the parser, requires success with no unconsumed tokens, and returns the result.
    #[track_caller]
    pub(in crate::read::parser::category) fn parse_all<P: CategoryParser<Printing>>(
        input: &[u8],
    ) -> P::Result {
        match run::<P>(input) {
            Ok((result, 0)) => result,
            Ok((_, left)) => panic!("{left} tokens left unconsumed in {:?}", text(input)),
            Err(err) => panic!("unexpected error {err:?} in {:?}", text(input)),
        }
    }

    /// Runs the parser, requires a parser error, checks the byte span the error carries,
    /// and returns its kind so that the caller can inspect the variant.
    #[track_caller]
    pub(in crate::read::parser::category) fn assert_error<P: CategoryParser<Printing>>(
        input: &[u8],
        start: u64,
        end: u64,
    ) -> CategoryParserErrorKind {
        match run::<P>(input) {
            Ok(_) => panic!("expected a parser error in {:?}, got Ok", text(input)),
            Err(err) => {
                let span = err.span();
                assert_eq!(
                    (span.start().offset(), span.end().offset()),
                    (start, end),
                    "error span mismatch (start, end) as byte offsets for {err:?} in {:?}",
                    text(input)
                );
                err.into_kind()
            }
        }
    }

    // --- Tests of the generic combinators ---

    // TODO: fix tests
    /*

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

    // TODO: replace test
    /*
    #[test]
    fn close_paren_parser() {
        parse_all::<CloseParenParser>(b")");

        let err = assert_error::<CloseParenParser>(b"x", 0, 1);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
    }
    */

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
    */
}

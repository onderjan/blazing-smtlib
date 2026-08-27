use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSymbol,
    read::parser::{ParserError, ParserOrHandlerError},
    token::{Token, TokenKind},
};

pub mod attribute;
pub mod ident;
pub mod sort;
pub mod term;

pub trait CategoryParser<H: SmtHandler>
where
    Self: std::marker::Sized,
{
    type Result;

    fn init() -> Self;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserOrHandlerError<H>>;
}

pub enum PairParser<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> {
    First(P1),
    Second(P1::Result, P2),
}

impl<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> CategoryParser<H>
    for PairParser<H, P1, P2>
{
    type Result = (P1::Result, P2::Result);

    fn init() -> Self {
        Self::First(P1::init())
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserOrHandlerError<H>> {
        let result = match self {
            PairParser::First(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => Self::First(parser),
                ControlFlow::Break(first) => Self::Second(first, P2::init()),
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

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for ClosedParser<H, P> {
    type Result = P::Result;

    fn init() -> Self {
        Self::Inner(P::init())
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserOrHandlerError<H>> {
        let result = match self {
            Self::Inner(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => Self::Inner(parser),
                ControlFlow::Break(result) => Self::BeforeClose(result),
            },
            Self::BeforeClose(result) => {
                if matches!(token.kind(), TokenKind::ParenClose) {
                    return Ok(ControlFlow::Break(result));
                } else {
                    return Err(ParserError::ExpectedToken(TokenKind::ParenClose).into());
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

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for OpenClosedParser<H, P> {
    type Result = P::Result;

    fn init() -> Self {
        Self::BeforeOpen
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserOrHandlerError<H>> {
        let result = match self {
            OpenClosedParser::BeforeOpen => {
                if matches!(token.kind(), TokenKind::ParenOpen) {
                    Self::AfterOpen(ClosedParser::init())
                } else {
                    return Err(ParserError::ExpectedToken(TokenKind::ParenOpen).into());
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

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for MultipleParser<H, P> {
    type Result = Vec<P::Result>;

    fn init() -> Self {
        Self::BeforeOpen
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Vec<P::Result>, Self>, ParserOrHandlerError<H>> {
        match self {
            MultipleParser::BeforeOpen => {
                if matches!(token.kind(), TokenKind::ParenOpen) {
                    Ok(ControlFlow::Continue(Self::Normal {
                        results: Vec::new(),
                        parser: None,
                    }))
                } else {
                    Err(ParserError::ExpectedToken(TokenKind::ParenOpen).into())
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
                            P::init()
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

/*
impl<H: SmtHandler, P: CategoryParser<H>> MultipleParser<H, P> {
    pub fn after_open_paren() -> Self {
        Self::Normal {
            results: Vec::new(),
            parser: None,
        }
    }
}*/

pub struct SymbolParser;

impl<H: SmtHandler> CategoryParser<H> for SymbolParser {
    type Result = SmtSymbol;

    fn init() -> Self {
        Self
    }

    fn progress(
        self,
        _handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result, Self>, ParserOrHandlerError<H>> {
        if let TokenKind::Symbol(symbol) = token.into_kind() {
            Ok(ControlFlow::Break(symbol))
        } else {
            Err(ParserError::ExpectedSymbol.into())
        }
    }
}

pub struct CloseParenParser;

impl<H: SmtHandler> CategoryParser<H> for CloseParenParser {
    type Result = ();

    fn init() -> Self {
        Self
    }

    fn progress(
        self,
        _handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<(), Self>, ParserOrHandlerError<H>> {
        if matches!(token.kind(), TokenKind::ParenClose) {
            Ok(ControlFlow::Break(()))
        } else {
            Err(ParserError::ExpectedToken(TokenKind::ParenClose).into())
        }
    }
}

fn expect_close_parenthesis<H: SmtHandler>(token: Token) -> Result<(), ParserOrHandlerError<H>> {
    if matches!(token.kind(), TokenKind::ParenClose) {
        Ok(())
    } else {
        Err(ParserError::ExpectedToken(TokenKind::ParenClose).into())
    }
}

#[cfg(test)]
pub(super) mod tests {
    use std::convert::Infallible;

    use super::*;
    use crate::{
        SmtAttributeValue, SmtIdent, SmtIndex, SmtKeyword, SmtQualifiedIdent, SmtSExpr, SmtSort,
        SmtSpecialConstant, SmtTerm, TokenSpan, read::lexer::Lexer,
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

        fn handle_sort(&mut self, sort: SmtSort) -> Result<String, Infallible> {
            Ok(match sort {
                SmtSort::Ident(ident) => render_ident(&ident),
            })
        }

        fn handle_term(&mut self, term: SmtTerm<Self>) -> Result<String, Infallible> {
            Ok(match term {
                SmtTerm::SpecialConstant(constant) => render_constant(&constant),
                SmtTerm::QualifiedIdent(SmtQualifiedIdent::Ident(ident)) => render_ident(&ident),
                SmtTerm::Application(application) => {
                    let SmtQualifiedIdent::Ident(function) = application.function;
                    let mut items = vec![render_ident(&function)];
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

        fn handle_s_expr(&mut self, expr: SmtSExpr<String>) -> Result<String, Infallible> {
            Ok(match expr {
                SmtSExpr::SpecialConstant(constant) => render_constant(&constant),
                SmtSExpr::Symbol(symbol) => text(symbol.as_slice()),
                SmtSExpr::Reserved(reserved) => format!("{reserved:?}"),
                SmtSExpr::Keyword(keyword) => format!(":{}", text(keyword.as_slice())),
                SmtSExpr::Exprs(exprs) => render_list(&exprs),
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
                Some(SmtAttributeValue::Exprs(exprs)) => format!("{name} {}", render_list(&exprs)),
            })
        }
    }

    // --- Driver ---

    /// Error returned by `run`: the parser error and the byte span of the token it was raised on.
    pub(in crate::read::parser::category) type RunError = (ParserError, TokenSpan);

    /// Lexes the input and feeds it to a fresh parser `P` over a `Printing` handler.
    ///
    /// Returns the parser result and the number of tokens left unconsumed
    /// (not counting the end-of-file token), so tests can check where the parser stopped.
    /// Panics if the parser did not finish before the end of the input.
    pub(in crate::read::parser::category) fn run<P: CategoryParser<Printing>>(
        input: &[u8],
    ) -> Result<(P::Result, usize), RunError> {
        run_with::<P>(&mut Printing::default(), input)
    }

    pub(in crate::read::parser::category) fn run_with<P: CategoryParser<Printing>>(
        handler: &mut Printing,
        input: &[u8],
    ) -> Result<(P::Result, usize), RunError> {
        let mut tokens = Lexer::lex_all(input)
            .expect("test input must lex")
            .into_iter();
        let mut parser = P::init();
        for token in tokens.by_ref() {
            let span = token.span();
            match parser.progress(handler, token) {
                Ok(ControlFlow::Continue(next)) => parser = next,
                Ok(ControlFlow::Break(result)) => {
                    let left = tokens
                        .filter(|token| !matches!(token.kind(), TokenKind::EndOfFile))
                        .count();
                    return Ok((result, left));
                }
                Err(ParserOrHandlerError::ParserError(err)) => return Err((err, span)),
                Err(ParserOrHandlerError::HandlerError(err)) => match err {},
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
            Err((err, span)) => panic!("unexpected error {err:?} at {span:?} in {:?}", text(input)),
        }
    }

    /// Runs the parser, requires a parser error, checks the byte span of the offending token,
    /// and returns the error so that the caller can inspect the variant.
    #[track_caller]
    pub(in crate::read::parser::category) fn assert_error<P: CategoryParser<Printing>>(
        input: &[u8],
        start: u64,
        end: u64,
    ) -> ParserError {
        match run::<P>(input) {
            Ok(_) => panic!("expected a parser error in {:?}, got Ok", text(input)),
            Err((err, span)) => {
                assert_eq!(
                    (span.start(), span.end()),
                    (start, end),
                    "token span mismatch (start, end) as byte offsets for {err:?} in {:?}",
                    text(input)
                );
                err
            }
        }
    }

    // --- Tests of the generic combinators ---

    #[test]
    fn symbol_parser() {
        let symbol = parse_all::<SymbolParser>(b"abc");
        assert_eq!(symbol.as_slice(), b"abc");
        let symbol = parse_all::<SymbolParser>(b"|quoted symbol|");
        assert_eq!(symbol.as_slice(), b"quoted symbol");

        let err = assert_error::<SymbolParser>(b"1", 0, 1);
        assert!(matches!(err, ParserError::ExpectedSymbol), "{err:?}");
        let err = assert_error::<SymbolParser>(b"(", 0, 1);
        assert!(matches!(err, ParserError::ExpectedSymbol), "{err:?}");
        // reserved words are not symbols
        let err = assert_error::<SymbolParser>(b"let", 0, 3);
        assert!(matches!(err, ParserError::ExpectedSymbol), "{err:?}");
    }

    #[test]
    fn symbol_parser_consumes_one_token() {
        let (symbol, left) = run::<SymbolParser>(b"a b c").expect("valid");
        assert_eq!(symbol.as_slice(), b"a");
        assert_eq!(left, 2);
    }

    #[test]
    fn close_paren_parser() {
        parse_all::<CloseParenParser>(b")");

        let err = assert_error::<CloseParenParser>(b"x", 0, 1);
        assert!(
            matches!(err, ParserError::ExpectedToken(TokenKind::ParenClose)),
            "{err:?}"
        );
    }

    #[test]
    fn pair_parser() {
        let (first, second) = parse_all::<PairParser<Printing, SymbolParser, SymbolParser>>(b"a b");
        assert_eq!(first.as_slice(), b"a");
        assert_eq!(second.as_slice(), b"b");

        // the error of the second element points at its token
        let err = assert_error::<PairParser<Printing, SymbolParser, SymbolParser>>(b"a 1", 2, 3);
        assert!(matches!(err, ParserError::ExpectedSymbol), "{err:?}");
    }

    #[test]
    fn closed_parser() {
        let symbol = parse_all::<ClosedParser<Printing, SymbolParser>>(b"a)");
        assert_eq!(symbol.as_slice(), b"a");

        let err = assert_error::<ClosedParser<Printing, SymbolParser>>(b"a b", 2, 3);
        assert!(
            matches!(err, ParserError::ExpectedToken(TokenKind::ParenClose)),
            "{err:?}"
        );
        // EOF instead of the closing parenthesis
        let err = assert_error::<ClosedParser<Printing, SymbolParser>>(b"a", 1, 1);
        assert!(
            matches!(err, ParserError::ExpectedToken(TokenKind::ParenClose)),
            "{err:?}"
        );
    }

    #[test]
    fn open_closed_parser() {
        let symbol = parse_all::<OpenClosedParser<Printing, SymbolParser>>(b"(a)");
        assert_eq!(symbol.as_slice(), b"a");

        let err = assert_error::<OpenClosedParser<Printing, SymbolParser>>(b"a)", 0, 1);
        assert!(
            matches!(err, ParserError::ExpectedToken(TokenKind::ParenOpen)),
            "{err:?}"
        );
        let err = assert_error::<OpenClosedParser<Printing, SymbolParser>>(b"(a", 2, 2);
        assert!(
            matches!(err, ParserError::ExpectedToken(TokenKind::ParenClose)),
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
            matches!(err, ParserError::ExpectedToken(TokenKind::ParenOpen)),
            "{err:?}"
        );
        // the element parser's error is reported for a bad element
        let err = assert_error::<MultipleParser<Printing, SymbolParser>>(b"(a 1)", 3, 4);
        assert!(matches!(err, ParserError::ExpectedSymbol), "{err:?}");
        // unclosed list ends at EOF inside the element parser
        let err = assert_error::<MultipleParser<Printing, SymbolParser>>(b"(a", 2, 2);
        assert!(matches!(err, ParserError::ExpectedSymbol), "{err:?}");
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
        assert!(matches!(err, ParserError::ExpectedSymbol), "{err:?}");
    }
}

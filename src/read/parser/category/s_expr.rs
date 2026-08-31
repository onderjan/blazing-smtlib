use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSExpr, SmtSpan,
    read::parser::{
        ParserError,
        category::{CategoryParser, CategoryParserErrorKind, handle_err, parse_special_constant},
    },
    token::{Token, TokenKind},
};

struct SExprLevel<H: SmtHandler> {
    s_exprs: Vec<H::SExpr>,
}

pub struct SExprParser<H: SmtHandler> {
    levels: Vec<SExprLevel<H>>,
}

impl<H: SmtHandler> SExprParser<H> {
    pub fn new() -> Self {
        Self { levels: Vec::new() }
    }
}

impl<H: SmtHandler> Default for SExprParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for SExprParser<H> {
    type Result = H::SExpr;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::SExpr, Self>, ParserError<H>> {
        let (mut levels, s_expr) = match self.progress_last_level(handler, token)? {
            ControlFlow::Continue(parser) => return Ok(ControlFlow::Continue(parser)),
            ControlFlow::Break((levels, s_expr)) => (levels, s_expr),
        };
        if let Some(last_level) = levels.last_mut() {
            // we need to append to the last level
            last_level.s_exprs.push(s_expr);
            Ok(ControlFlow::Continue(Self { levels }))
        } else {
            // this is the root level, we are done
            Ok(ControlFlow::Break(s_expr))
        }
    }
}

type SExprProgressOk<H, P> = ControlFlow<(Vec<SExprLevel<H>>, <H as SmtHandler>::SExpr), P>;

impl<H: SmtHandler> SExprParser<H> {
    fn progress_last_level(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<SExprProgressOk<H, Self>, ParserError<H>> {
        let mut levels = self.levels;

        let span = token.span();
        let kind = token.into_kind();
        let kind = match parse_special_constant(kind) {
            Ok(special_constant) => {
                let s_expr = SmtSExpr::SpecialConstant(special_constant);
                return Self::break_with(handler, levels, s_expr, span);
            }
            Err(kind) => kind,
        };

        match kind {
            TokenKind::Symbol(symbol) => {
                let s_expr = SmtSExpr::Symbol(symbol);
                Self::break_with(handler, levels, s_expr, span)
            }
            TokenKind::Reserved(reserved) => {
                let s_expr = SmtSExpr::Reserved(reserved);
                Self::break_with(handler, levels, s_expr, span)
            }
            TokenKind::Keyword(keyword) => {
                let s_expr = SmtSExpr::Keyword(keyword);
                Self::break_with(handler, levels, s_expr, span)
            }
            TokenKind::ParenOpen => {
                // add new level
                levels.push(SExprLevel {
                    s_exprs: Vec::new(),
                });
                Ok(ControlFlow::Continue(Self { levels }))
            }
            kind => {
                if matches!(kind, TokenKind::ParenClose) {
                    // closes the last level if it exists
                    if let Some(last_level) = levels.pop() {
                        // empty s_expr is allowed
                        let s_expr = SmtSExpr::SExprs(last_level.s_exprs);
                        return Self::break_with(handler, levels, s_expr, span);
                    }
                }

                let kind = CategoryParserErrorKind::ExpectedSExpr;
                Err(ParserError::category_error(kind, span))
            }
        }
    }

    fn break_with(
        handler: &mut H,
        levels: Vec<SExprLevel<H>>,
        s_expr: SmtSExpr<H>,
        span: SmtSpan,
    ) -> Result<SExprProgressOk<H, Self>, ParserError<H>> {
        let s_expr = handle_err(handler.handle_s_expr(s_expr), span)?;
        Ok(ControlFlow::Break((levels, s_expr)))
    }
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use super::*;
    use crate::{
        SmtAttributeValue, SmtKeyword, SmtSort, SmtSymbol, SmtTerm,
        read::{
            lexer::Lexer,
            parser::{
                ParserErrorKind,
                category::tests::{Printing, assert_error, parse_all, run},
            },
        },
    };

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
        let mut parser = SExprParser::<Counting>::default();
        let mut finished = false;
        for token in Lexer::lex_all(&input).expect("valid input") {
            match parser.progress(&mut handler, token) {
                Ok(ControlFlow::Continue(next)) => parser = next,
                Ok(ControlFlow::Break(())) => {
                    finished = true;
                    break;
                }
                Err(err) => {
                    let span = err.span();
                    match err.into_kind() {
                        ParserErrorKind::Category(kind) => panic!("{kind:?} at {span:?}"),
                        // the `Counting` handler never fails
                        ParserErrorKind::Handler(err) => match err {},
                    }
                }
            }
        }
        assert!(finished);
        // every list level plus the single atom
        assert_eq!(handler.s_exprs, DEPTH + 1);
    }
}

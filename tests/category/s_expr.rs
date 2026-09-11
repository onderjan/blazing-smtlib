//! Tests of the s-expression parser.

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
    let expected_s_expr = CategoryErrorKind::ExpectedSExpr;

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

    fn handle_sort(&mut self, _sort: SmtSort<'_, Self>) -> Result<(), Infallible> {
        Ok(())
    }
    fn handle_term(&mut self, _term: SmtTerm<'_, Self>) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_let(&mut self, _bindings: SmtBindings<'_, Self>) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_let(&mut self, _term: ()) -> Result<(), Infallible> {
        Ok(())
    }
    fn handle_s_expr(&mut self, _expr: SmtSExpr<'_, Self>) -> Result<(), Infallible> {
        self.s_exprs += 1;
        Ok(())
    }
    fn handle_attribute(
        &mut self,
        _name: SmtKeywordView<'_>,
        _value: Option<SmtAttributeValue<'_, Self>>,
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn annotate_term(
        &mut self,
        _term: (),
        _attributes: SmtAttributes<'_, Self>,
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _name: SmtSymbolView<'_>,
        _sort: (),
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_quantifier(&mut self, _term: ()) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_lambda(&mut self, _name: SmtSymbolView<'_>, _sort: ()) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_lambda(&mut self, _term: ()) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_match(&mut self, _scrutinee: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_match_case(&mut self, _pattern: SmtPattern) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_match_case(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_match(&mut self) -> Result<Self::Term, Self::Error> {
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

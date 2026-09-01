//! Tests of the term parser.

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
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen, TokenType::ParenClose])
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

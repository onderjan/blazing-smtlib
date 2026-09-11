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
        matches!(err, CategoryErrorKind::EmptyTermApplication),
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
        matches!(err, CategoryErrorKind::EmptyLetBindings),
        "{err:?}"
    );

    let err = assert_error::<TermParser<Printing>>(b"(let x x)", 5, 6);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[TokenType::ParenOpen])
        ),
        "{err:?}"
    );

    let err = assert_error::<TermParser<Printing>>(b"(let (x) x)", 6, 7);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[TokenType::ParenOpen, TokenType::ParenClose])
        ),
        "{err:?}"
    );

    let err = assert_error::<TermParser<Printing>>(b"(let ((1 x)) x)", 7, 8);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );

    let err = assert_error::<TermParser<Printing>>(b"(let ((x 1 2)) x)", 11, 12);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );

    let err = assert_error::<TermParser<Printing>>(b"(let ((x 1)) x y)", 15, 16);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
}

#[test]
fn errors() {
    let err = assert_error::<TermParser<Printing>>(b")", 0, 1);
    assert!(
        matches!(err, CategoryErrorKind::ExpectedTerm),
        "{err:?}"
    );

    let err = assert_error::<TermParser<Printing>>(b":kw", 0, 3);
    assert!(
        matches!(err, CategoryErrorKind::ExpectedTerm),
        "{err:?}"
    );

    let err = assert_error::<TermParser<Printing>>(b"", 0, 0);
    assert!(
        matches!(err, CategoryErrorKind::ExpectedTerm),
        "{err:?}"
    );

    // the operator position takes a symbol, a reserved binder, `_` or `(`
    let err = assert_error::<TermParser<Printing>>(b"(1 x)", 1, 2);
    assert!(
        matches!(err, CategoryErrorKind::ExpectedOperator),
        "{err:?}"
    );

    let err = assert_error::<TermParser<Printing>>(b"()", 1, 2);
    assert!(
        matches!(err, CategoryErrorKind::ExpectedOperator),
        "{err:?}"
    );

    // bad argument
    let err = assert_error::<TermParser<Printing>>(b"(f x :kw)", 5, 8);
    assert!(
        matches!(err, CategoryErrorKind::ExpectedTerm),
        "{err:?}"
    );

    // EOF inside an application is a missing term
    let err = assert_error::<TermParser<Printing>>(b"(f x", 4, 4);
    assert!(
        matches!(err, CategoryErrorKind::ExpectedTerm),
        "{err:?}"
    );

    // bad indexed identifier in a term
    let err = assert_error::<TermParser<Printing>>(b"(_ f)", 4, 5);
    assert!(
        matches!(err, CategoryErrorKind::EmptyIdentIndices),
        "{err:?}"
    );
}

#[test]
fn annotations() {
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(! x :named foo)"),
        "(! x :named foo)"
    );
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(! (f x 1) :a)"),
        "(! (f x 1) :a)"
    );
    // multiple attributes, name-only and valued
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(! x :a :b 2 :c)"),
        "(! x :a :b 2 :c)"
    );
    // keywords inside an s-expression value do not start a new attribute
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(! x :a (p :k q) :b)"),
        "(! x :a (p :k q) :b)"
    );
}

#[test]
fn annotations_nest_and_compose() {
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(! (! x :a) :b)"),
        "(! (! x :a) :b)"
    );
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(f (! x :a) y)"),
        "(f (! x :a) y)"
    );
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(let ((a (! 1 :k))) (! a :l))"),
        "(let ((a (! 1 :k))) (! a :l))"
    );
}

#[test]
fn annotation_consumes_exactly_one_term() {
    let (term, left) = run::<TermParser<Printing>>(b"(! x :a) y").expect("valid");
    assert_eq!(term, "(! x :a)");
    assert_eq!(left, 1);
}

#[test]
fn annotated_term_parser_is_reusable() {
    let (first, second) = parse_two::<TermParser<Printing>>(b"(! x :a) (! y :b 2)");
    assert_eq!(first, "(! x :a)");
    assert_eq!(second, "(! y :b 2)");
}

#[test]
fn quantifiers() {
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(forall ((x Int)) x)"),
        "(forall ((x Int)) x)"
    );
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(exists ((x Int)) (f x 1))"),
        "(exists ((x Int)) (f x 1))"
    );
    // multiple variables desugar into nested single-variable binders
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(forall ((x Int) (y Bool)) (f x y))"),
        "(forall ((x Int)) (forall ((y Bool)) (f x y)))"
    );
    // complex sorts flow through the sort parser
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(forall ((a (Array Int Int))) (select a 0))"),
        "(forall ((a (Array Int Int))) (select a 0))"
    );
}

#[test]
fn multi_variable_binder_is_equivalent_to_nested_binders() {
    // the handler cannot distinguish the sugared multi-variable form
    // from the explicitly nested form; this is the contract a streaming
    // rewrite of the variable handling must preserve
    let sugared = parse_all::<TermParser<Printing>>(b"(exists ((x Int) (y Bool) (z Real)) x)");
    let nested = parse_all::<TermParser<Printing>>(
        b"(exists ((x Int)) (exists ((y Bool)) (exists ((z Real)) x)))",
    );
    assert_eq!(sugared, nested);
    assert_eq!(
        sugared,
        "(exists ((x Int)) (exists ((y Bool)) (exists ((z Real)) x)))"
    );
}

#[test]
fn lambdas() {
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(lambda ((x Int)) x)"),
        "(lambda ((x Int)) x)"
    );
    // multiple variables desugar by currying
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(lambda ((x Int) (y Int)) (+ x y))"),
        "(lambda ((x Int)) (lambda ((y Int)) (+ x y)))"
    );
}

#[test]
fn binders_nest_and_compose() {
    // quantifiers of both kinds and lambda nested within each other
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(forall ((x Int)) (exists ((y Int)) (f x y)))"),
        "(forall ((x Int)) (exists ((y Int)) (f x y)))"
    );
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(forall ((x Int)) (lambda ((y Int)) y))"),
        "(forall ((x Int)) (lambda ((y Int)) y))"
    );
    // binder as an application argument
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(f (forall ((x Int)) x) y)"),
        "(f (forall ((x Int)) x) y)"
    );
    // let inside a binder and binder inside a let
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(forall ((x Int)) (let ((a x)) a))"),
        "(forall ((x Int)) (let ((a x)) a))"
    );
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(let ((a 1)) (exists ((x Int)) (f a x)))"),
        "(let ((a 1)) (exists ((x Int)) (f a x)))"
    );
    // annotated binder body
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(forall ((x Int)) (! x :qid q))"),
        "(forall ((x Int)) (! x :qid q))"
    );
    // annotated binder term
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(! (forall ((x Int)) x) :named n)"),
        "(! (forall ((x Int)) x) :named n)"
    );
}

#[test]
fn binder_consumes_exactly_one_term() {
    let (term, left) = run::<TermParser<Printing>>(b"(forall ((x Int)) x) y").expect("valid");
    assert_eq!(term, "(forall ((x Int)) x)");
    assert_eq!(left, 1);
}

#[test]
fn binder_term_parser_is_reusable() {
    let (first, second) =
        parse_two::<TermParser<Printing>>(b"(forall ((x Int)) x) (lambda ((y Bool)) y)");
    assert_eq!(first, "(forall ((x Int)) x)");
    assert_eq!(second, "(lambda ((y Bool)) y)");

    // reuse with the same binder kind exercises the self-reset contract
    // of the variable-list machinery
    let (first, second) =
        parse_two::<TermParser<Printing>>(b"(forall ((x Int)) x) (forall ((y Bool) (z Real)) y)");
    assert_eq!(first, "(forall ((x Int)) x)");
    assert_eq!(second, "(forall ((y Bool)) (forall ((z Real)) y))");
}

#[test]
fn binder_errors() {
    // a quantifier must bind at least one variable
    let err = assert_error::<TermParser<Printing>>(b"(forall () x)", 9, 10);
    assert!(
        matches!(err, CategoryErrorKind::EmptyQuantifierBindings),
        "{err:?}"
    );
    let err = assert_error::<TermParser<Printing>>(b"(exists () x)", 9, 10);
    assert!(
        matches!(err, CategoryErrorKind::EmptyQuantifierBindings),
        "{err:?}"
    );

    // so must a lambda, with its own error kind
    let err = assert_error::<TermParser<Printing>>(b"(lambda () x)", 9, 10);
    assert!(
        matches!(err, CategoryErrorKind::EmptyLambdaBindings),
        "{err:?}"
    );

    // the variable list must be parenthesized
    let err = assert_error::<TermParser<Printing>>(b"(forall x x)", 8, 9);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[TokenType::ParenOpen])
        ),
        "{err:?}"
    );

    // a variable must have a sort
    let err = assert_error::<TermParser<Printing>>(b"(forall ((x)) x)", 11, 12);
    assert!(
        matches!(err, CategoryErrorKind::ExpectedSort),
        "{err:?}"
    );

    // EOF before the body is a missing term
    let err = assert_error::<TermParser<Printing>>(b"(forall ((x Int))", 17, 17);
    assert!(
        matches!(err, CategoryErrorKind::ExpectedTerm),
        "{err:?}"
    );
}

#[test]
fn annotation_errors() {
    // an annotation must contain at least one attribute
    let err = assert_error::<TermParser<Printing>>(b"(! x)", 4, 5);
    assert!(
        matches!(err, CategoryErrorKind::EmptyAnnotation),
        "{err:?}"
    );

    // an annotation must contain a term
    let err = assert_error::<TermParser<Printing>>(b"(!)", 2, 3);
    assert!(
        matches!(err, CategoryErrorKind::ExpectedTerm),
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

    fn handle_sort(&mut self, _sort: SmtSort<'_, Self>) -> Result<(), Infallible> {
        Ok(())
    }
    fn handle_term(&mut self, _term: SmtTerm<'_, Self>) -> Result<(), Infallible> {
        self.terms += 1;
        Ok(())
    }
    fn start_let(&mut self, _bindings: SmtBindings<'_, Self>) -> Result<(), Infallible> {
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
    fn annotate_term(&mut self, _term: (), _attributes: Vec<()>) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _name: SmtSymbol,
        _sort: (),
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_quantifier(&mut self, _term: ()) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_lambda(&mut self, _name: SmtSymbol, _sort: ()) -> Result<(), Infallible> {
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

#[test]
fn deep_annotation_nesting_does_not_overflow_the_stack() {
    // (! (! ... x ... :a) :a) with a depth far beyond what recursion would survive
    const DEPTH: usize = 200_000;
    let mut input = Vec::with_capacity(DEPTH * 7 + 1);
    for _ in 0..DEPTH {
        input.extend_from_slice(b"(! ");
    }
    input.push(b'x');
    for _ in 0..DEPTH {
        input.extend_from_slice(b" :a)");
    }

    let mut handler = Counting::default();
    let ((), left) = run_with::<Counting, TermParser<Counting>>(&mut handler, &input)
        .unwrap_or_else(|(kind, span)| panic!("{kind:?} at {span:?}"));
    assert_eq!(left, 0);
    // annotations produce no terms of their own, only the innermost x does
    assert_eq!(handler.terms, 1);
}

#[test]
fn deep_binder_nesting_does_not_overflow_the_stack() {
    // (forall ((x Int)) (forall ((x Int)) ... x ...)) with a depth
    // far beyond what recursion would survive
    const DEPTH: usize = 200_000;
    let mut input = Vec::with_capacity(DEPTH * 19 + 1);
    for _ in 0..DEPTH {
        input.extend_from_slice(b"(forall ((x Int)) ");
    }
    input.push(b'x');
    input.extend(std::iter::repeat_n(b')', DEPTH));

    let mut handler = Counting::default();
    let ((), left) = run_with::<Counting, TermParser<Counting>>(&mut handler, &input)
        .unwrap_or_else(|(kind, span)| panic!("{kind:?} at {span:?}"));
    assert_eq!(left, 0);
    // binders produce no terms of their own, only the innermost x does
    assert_eq!(handler.terms, 1);
}

#[test]
fn binder_with_many_variables_does_not_overflow_the_stack() {
    // a single binder with a huge variable list exercises the desugared
    // start/end calls: one pair per variable, iteratively
    const VARIABLES: usize = 100_000;
    let mut input = Vec::with_capacity(VARIABLES * 8 + 12);
    input.extend_from_slice(b"(exists (");
    for _ in 0..VARIABLES {
        input.extend_from_slice(b"(x Int)");
    }
    input.extend_from_slice(b") x)");

    let mut handler = Counting::default();
    let ((), left) = run_with::<Counting, TermParser<Counting>>(&mut handler, &input)
        .unwrap_or_else(|(kind, span)| panic!("{kind:?} at {span:?}"));
    assert_eq!(left, 0);
    assert_eq!(handler.terms, 1);
}

#[test]
fn matches() {
    // the standard's list append and length examples
    assert_eq!(
        parse_all::<TermParser<Printing>>(
            b"(match l ((nil l2) ((cons h t) (cons h (append t l2)))))"
        ),
        "(match l ((nil l2) ((cons h t) (cons h (append t l2)))))"
    );
    assert_eq!(
        parse_all::<TermParser<Printing>>(
            b"(match l (((cons h t) (cons h (append t l2))) (_ l2)))"
        ),
        "(match l (((cons h t) (cons h (append t l2))) (_ l2)))"
    );
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(match l ((nil 0) ((cons _ t) (+ 1 (length t)))))"),
        "(match l ((nil 0) ((cons _ t) (+ 1 (length t)))))"
    );
    // a single case with a symbol pattern
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(match x ((y y)))"),
        "(match x ((y y)))"
    );
    // wildcards in every position
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(match x (((c _ _) 1) (_ 2)))"),
        "(match x (((c _ _) 1) (_ 2)))"
    );
    // a compound scrutinee
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(match (f x y) ((z z)))"),
        "(match (f x y) ((z z)))"
    );
}

#[test]
fn matches_nest_and_compose() {
    // match in the scrutinee and in a case body
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(match (match x ((a 1))) ((b 2)))"),
        "(match (match x ((a 1))) ((b 2)))"
    );
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(match x ((a (match y ((b 1))))))"),
        "(match x ((a (match y ((b 1))))))"
    );
    // match as an application argument
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(f (match x ((a 1))) 2)"),
        "(f (match x ((a 1))) 2)"
    );
    // match inside a let and let inside a match
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(let ((v (match x ((a 1))))) v)"),
        "(let ((v (match x ((a 1))))) v)"
    );
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(match x ((a (let ((v 1)) v))))"),
        "(match x ((a (let ((v 1)) v))))"
    );
    // match inside a binder
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(forall ((x Int)) (match x ((a 1))))"),
        "(forall ((x Int)) (match x ((a 1))))"
    );
    // annotated match and annotated case body
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(! (match x ((a 1))) :named n)"),
        "(! (match x ((a 1))) :named n)"
    );
    assert_eq!(
        parse_all::<TermParser<Printing>>(b"(match x ((a (! 1 :named n))))"),
        "(match x ((a (! 1 :named n))))"
    );
}

#[test]
fn match_consumes_exactly_one_term() {
    let (term, left) = run::<TermParser<Printing>>(b"(match x ((a 1))) y").expect("valid");
    assert_eq!(term, "(match x ((a 1)))");
    assert_eq!(left, 1);
}

#[test]
fn match_term_parser_is_reusable() {
    let (first, second) =
        parse_two::<TermParser<Printing>>(b"(match x ((a 1))) (match y (((c v) v) (_ 0)))");
    assert_eq!(first, "(match x ((a 1)))");
    assert_eq!(second, "(match y (((c v) v) (_ 0)))");

    // a constructor pattern followed by a simple one exercises
    // the self-reset contract of the pattern machinery
    let (first, second) =
        parse_two::<TermParser<Printing>>(b"(match x (((c v) v))) (match y ((_ 0)))");
    assert_eq!(first, "(match x (((c v) v)))");
    assert_eq!(second, "(match y ((_ 0)))");
}

#[test]
fn match_errors() {
    // the scrutinee is required
    let err = assert_error::<TermParser<Printing>>(b"(match)", 6, 7);
    assert!(
        matches!(err, CategoryErrorKind::ExpectedTerm),
        "{err:?}"
    );
    // the case list is required
    let err = assert_error::<TermParser<Printing>>(b"(match x)", 8, 9);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[TokenType::ParenOpen])
        ),
        "{err:?}"
    );
    // at least one case is required
    let err = assert_error::<TermParser<Printing>>(b"(match x ())", 10, 11);
    assert!(
        matches!(err, CategoryErrorKind::EmptyMatchCases),
        "{err:?}"
    );
    // each case is parenthesized
    let err = assert_error::<TermParser<Printing>>(b"(match x (x))", 10, 11);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[TokenType::ParenOpen, TokenType::ParenClose])
        ),
        "{err:?}"
    );
    // a pattern starts with a symbol, a wildcard, or a constructor application
    let err = assert_error::<TermParser<Printing>>(b"(match x ((1 y)))", 11, 12);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[
                TokenType::Symbol,
                TokenType::Reserved(Reserved::Underscore),
                TokenType::ParenOpen
            ])
        ),
        "{err:?}"
    );
    // a constructor application has at least one argument
    let err = assert_error::<TermParser<Printing>>(b"(match x (((c) y)))", 13, 14);
    assert!(
        matches!(err, CategoryErrorKind::EmptyPatternArguments),
        "{err:?}"
    );
    // the constructor is a symbol, not a wildcard or a constant
    let err = assert_error::<TermParser<Printing>>(b"(match x (((1 y) z)))", 12, 13);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
    let err = assert_error::<TermParser<Printing>>(b"(match x (((_ y) z)))", 12, 13);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
    // the arguments are symbols or wildcards, not nested patterns or constants
    let err = assert_error::<TermParser<Printing>>(b"(match x (((c 1) z)))", 14, 15);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[
                TokenType::Symbol,
                TokenType::Reserved(Reserved::Underscore)
            ])
        ),
        "{err:?}"
    );
    let err = assert_error::<TermParser<Printing>>(b"(match x (((c (d y)) z)))", 14, 15);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[
                TokenType::Symbol,
                TokenType::Reserved(Reserved::Underscore)
            ])
        ),
        "{err:?}"
    );
    // the case body is required
    let err = assert_error::<TermParser<Printing>>(b"(match x ((y)))", 12, 13);
    assert!(
        matches!(err, CategoryErrorKind::ExpectedTerm),
        "{err:?}"
    );
    // exactly one case body
    let err = assert_error::<TermParser<Printing>>(b"(match x ((y 1 2)))", 15, 16);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
    // nothing follows the case list
    let err = assert_error::<TermParser<Printing>>(b"(match x ((y 1)) z)", 17, 18);
    assert!(
        matches!(
            err,
            CategoryErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
}

#[test]
fn deep_match_nesting_does_not_overflow_the_stack() {
    // (match x ((_ (match x ((_ ... y ...)))))) with a depth far beyond
    // what recursion would survive
    const DEPTH: usize = 200_000;
    let mut input = Vec::with_capacity(DEPTH * 16);
    for _ in 0..DEPTH {
        input.extend_from_slice(b"(match x ((_ ");
    }
    input.push(b'y');
    for _ in 0..DEPTH {
        input.extend_from_slice(b")))");
    }

    let mut handler = Counting::default();
    let ((), left) = run_with::<Counting, TermParser<Counting>>(&mut handler, &input)
        .unwrap_or_else(|(kind, span)| panic!("{kind:?} at {span:?}"));
    assert_eq!(left, 0);
    // every scrutinee plus the innermost y
    assert_eq!(handler.terms, DEPTH + 1);
}

/// How a handler consumes the arguments handed over with an application.
#[derive(Clone, Copy, Debug)]
enum Consumption {
    /// Only inspects the arguments in place.
    Inspect,
    /// Moves the first argument out and leaves the rest.
    TakeFirst,
    /// Moves every argument out.
    TakeAll,
}

/// Handler that records every application with the arguments it was handed,
/// consuming them in the given way, so the arguments of an enclosing
/// application must not depend on how the inner ones were consumed.
struct Consuming {
    consumption: Consumption,
    applications: Vec<(String, Vec<String>)>,
}

impl SmtHandler for Consuming {
    type Error = Infallible;
    type SExpr = ();
    type Attribute = ();
    type Sort = ();
    type Term = String;

    fn handle_sort(&mut self, _sort: SmtSort<'_, Self>) -> Result<(), Infallible> {
        Ok(())
    }
    fn handle_term(&mut self, term: SmtTerm<'_, Self>) -> Result<String, Infallible> {
        Ok(match term {
            SmtTerm::SpecialConstant(constant) => render_constant(&constant),
            SmtTerm::QualifiedIdent(qualified_ident) => render_ident(&qualified_ident.ident),
            SmtTerm::Application(application) => {
                let function = render_ident(&application.function.ident);
                let args: Vec<String> = application.args.iter().cloned().collect();
                let rendered = format!("({} {})", function, args.join(" "));
                self.applications.push((function, args));
                match self.consumption {
                    Consumption::Inspect => {}
                    Consumption::TakeFirst => {
                        application.args.into_iter().next();
                    }
                    Consumption::TakeAll => {
                        application.args.into_iter().for_each(drop);
                    }
                }
                rendered
            }
        })
    }
    fn start_let(&mut self, _bindings: SmtBindings<'_, Self>) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_let(&mut self, term: String) -> Result<String, Infallible> {
        Ok(term)
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
    fn annotate_term(&mut self, term: String, _attributes: Vec<()>) -> Result<String, Infallible> {
        Ok(term)
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _name: SmtSymbol,
        _sort: (),
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_quantifier(&mut self, term: String) -> Result<String, Infallible> {
        Ok(term)
    }
    fn start_lambda(&mut self, _name: SmtSymbol, _sort: ()) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_lambda(&mut self, term: String) -> Result<String, Infallible> {
        Ok(term)
    }
    fn start_match(&mut self, _scrutinee: String) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_match_case(&mut self, _pattern: SmtPattern) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_match_case(&mut self, _term: String) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_match(&mut self) -> Result<String, Infallible> {
        Ok(String::from("<match>"))
    }
}

#[test]
fn application_arguments_are_handed_over_regardless_of_consumption() {
    // the arguments handed over with an inner application must not leak
    // into the enclosing one, whether the handler moved them out or not
    for consumption in [
        Consumption::Inspect,
        Consumption::TakeFirst,
        Consumption::TakeAll,
    ] {
        let mut handler = Consuming {
            consumption,
            applications: Vec::new(),
        };
        let (term, left) = run_with::<Consuming, TermParser<Consuming>>(
            &mut handler,
            b"(f (g x) (h a b c) y)",
        )
        .unwrap_or_else(|(kind, span)| panic!("{kind:?} at {span:?} with {consumption:?}"));
        assert_eq!(left, 0, "with {consumption:?}");
        assert_eq!(term, "(f (g x) (h a b c) y)", "with {consumption:?}");
        let expected: Vec<(String, Vec<String>)> = vec![
            ("g".into(), vec!["x".into()]),
            ("h".into(), vec!["a".into(), "b".into(), "c".into()]),
            (
                "f".into(),
                vec!["(g x)".into(), "(h a b c)".into(), "y".into()],
            ),
        ];
        assert_eq!(handler.applications, expected, "with {consumption:?}");
    }
}

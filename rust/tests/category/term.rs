//! Tests of the term parser.

use super::*;
use blazing_smtlib::{
    parser::{SmtNonEmptyList, SmtSyntaxExpected},
    token::{SmtGeneralReserved, SmtReserved, SmtTokenCategory},
};

#[test]
fn special_constants() {
    assert_eq!(parse_all::<TermParser>(b"42"), "42");
    assert_eq!(parse_all::<TermParser>(b"0"), "0");
    assert_eq!(parse_all::<TermParser>(b"3.25"), "3.25");
    assert_eq!(parse_all::<TermParser>(b"#xdead"), "#xdead");
    assert_eq!(parse_all::<TermParser>(b"#b101"), "#b101");
    assert_eq!(parse_all::<TermParser>(b"\"str\""), "\"str\"");
}

#[test]
fn identifiers() {
    assert_eq!(parse_all::<TermParser>(b"x"), "x");
    assert_eq!(parse_all::<TermParser>(b"|x y|"), "|x y|");
    assert_eq!(parse_all::<TermParser>(b"(_ bv5 8)"), "(_ bv5 8)");
}

#[test]
fn term_consumes_exactly_one_term() {
    let (term, left) = run::<TermParser>(b"x y").expect("valid");
    assert_eq!(term, "x");
    assert_eq!(left, 1);

    let (term, left) = run::<TermParser>(b"(f x) )").expect("valid");
    assert_eq!(term, "(f x)");
    assert_eq!(left, 1);
}

#[test]
fn applications() {
    assert_eq!(parse_all::<TermParser>(b"(f x)"), "(f x)");
    assert_eq!(parse_all::<TermParser>(b"(f x 1 \"s\")"), "(f x 1 \"s\")");
    assert_eq!(
        parse_all::<TermParser>(b"(f (g x) (h y z))"),
        "(f (g x) (h y z))"
    );
    assert_eq!(
        parse_all::<TermParser>(b"(+ (* 2 x) (- y))"),
        "(+ (* 2 x) (- y))"
    );
}

#[test]
fn application_of_indexed_function() {
    assert_eq!(
        parse_all::<TermParser>(b"((_ extract 7 0) x)"),
        "((_ extract 7 0) x)"
    );
    assert_eq!(
        parse_all::<TermParser>(b"(f ((_ zero_extend 8) y) (_ bv1 8))"),
        "(f ((_ zero_extend 8) y) (_ bv1 8))"
    );
}

#[test]
fn qualified_identifiers() {
    assert_eq!(parse_all::<TermParser>(b"(as x Bool)"), "(as x Bool)");
    assert_eq!(
        parse_all::<TermParser>(b"(as (_ bv5 8) (_ BitVec 8))"),
        "(as (_ bv5 8) (_ BitVec 8))"
    );
    // qualified identifier as an application argument
    assert_eq!(
        parse_all::<TermParser>(b"(f (as x Bool) 1)"),
        "(f (as x Bool) 1)"
    );
}

#[test]
fn application_of_qualified_function() {
    assert_eq!(
        parse_all::<TermParser>(b"((as f Bool) x)"),
        "((as f Bool) x)"
    );
    assert_eq!(
        parse_all::<TermParser>(b"((as (_ f 2) (_ BitVec 8)) x y)"),
        "((as (_ f 2) (_ BitVec 8)) x y)"
    );
}

#[test]
fn empty_application_is_rejected() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // an application must have at least one argument
    let err = assert_error::<TermParser>(b"(f)", 2, 3);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Empty(SmtNonEmptyList::TermApplication)
        ),
        "{err:?}"
    );
}

#[test]
fn lets() {
    assert_eq!(
        parse_all::<TermParser>(b"(let ((x 1)) x)"),
        "(let ((x 1)) x)"
    );
    assert_eq!(
        parse_all::<TermParser>(b"(let ((x 1) (y (f 2))) (g x y))"),
        "(let ((x 1) (y (f 2))) (g x y))"
    );
    // nested lets in the bindings and in the body
    assert_eq!(
        parse_all::<TermParser>(b"(let ((x (let ((z 0)) z))) (let ((y x)) (f x y)))"),
        "(let ((x (let ((z 0)) z))) (let ((y x)) (f x y)))"
    );
    // let as an application argument
    assert_eq!(
        parse_all::<TermParser>(b"(f (let ((x 1)) x) 2)"),
        "(f (let ((x 1)) x) 2)"
    );
}

#[test]
fn let_errors() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    let err = assert_error::<TermParser>(b"(let () x)", 6, 7);
    assert!(
        matches!(err, SmtSyntaxErrorKind::Empty(SmtNonEmptyList::LetBindings)),
        "{err:?}"
    );

    let err = assert_error::<TermParser>(b"(let x x)", 5, 6);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(SmtTokenCategory::ParenOpen)])
        ),
        "{err:?}"
    );

    let err = assert_error::<TermParser>(b"(let (x) x)", 6, 7);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[
                SmtSyntaxExpected::Token(SmtTokenCategory::ParenOpen),
                SmtSyntaxExpected::Token(SmtTokenCategory::ParenClose)
            ])
        ),
        "{err:?}"
    );

    let err = assert_error::<TermParser>(b"(let ((1 x)) x)", 7, 8);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Symbol])
        ),
        "{err:?}"
    );

    let err = assert_error::<TermParser>(b"(let ((x 1 2)) x)", 11, 12);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(SmtTokenCategory::ParenClose)])
        ),
        "{err:?}"
    );

    let err = assert_error::<TermParser>(b"(let ((x 1)) x y)", 15, 16);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(SmtTokenCategory::ParenClose)])
        ),
        "{err:?}"
    );
}

#[test]
fn errors() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    let err = assert_error::<TermParser>(b")", 0, 1);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Term])
        ),
        "{err:?}"
    );

    let err = assert_error::<TermParser>(b":kw", 0, 3);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Term])
        ),
        "{err:?}"
    );

    let err = assert_error::<TermParser>(b"", 0, 0);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Term])
        ),
        "{err:?}"
    );

    // the operator position takes a symbol, a reserved binder, `_` or `(`
    let err = assert_error::<TermParser>(b"(1 x)", 1, 2);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Operator])
        ),
        "{err:?}"
    );

    let err = assert_error::<TermParser>(b"()", 1, 2);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Operator])
        ),
        "{err:?}"
    );

    // bad argument
    let err = assert_error::<TermParser>(b"(f x :kw)", 5, 8);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Term])
        ),
        "{err:?}"
    );

    // EOF inside an application is a missing term
    let err = assert_error::<TermParser>(b"(f x", 4, 4);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Term])
        ),
        "{err:?}"
    );

    // bad indexed identifier in a term
    let err = assert_error::<TermParser>(b"(_ f)", 4, 5);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Empty(SmtNonEmptyList::IdentIndices)
        ),
        "{err:?}"
    );
}

#[test]
fn annotations() {
    assert_eq!(
        parse_all::<TermParser>(b"(! x :named foo)"),
        "(! x :named foo)"
    );
    assert_eq!(parse_all::<TermParser>(b"(! (f x 1) :a)"), "(! (f x 1) :a)");
    // multiple attributes, name-only and valued
    assert_eq!(
        parse_all::<TermParser>(b"(! x :a :b 2 :c)"),
        "(! x :a :b 2 :c)"
    );
    // keywords inside an s-expression value do not start a new attribute
    assert_eq!(
        parse_all::<TermParser>(b"(! x :a (p :k q) :b)"),
        "(! x :a (p :k q) :b)"
    );
}

#[test]
fn annotations_nest_and_compose() {
    assert_eq!(
        parse_all::<TermParser>(b"(! (! x :a) :b)"),
        "(! (! x :a) :b)"
    );
    assert_eq!(parse_all::<TermParser>(b"(f (! x :a) y)"), "(f (! x :a) y)");
    assert_eq!(
        parse_all::<TermParser>(b"(let ((a (! 1 :k))) (! a :l))"),
        "(let ((a (! 1 :k))) (! a :l))"
    );
}

#[test]
fn annotation_consumes_exactly_one_term() {
    let (term, left) = run::<TermParser>(b"(! x :a) y").expect("valid");
    assert_eq!(term, "(! x :a)");
    assert_eq!(left, 1);
}

#[test]
fn annotated_term_parser_is_reusable() {
    let (first, second) = parse_two::<TermParser>(b"(! x :a) (! y :b 2)");
    assert_eq!(first, "(! x :a)");
    assert_eq!(second, "(! y :b 2)");
}

#[test]
fn quantifiers() {
    assert_eq!(
        parse_all::<TermParser>(b"(forall ((x Int)) x)"),
        "(forall ((x Int)) x)"
    );
    assert_eq!(
        parse_all::<TermParser>(b"(exists ((x Int)) (f x 1))"),
        "(exists ((x Int)) (f x 1))"
    );
    // multiple variables are handed over together, in one start
    assert_eq!(
        parse_all::<TermParser>(b"(forall ((x Int) (y Bool)) (f x y))"),
        "(forall ((x Int) (y Bool)) (f x y))"
    );
    // complex sorts flow through the sort parser
    assert_eq!(
        parse_all::<TermParser>(b"(forall ((a (Array Int Int))) (select a 0))"),
        "(forall ((a (Array Int Int))) (select a 0))"
    );
}

#[test]
fn binder_variables_are_handed_over_as_one_group() {
    // the variables of one binder arrive in one start, in order, so the
    // handler can tell a binder of several variables from nested binders
    let grouped = parse_all::<TermParser>(b"(exists ((x Int) (y Bool) (z Real)) x)");
    let nested =
        parse_all::<TermParser>(b"(exists ((x Int)) (exists ((y Bool)) (exists ((z Real)) x)))");
    assert_eq!(grouped, "(exists ((x Int) (y Bool) (z Real)) x)");
    assert_eq!(
        nested,
        "(exists ((x Int)) (exists ((y Bool)) (exists ((z Real)) x)))"
    );
    // a repeated name is handed over again, in its place
    assert_eq!(
        parse_all::<TermParser>(b"(lambda ((x Int) (x Bool)) x)"),
        "(lambda ((x Int) (x Bool)) x)"
    );
}

#[test]
fn lambdas() {
    assert_eq!(
        parse_all::<TermParser>(b"(lambda ((x Int)) x)"),
        "(lambda ((x Int)) x)"
    );
    // multiple variables are handed over together, in one start
    assert_eq!(
        parse_all::<TermParser>(b"(lambda ((x Int) (y Int)) (+ x y))"),
        "(lambda ((x Int) (y Int)) (+ x y))"
    );
}

#[test]
fn binders_nest_and_compose() {
    // quantifiers of both kinds and lambda nested within each other
    assert_eq!(
        parse_all::<TermParser>(b"(forall ((x Int)) (exists ((y Int)) (f x y)))"),
        "(forall ((x Int)) (exists ((y Int)) (f x y)))"
    );
    assert_eq!(
        parse_all::<TermParser>(b"(forall ((x Int)) (lambda ((y Int)) y))"),
        "(forall ((x Int)) (lambda ((y Int)) y))"
    );
    // binder as an application argument
    assert_eq!(
        parse_all::<TermParser>(b"(f (forall ((x Int)) x) y)"),
        "(f (forall ((x Int)) x) y)"
    );
    // let inside a binder and binder inside a let
    assert_eq!(
        parse_all::<TermParser>(b"(forall ((x Int)) (let ((a x)) a))"),
        "(forall ((x Int)) (let ((a x)) a))"
    );
    assert_eq!(
        parse_all::<TermParser>(b"(let ((a 1)) (exists ((x Int)) (f a x)))"),
        "(let ((a 1)) (exists ((x Int)) (f a x)))"
    );
    // annotated binder body
    assert_eq!(
        parse_all::<TermParser>(b"(forall ((x Int)) (! x :qid q))"),
        "(forall ((x Int)) (! x :qid q))"
    );
    // annotated binder term
    assert_eq!(
        parse_all::<TermParser>(b"(! (forall ((x Int)) x) :named n)"),
        "(! (forall ((x Int)) x) :named n)"
    );
}

#[test]
fn binder_consumes_exactly_one_term() {
    let (term, left) = run::<TermParser>(b"(forall ((x Int)) x) y").expect("valid");
    assert_eq!(term, "(forall ((x Int)) x)");
    assert_eq!(left, 1);
}

#[test]
fn binder_term_parser_is_reusable() {
    let (first, second) = parse_two::<TermParser>(b"(forall ((x Int)) x) (lambda ((y Bool)) y)");
    assert_eq!(first, "(forall ((x Int)) x)");
    assert_eq!(second, "(lambda ((y Bool)) y)");

    // reuse with the same binder kind exercises the self-reset contract
    // of the variable-list machinery
    let (first, second) =
        parse_two::<TermParser>(b"(forall ((x Int)) x) (forall ((y Bool) (z Real)) y)");
    assert_eq!(first, "(forall ((x Int)) x)");
    assert_eq!(second, "(forall ((y Bool) (z Real)) y)");
}

#[test]
fn binder_errors() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // a quantifier must bind at least one variable
    let err = assert_error::<TermParser>(b"(forall () x)", 9, 10);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Empty(SmtNonEmptyList::QuantifierBindings)
        ),
        "{err:?}"
    );
    let err = assert_error::<TermParser>(b"(exists () x)", 9, 10);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Empty(SmtNonEmptyList::QuantifierBindings)
        ),
        "{err:?}"
    );

    // so must a lambda, with its own error kind
    let err = assert_error::<TermParser>(b"(lambda () x)", 9, 10);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Empty(SmtNonEmptyList::LambdaBindings)
        ),
        "{err:?}"
    );

    // the variable list must be parenthesized
    let err = assert_error::<TermParser>(b"(forall x x)", 8, 9);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(SmtTokenCategory::ParenOpen)])
        ),
        "{err:?}"
    );

    // a variable must have a sort
    let err = assert_error::<TermParser>(b"(forall ((x)) x)", 11, 12);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Sort])
        ),
        "{err:?}"
    );

    // EOF before the body is a missing term
    let err = assert_error::<TermParser>(b"(forall ((x Int))", 17, 17);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Term])
        ),
        "{err:?}"
    );
}

#[test]
fn annotation_errors() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // an annotation must contain at least one attribute
    let err = assert_error::<TermParser>(b"(! x)", 4, 5);
    assert!(
        matches!(err, SmtSyntaxErrorKind::Empty(SmtNonEmptyList::Annotation)),
        "{err:?}"
    );

    // an annotation must contain a term
    let err = assert_error::<TermParser>(b"(!)", 2, 3);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Term])
        ),
        "{err:?}"
    );
}

/// Handler that only counts terms, so deep nesting does not build huge strings.
#[derive(Default)]
struct Counting {
    terms: usize,
}

impl Handler for Counting {
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
        self.terms += 1;
        Ok(())
    }
    fn start_let(&mut self, _bindings: Bindings<Self::Term>) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_let(&mut self, _scope: (), _body: ()) -> Result<(), Infallible> {
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
        Ok(())
    }
    fn annotate_term(
        &mut self,
        _term: (),
        _attributes: Vec<Self::Attribute>,
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _vars: SortedVars<Self::Sort>,
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _scope: (),
        _body: (),
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_lambda(&mut self, _vars: SortedVars<Self::Sort>) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_lambda(&mut self, _scope: (), _body: ()) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_match(&mut self, _scrutinee: &Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_match_case(
        &mut self,
        _scrutinee: &Self::Term,
        _pattern: SmtPatternBuf,
    ) -> Result<Self::Scope, Self::Error> {
        Ok(())
    }
    fn end_match_case(
        &mut self,
        _scope: Self::Scope,
        _scrutinee: &Self::Term,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error> {
        Ok(body)
    }
    fn end_match(
        &mut self,
        _scrutinee: Self::Term,
        _cases: MatchCases<Self::Term>,
    ) -> Result<Self::Term, Self::Error> {
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
    let ((), left) = run_with::<Counting, TermParser>(&mut handler, &input)
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
    let ((), left) = run_with::<Counting, TermParser>(&mut handler, &input)
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
    let ((), left) = run_with::<Counting, TermParser>(&mut handler, &input)
        .unwrap_or_else(|(kind, span)| panic!("{kind:?} at {span:?}"));
    assert_eq!(left, 0);
    // binders produce no terms of their own, only the innermost x does
    assert_eq!(handler.terms, 1);
}

#[test]
fn binder_with_many_variables_does_not_overflow_the_stack() {
    // a single binder with a huge variable list is stored in the arena
    // and handed over in one start
    const VARIABLES: usize = 100_000;
    let mut input = Vec::with_capacity(VARIABLES * 8 + 12);
    input.extend_from_slice(b"(exists (");
    for _ in 0..VARIABLES {
        input.extend_from_slice(b"(x Int)");
    }
    input.extend_from_slice(b") x)");

    let mut handler = Counting::default();
    let ((), left) = run_with::<Counting, TermParser>(&mut handler, &input)
        .unwrap_or_else(|(kind, span)| panic!("{kind:?} at {span:?}"));
    assert_eq!(left, 0);
    assert_eq!(handler.terms, 1);
}

#[test]
fn matches() {
    // the standard's list append and length examples
    assert_eq!(
        parse_all::<TermParser>(b"(match l ((nil l2) ((cons h t) (cons h (append t l2)))))"),
        "(match l ((nil l2) ((cons h t) (cons h (append t l2)))))"
    );
    assert_eq!(
        parse_all::<TermParser>(b"(match l (((cons h t) (cons h (append t l2))) (_ l2)))"),
        "(match l (((cons h t) (cons h (append t l2))) (_ l2)))"
    );
    assert_eq!(
        parse_all::<TermParser>(b"(match l ((nil 0) ((cons _ t) (+ 1 (length t)))))"),
        "(match l ((nil 0) ((cons _ t) (+ 1 (length t)))))"
    );
    // a single case with a symbol pattern
    assert_eq!(
        parse_all::<TermParser>(b"(match x ((y y)))"),
        "(match x ((y y)))"
    );
    // wildcards in every position
    assert_eq!(
        parse_all::<TermParser>(b"(match x (((c _ _) 1) (_ 2)))"),
        "(match x (((c _ _) 1) (_ 2)))"
    );
    // a compound scrutinee
    assert_eq!(
        parse_all::<TermParser>(b"(match (f x y) ((z z)))"),
        "(match (f x y) ((z z)))"
    );
}

#[test]
fn matches_nest_and_compose() {
    // match in the scrutinee and in a case body
    assert_eq!(
        parse_all::<TermParser>(b"(match (match x ((a 1))) ((b 2)))"),
        "(match (match x ((a 1))) ((b 2)))"
    );
    assert_eq!(
        parse_all::<TermParser>(b"(match x ((a (match y ((b 1))))))"),
        "(match x ((a (match y ((b 1))))))"
    );
    // match as an application argument
    assert_eq!(
        parse_all::<TermParser>(b"(f (match x ((a 1))) 2)"),
        "(f (match x ((a 1))) 2)"
    );
    // match inside a let and let inside a match
    assert_eq!(
        parse_all::<TermParser>(b"(let ((v (match x ((a 1))))) v)"),
        "(let ((v (match x ((a 1))))) v)"
    );
    assert_eq!(
        parse_all::<TermParser>(b"(match x ((a (let ((v 1)) v))))"),
        "(match x ((a (let ((v 1)) v))))"
    );
    // match inside a binder
    assert_eq!(
        parse_all::<TermParser>(b"(forall ((x Int)) (match x ((a 1))))"),
        "(forall ((x Int)) (match x ((a 1))))"
    );
    // annotated match and annotated case body
    assert_eq!(
        parse_all::<TermParser>(b"(! (match x ((a 1))) :named n)"),
        "(! (match x ((a 1))) :named n)"
    );
    assert_eq!(
        parse_all::<TermParser>(b"(match x ((a (! 1 :named n))))"),
        "(match x ((a (! 1 :named n))))"
    );
}

#[test]
fn match_consumes_exactly_one_term() {
    let (term, left) = run::<TermParser>(b"(match x ((a 1))) y").expect("valid");
    assert_eq!(term, "(match x ((a 1)))");
    assert_eq!(left, 1);
}

#[test]
fn match_term_parser_is_reusable() {
    let (first, second) = parse_two::<TermParser>(b"(match x ((a 1))) (match y (((c v) v) (_ 0)))");
    assert_eq!(first, "(match x ((a 1)))");
    assert_eq!(second, "(match y (((c v) v) (_ 0)))");

    // a constructor pattern followed by a simple one exercises
    // the self-reset contract of the pattern machinery
    let (first, second) = parse_two::<TermParser>(b"(match x (((c v) v))) (match y ((_ 0)))");
    assert_eq!(first, "(match x (((c v) v)))");
    assert_eq!(second, "(match y ((_ 0)))");
}

#[test]
fn match_errors() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // the scrutinee is required
    let err = assert_error::<TermParser>(b"(match)", 6, 7);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Term])
        ),
        "{err:?}"
    );
    // the case list is required
    let err = assert_error::<TermParser>(b"(match x)", 8, 9);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(SmtTokenCategory::ParenOpen)])
        ),
        "{err:?}"
    );
    // at least one case is required
    let err = assert_error::<TermParser>(b"(match x ())", 10, 11);
    assert!(
        matches!(err, SmtSyntaxErrorKind::Empty(SmtNonEmptyList::MatchCases)),
        "{err:?}"
    );
    // each case is parenthesized
    let err = assert_error::<TermParser>(b"(match x (x))", 10, 11);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[
                SmtSyntaxExpected::Token(SmtTokenCategory::ParenOpen),
                SmtSyntaxExpected::Token(SmtTokenCategory::ParenClose)
            ])
        ),
        "{err:?}"
    );
    // a pattern starts with a symbol, a wildcard, or a constructor application
    let err = assert_error::<TermParser>(b"(match x ((1 y)))", 11, 12);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[
                SmtSyntaxExpected::Symbol,
                SmtSyntaxExpected::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore)),
                SmtSyntaxExpected::Token(SmtTokenCategory::ParenOpen)
            ])
        ),
        "{err:?}"
    );
    // a constructor application has at least one argument
    let err = assert_error::<TermParser>(b"(match x (((c) y)))", 13, 14);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Empty(SmtNonEmptyList::PatternArguments)
        ),
        "{err:?}"
    );
    // the constructor is a symbol, not a wildcard or a constant
    let err = assert_error::<TermParser>(b"(match x (((1 y) z)))", 12, 13);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Symbol])
        ),
        "{err:?}"
    );
    let err = assert_error::<TermParser>(b"(match x (((_ y) z)))", 12, 13);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Symbol])
        ),
        "{err:?}"
    );
    // the arguments are symbols or wildcards, not nested patterns or constants
    let err = assert_error::<TermParser>(b"(match x (((c 1) z)))", 14, 15);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[
                SmtSyntaxExpected::Symbol,
                SmtSyntaxExpected::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore))
            ])
        ),
        "{err:?}"
    );
    let err = assert_error::<TermParser>(b"(match x (((c (d y)) z)))", 14, 15);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[
                SmtSyntaxExpected::Symbol,
                SmtSyntaxExpected::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore))
            ])
        ),
        "{err:?}"
    );
    // the case body is required
    let err = assert_error::<TermParser>(b"(match x ((y)))", 12, 13);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Term])
        ),
        "{err:?}"
    );
    // exactly one case body
    let err = assert_error::<TermParser>(b"(match x ((y 1 2)))", 15, 16);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(SmtTokenCategory::ParenClose)])
        ),
        "{err:?}"
    );
    // nothing follows the case list
    let err = assert_error::<TermParser>(b"(match x ((y 1)) z)", 17, 18);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(SmtTokenCategory::ParenClose)])
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
    let ((), left) = run_with::<Counting, TermParser>(&mut handler, &input)
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

impl Handler for Consuming {
    type Error = Infallible;
    type SExpr = ();
    type Attribute = ();
    type Sort = ();
    type Term = String;
    type Scope = ();

    fn set_version(&mut self, _version: SmtVersion) {}

    fn handle_sort(&mut self, _sort: Sort<Self::Sort>) -> Result<(), Infallible> {
        Ok(())
    }
    fn handle_term(&mut self, term: Term<Self::Sort, Self::Term>) -> Result<String, Infallible> {
        Ok(match term {
            Term::SpecialConstant(constant) => render_constant(&constant),
            Term::QualifiedIdent(qualified_ident) => render_ident(&qualified_ident.ident),
            Term::Application(application) => {
                let function = render_ident(&application.function.ident);
                let args: Vec<String> = application.args.to_vec();
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
    fn start_let(&mut self, _bindings: Bindings<Self::Term>) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_let(&mut self, _scope: (), body: String) -> Result<String, Infallible> {
        Ok(body)
    }
    fn handle_s_expr(&mut self, _expr: SExpr<Self::SExpr>) -> Result<(), Infallible> {
        Ok(())
    }
    fn handle_attribute(
        &mut self,
        _name: SmtKeywordBuf,
        _value: Option<AttributeValue<Self::SExpr>>,
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn annotate_term(
        &mut self,
        term: String,
        _attributes: Vec<Self::Attribute>,
    ) -> Result<String, Infallible> {
        Ok(term)
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _vars: SortedVars<Self::Sort>,
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _scope: (),
        body: String,
    ) -> Result<String, Infallible> {
        Ok(body)
    }
    fn start_lambda(&mut self, _vars: SortedVars<Self::Sort>) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_lambda(&mut self, _scope: (), body: String) -> Result<String, Infallible> {
        Ok(body)
    }
    fn start_match(&mut self, _scrutinee: &String) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_match_case(
        &mut self,
        _scrutinee: &String,
        _pattern: SmtPatternBuf,
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn end_match_case(
        &mut self,
        _scope: (),
        _scrutinee: &String,
        body: String,
    ) -> Result<String, Infallible> {
        Ok(body)
    }
    fn end_match(
        &mut self,
        _scrutinee: String,
        _cases: MatchCases<Self::Term>,
    ) -> Result<String, Infallible> {
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
        let (term, left) =
            run_with::<Consuming, TermParser>(&mut handler, b"(f (g x) (h a b c) y)")
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

#[test]
fn no_end_call_comes_before_a_missing_closing_parenthesis() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // each input has a stray token where a construct's closing parenthesis
    // belongs; the construct is not ended before the error
    let cases: [(&[u8], u64, u64, &[&str]); 6] = [
        (b"(let ((x 1)) x y)", 15, 16, &["start-let"]),
        (b"(forall ((x Int)) x y)", 20, 21, &["start-quantifier"]),
        (
            b"(exists ((x Int) (y Int)) x z)",
            28,
            29,
            &["start-quantifier"],
        ),
        (b"(lambda ((x Int)) x y)", 20, 21, &["start-lambda"]),
        // the case is not ended before its closing parenthesis
        (
            b"(match s ((x 1 2)))",
            15,
            16,
            &["start-match", "start-match-case"],
        ),
        // the match is not ended before its closing parenthesis
        (
            b"(match s ((x 1)) y)",
            17,
            18,
            &["start-match", "start-match-case", "end-match-case"],
        ),
    ];
    for (input, start, end, calls) in cases {
        let mut handler = Calls::default();
        match run_with::<Calls, TermParser>(&mut handler, input) {
            Ok(_) => panic!("expected a parser error in {:?}, got Ok", text(input)),
            Err((kind, span)) => {
                assert!(
                    matches!(
                        kind,
                        SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(
                            SmtTokenCategory::ParenClose
                        )])
                    ),
                    "{kind:?} in {:?}",
                    text(input)
                );
                assert_eq!(
                    (span.start().offset(), span.end().offset()),
                    (start, end),
                    "error span mismatch (start, end) as byte offsets in {:?}",
                    text(input)
                );
            }
        }
        assert_eq!(handler.calls, calls, "calls in {:?}", text(input));
    }
}

#[test]
fn match_cases_keep_their_patterns_and_scrutinee_across_nested_matches() {
    // the cases of the outer match are stored while a nested match in a case
    // body stores and hands over its own; `Printing` checks that every case
    // and match end is given the scrutinee of its own match, and that the
    // patterns handed over with the cases are the ones the cases started with
    assert_eq!(
        parse_all::<TermParser>(
            b"(match l (((cons h t) (match t (((cons h2 t2) h2) (nil h)))) \
              (nil (match m ((_ 0) ((pair a b) a))))))"
        ),
        "(match l (((cons h t) (match t (((cons h2 t2) h2) (nil h)))) \
         (nil (match m ((_ 0) ((pair a b) a))))))"
    );
    // two constructor cases at each level: each case's arguments end where
    // the next case's begin
    assert_eq!(
        parse_all::<TermParser>(
            b"(match p (((pair a b) (match a (((pair c d) c) ((single e) e)))) ((single f) f)))"
        ),
        "(match p (((pair a b) (match a (((pair c d) c) ((single e) e)))) ((single f) f)))"
    );
    // a nested match as the scrutinee of a case's own match
    assert_eq!(
        parse_all::<TermParser>(b"(match x (((c u v) (match (match u ((w w))) ((z (f z v)))))))"),
        "(match x (((c u v) (match (match u ((w w))) ((z (f z v)))))))"
    );
}

/// Handler that numbers every scope it opens and checks that each end call
/// is given back the scope of its own construct, the innermost one open.
#[derive(Default)]
struct ScopeIds {
    /// The number of the next scope.
    next: u64,
    /// The scopes open, innermost last.
    open: Vec<u64>,
    /// The starts and ends, with their scopes.
    calls: Vec<String>,
}

impl ScopeIds {
    fn open(&mut self, call: &str) -> u64 {
        self.next += 1;
        self.open.push(self.next);
        self.calls.push(format!("{call} {}", self.next));
        self.next
    }

    fn close(&mut self, call: &str, scope: u64) {
        assert_eq!(
            self.open.pop(),
            Some(scope),
            "{call} is given back the scope of its own construct"
        );
        self.calls.push(format!("{call} {scope}"));
    }
}

impl Handler for ScopeIds {
    type Error = Infallible;
    type SExpr = ();
    type Attribute = ();
    type Sort = ();
    type Term = ();
    type Scope = u64;

    fn set_version(&mut self, _version: SmtVersion) {}

    fn handle_sort(&mut self, _sort: Sort<Self::Sort>) -> Result<(), Infallible> {
        Ok(())
    }
    fn handle_term(&mut self, _term: Term<Self::Sort, Self::Term>) -> Result<(), Infallible> {
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
        Ok(())
    }
    fn annotate_term(
        &mut self,
        _term: (),
        _attributes: Vec<Self::Attribute>,
    ) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_let(&mut self, _bindings: Bindings<Self::Term>) -> Result<u64, Infallible> {
        Ok(self.open("start-let"))
    }
    fn end_let(&mut self, scope: u64, _body: ()) -> Result<(), Infallible> {
        self.close("end-let", scope);
        Ok(())
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _vars: SortedVars<Self::Sort>,
    ) -> Result<u64, Infallible> {
        Ok(self.open("start-quantifier"))
    }
    fn end_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        scope: u64,
        _body: (),
    ) -> Result<(), Infallible> {
        self.close("end-quantifier", scope);
        Ok(())
    }
    fn start_lambda(&mut self, _vars: SortedVars<Self::Sort>) -> Result<u64, Infallible> {
        Ok(self.open("start-lambda"))
    }
    fn end_lambda(&mut self, scope: u64, _body: ()) -> Result<(), Infallible> {
        self.close("end-lambda", scope);
        Ok(())
    }
    fn start_match(&mut self, _scrutinee: &()) -> Result<(), Infallible> {
        Ok(())
    }
    fn start_match_case(
        &mut self,
        _scrutinee: &(),
        _pattern: SmtPatternBuf,
    ) -> Result<u64, Infallible> {
        Ok(self.open("start-match-case"))
    }
    fn end_match_case(&mut self, scope: u64, _scrutinee: &(), _body: ()) -> Result<(), Infallible> {
        self.close("end-match-case", scope);
        Ok(())
    }
    fn end_match(
        &mut self,
        _scrutinee: (),
        _cases: MatchCases<Self::Term>,
    ) -> Result<(), Infallible> {
        Ok(())
    }
}

#[test]
fn every_scope_is_given_back_at_its_own_end() {
    let mut handler = ScopeIds::default();
    let ((), left) = run_with::<ScopeIds, TermParser>(
        &mut handler,
        b"(let ((a 1)) (forall ((x Int) (y Int)) \
          (match a ((b (lambda ((z Int)) (exists ((w Int)) z))) (_ (let ((c 2)) c))))))",
    )
    .unwrap_or_else(|(kind, span)| panic!("{kind:?} at {span:?}"));
    assert_eq!(left, 0);
    assert!(handler.open.is_empty(), "every scope is closed");
    assert_eq!(
        handler.calls,
        [
            "start-let 1",
            "start-quantifier 2",
            "start-match-case 3",
            "start-lambda 4",
            "start-quantifier 5",
            "end-quantifier 5",
            "end-lambda 4",
            "end-match-case 3",
            "start-match-case 6",
            "start-let 7",
            "end-let 7",
            "end-match-case 6",
            "end-quantifier 2",
            "end-let 1",
        ]
    );
}

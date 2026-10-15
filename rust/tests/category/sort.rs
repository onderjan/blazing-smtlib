//! Tests of the sort parser.

use super::*;
use blazing_smtlib::{
    parser::{SmtNonEmptyList, SmtSyntaxExpected},
    token::{SmtGeneralReserved, SmtReserved, SmtTokenCategory},
};

#[test]
fn simple_sort() {
    assert_eq!(parse_all::<SortParser>(b"Bool"), "Bool");
    assert_eq!(parse_all::<SortParser>(b"|my sort|"), "|my sort|");

    let (sort, left) = run::<SortParser>(b"Int Bool").expect("valid");
    assert_eq!(sort, "Int");
    assert_eq!(left, 1);
}

#[test]
fn indexed_sort() {
    assert_eq!(parse_all::<SortParser>(b"(_ BitVec 8)"), "(_ BitVec 8)");
    assert_eq!(
        parse_all::<SortParser>(b"(_ FloatingPoint 8 24)"),
        "(_ FloatingPoint 8 24)"
    );
}

#[test]
fn applied_sort() {
    assert_eq!(parse_all::<SortParser>(b"(Set Int)"), "(Set Int)");
    assert_eq!(
        parse_all::<SortParser>(b"(Array Int Int)"),
        "(Array Int Int)"
    );

    // sorts nest in any argument position
    assert_eq!(
        parse_all::<SortParser>(b"(Array (Array Int Int) Int)"),
        "(Array (Array Int Int) Int)"
    );
    assert_eq!(
        parse_all::<SortParser>(b"(Array Int (Array Int Int))"),
        "(Array Int (Array Int Int))"
    );

    // the closing parenthesis ends the sort; the rest is left for the caller
    let (sort, left) = run::<SortParser>(b"(Set Int) Bool").expect("valid");
    assert_eq!(sort, "(Set Int)");
    assert_eq!(left, 1);
}

#[test]
fn applied_indexed_sort() {
    // indexed identifier as an argument sort
    assert_eq!(
        parse_all::<SortParser>(b"(Array (_ BitVec 8) Int)"),
        "(Array (_ BitVec 8) Int)"
    );

    // indexed identifier as the applied head
    assert_eq!(
        parse_all::<SortParser>(b"((_ FixedSizeList 4) Real)"),
        "((_ FixedSizeList 4) Real)"
    );

    // both at once
    assert_eq!(
        parse_all::<SortParser>(b"((_ Tuple 2) (_ BitVec 8) (Set Int))"),
        "((_ Tuple 2) (_ BitVec 8) (Set Int))"
    );
}

#[test]
fn errors() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    let expected_sort = SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Sort]);
    assert_eq!(assert_error::<SortParser>(b"1", 0, 1), expected_sort);
    assert_eq!(assert_error::<SortParser>(b")", 0, 1), expected_sort);
    assert_eq!(assert_error::<SortParser>(b"", 0, 0), expected_sort);

    // unterminated applied sort runs into the end of input
    assert_eq!(
        assert_error::<SortParser>(b"(Array Int", 10, 10),
        expected_sort
    );

    // after `(`, only `_`, a symbol, or `(` may follow
    let err = assert_error::<SortParser>(b"(as x Bool)", 1, 3);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[
                SmtSyntaxExpected::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore)),
                SmtSyntaxExpected::Symbol,
                SmtSyntaxExpected::Token(SmtTokenCategory::ParenOpen)
            ])
        ),
        "{err:?}"
    );
    let err = assert_error::<SortParser>(b"(1 2)", 1, 2);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[
                SmtSyntaxExpected::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore)),
                SmtSyntaxExpected::Symbol,
                SmtSyntaxExpected::Token(SmtTokenCategory::ParenOpen)
            ])
        ),
        "{err:?}"
    );
    let err = assert_error::<SortParser>(b"()", 1, 2);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[
                SmtSyntaxExpected::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore)),
                SmtSyntaxExpected::Symbol,
                SmtSyntaxExpected::Token(SmtTokenCategory::ParenOpen)
            ])
        ),
        "{err:?}"
    );

    // an applied identifier must be applied to at least one sort
    let err = assert_error::<SortParser>(b"(Int)", 4, 5);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Empty(SmtNonEmptyList::SortApplication)
        ),
        "{err:?}"
    );
    let err = assert_error::<SortParser>(b"((_ BitVec 8))", 13, 14);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Empty(SmtNonEmptyList::SortApplication)
        ),
        "{err:?}"
    );

    // a parenthesized applied head must be an indexed identifier
    let err = assert_error::<SortParser>(b"((Array) Int)", 2, 7);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Reserved(SmtReserved::General(
                SmtGeneralReserved::Underscore
            ))])
        ),
        "{err:?}"
    );

    // errors inside the indexed identifier are reported by the identifier parser
    let err = assert_error::<SortParser>(b"(_ BitVec)", 9, 10);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Empty(SmtNonEmptyList::IdentIndices)
        ),
        "{err:?}"
    );
}

/// Handler that only counts sorts, so deep nesting does not build huge strings.
#[derive(Default)]
struct Counting {
    sorts: usize,
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
        self.sorts += 1;
        Ok(())
    }
    fn handle_term(&mut self, _term: Term<Self::Sort, Self::Term>) -> Result<(), Infallible> {
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
    let ((), left) = run_with::<Counting, SortParser>(&mut handler, &input)
        .unwrap_or_else(|(kind, span)| panic!("{kind:?} at {span:?}"));
    assert_eq!(left, 0);
    // every applied `Array` sort plus every `Int` leaf
    assert_eq!(handler.sorts, 2 * DEPTH + 1);
}

//! Tests of the sort parser.

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
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Reserved(Reserved::Underscore)])
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
    fn annotate_term(&mut self, _term: (), _attributes: Vec<()>) -> Result<(), Infallible> {
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

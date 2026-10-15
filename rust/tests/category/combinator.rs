//! Tests of the generic combinators.

use super::*;
use blazing_smtlib::{parser::SmtSyntaxExpected, token::SmtTokenCategory};

#[test]
fn pair_parser() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    let (first, second) = parse_all::<PairParser<SymbolParser, SymbolParser>>(b"a b");
    assert_eq!(first.as_slice(), b"a");
    assert_eq!(second.as_slice(), b"b");

    // the error of the second element points at its token
    let err = assert_error::<PairParser<SymbolParser, SymbolParser>>(b"a 1", 2, 3);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Symbol])
        ),
        "{err:?}"
    );
}

#[test]
fn closed_parser() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    let symbol = parse_all::<ClosedParser<SymbolParser>>(b"a)");
    assert_eq!(symbol.as_slice(), b"a");

    let err = assert_error::<ClosedParser<SymbolParser>>(b"a b", 2, 3);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(SmtTokenCategory::ParenClose)])
        ),
        "{err:?}"
    );
    // EOF instead of the closing parenthesis
    let err = assert_error::<ClosedParser<SymbolParser>>(b"a", 1, 1);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(SmtTokenCategory::ParenClose)])
        ),
        "{err:?}"
    );
}

#[test]
fn open_closed_parser() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    let symbol = parse_all::<ParenParser<SymbolParser>>(b"(a)");
    assert_eq!(symbol.as_slice(), b"a");

    let err = assert_error::<ParenParser<SymbolParser>>(b"a)", 0, 1);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(SmtTokenCategory::ParenOpen)])
        ),
        "{err:?}"
    );
    let err = assert_error::<ParenParser<SymbolParser>>(b"(a", 2, 2);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(SmtTokenCategory::ParenClose)])
        ),
        "{err:?}"
    );
}

#[test]
fn closed_multiple_parser() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // the closed multiple parser starts inside the list:
    // its opening parenthesis was already consumed by the caller
    let symbols = parse_all::<ClosedMultipleParser<SymbolParser>>(b"a b c)");
    let symbols: Vec<&[u8]> = symbols.iter().map(|s| s.as_slice()).collect();
    assert_eq!(symbols, [b"a" as &[u8], b"b", b"c"]);

    // zero elements are allowed
    let symbols = parse_all::<ClosedMultipleParser<SymbolParser>>(b")");
    assert!(symbols.is_empty());

    // the element parser's error is reported for a bad element
    let err = assert_error::<ClosedMultipleParser<SymbolParser>>(b"a 1)", 2, 3);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Symbol])
        ),
        "{err:?}"
    );
    // unclosed list ends at EOF inside the element parser
    let err = assert_error::<ClosedMultipleParser<SymbolParser>>(b"a", 1, 1);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Symbol])
        ),
        "{err:?}"
    );
}

#[test]
fn paren_multiple_parser() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // the parenthesized variant consumes the opening parenthesis itself
    let symbols = parse_all::<ParenMultipleParser<SymbolParser>>(b"(a b c)");
    let symbols: Vec<&[u8]> = symbols.iter().map(|s| s.as_slice()).collect();
    assert_eq!(symbols, [b"a" as &[u8], b"b", b"c"]);

    // zero elements are allowed
    let symbols = parse_all::<ParenMultipleParser<SymbolParser>>(b"()");
    assert!(symbols.is_empty());

    // the opening parenthesis is required
    let err = assert_error::<ParenMultipleParser<SymbolParser>>(b"a", 0, 1);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(SmtTokenCategory::ParenOpen)])
        ),
        "{err:?}"
    );
    // the element parser's error is reported for a bad element
    let err = assert_error::<ParenMultipleParser<SymbolParser>>(b"(a 1)", 3, 4);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Symbol])
        ),
        "{err:?}"
    );
    // unclosed list ends at EOF inside the element parser
    let err = assert_error::<ParenMultipleParser<SymbolParser>>(b"(a", 2, 2);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Symbol])
        ),
        "{err:?}"
    );
}

#[test]
fn nested_combinators() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // the shape used for define-fun parameters: ((x S) (y T))
    type Params = ParenMultipleParser<ParenParser<PairParser<SymbolParser, SymbolParser>>>;
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
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Symbol])
        ),
        "{err:?}"
    );
}

// --- Tuples ---

use super::parse_backend::{
    Tuple3Parser, Tuple4Parser, Tuple5Parser, Tuple6Parser, Tuple7Parser, Tuple8Parser,
};

/// The bytes of symbols, to compare tuples of them.
fn slices<const N: usize>(symbols: [&SmtSymbolBuf; N]) -> [&[u8]; N] {
    symbols.map(|symbol| symbol.as_slice())
}

#[test]
fn tuple_parsers_yield_the_values_in_one_flat_tuple() {
    type S = SymbolParser;
    let (a, b, c) = parse_all::<Tuple3Parser<S, S, S>>(b"a b c");
    assert_eq!(slices([&a, &b, &c]), [b"a", b"b", b"c"]);
    let (a, b, c, d) = parse_all::<Tuple4Parser<S, S, S, S>>(b"a b c d");
    assert_eq!(slices([&a, &b, &c, &d]), [b"a", b"b", b"c", b"d"]);
    let (a, b, c, d, e) = parse_all::<Tuple5Parser<S, S, S, S, S>>(b"a b c d e");
    assert_eq!(slices([&a, &b, &c, &d, &e]), [b"a", b"b", b"c", b"d", b"e"]);
    let (a, b, c, d, e, f) = parse_all::<Tuple6Parser<S, S, S, S, S, S>>(b"a b c d e f");
    assert_eq!(
        slices([&a, &b, &c, &d, &e, &f]),
        [b"a", b"b", b"c", b"d", b"e", b"f"]
    );
    let (a, b, c, d, e, f, g) = parse_all::<Tuple7Parser<S, S, S, S, S, S, S>>(b"a b c d e f g");
    assert_eq!(
        slices([&a, &b, &c, &d, &e, &f, &g]),
        [b"a", b"b", b"c", b"d", b"e", b"f", b"g"]
    );
    let (a, b, c, d, e, f, g, h) =
        parse_all::<Tuple8Parser<S, S, S, S, S, S, S, S>>(b"a b c d e f g h");
    assert_eq!(
        slices([&a, &b, &c, &d, &e, &f, &g, &h]),
        [b"a", b"b", b"c", b"d", b"e", b"f", b"g", b"h"]
    );

    // values of several categories, each over several tokens
    let (name, sort, term) =
        parse_all::<Tuple3Parser<SymbolParser, SortParser, TermParser>>(b"x (Array Int Int) (f x)");
    assert_eq!(name.as_slice(), b"x");
    assert_eq!(sort, "(Array Int Int)");
    assert_eq!(term, "(f x)");
}

#[test]
fn tuple_parser_fails_as_the_nested_pair_parsers() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    type Tuple = Tuple3Parser<SymbolParser, SortParser, SymbolParser>;
    type Nested = PairParser<SymbolParser, PairParser<SortParser, SymbolParser>>;

    // a missing middle value: the error points at the token in its place
    let err = assert_error::<Tuple>(b"a ) c", 2, 3);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Sort])
        ),
        "{err:?}"
    );

    for input in [
        &b"a ) c"[..],
        b"1 Int c",
        b"a (Array) c",
        b"a Int 1",
        b"a Int",
        b"a",
        b"",
    ] {
        let tuple = run::<Tuple>(input);
        let nested = run::<Nested>(input);
        match (tuple, nested) {
            (Err(tuple), Err(nested)) => assert_eq!(tuple, nested, "in {:?}", text(input)),
            (tuple, nested) => panic!(
                "both must fail in {:?}, got {:?} and {:?}",
                text(input),
                tuple.err(),
                nested.err()
            ),
        }
    }

    // and they agree where they succeed
    let ((a, sort, b), left) = run::<Tuple>(b"a (Array Int Bool) b c").expect("a valid tuple");
    let ((na, (nsort, nb)), nleft) =
        run::<Nested>(b"a (Array Int Bool) b c").expect("valid nested pairs");
    assert_eq!(
        (a.as_slice(), sort.as_str(), b.as_slice(), left),
        (na.as_slice(), nsort.as_str(), nb.as_slice(), nleft)
    );
    assert_eq!(left, 1);
}

#[test]
fn tuple_parser_parses_consecutive_values() {
    // the first value ends inside a compound sort of the last parser, which
    // must start the second value at the first parser again
    let ((sort, name, last), (next_sort, next_name, next_last)) =
        parse_two::<Tuple3Parser<SortParser, SymbolParser, SortParser>>(
            b"(Array Int Int) a (_ BitVec 8) Bool b Int",
        );
    assert_eq!(
        (sort.as_str(), name.as_slice(), last.as_str()),
        ("(Array Int Int)", &b"a"[..], "(_ BitVec 8)")
    );
    assert_eq!(
        (next_sort.as_str(), next_name.as_slice(), next_last.as_str()),
        ("Bool", &b"b"[..], "Int")
    );
}

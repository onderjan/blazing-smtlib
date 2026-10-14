//! Tests of the generic combinators.

use super::*;

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
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
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
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
    // EOF instead of the closing parenthesis
    let err = assert_error::<ClosedParser<SymbolParser>>(b"a", 1, 1);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
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
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    let err = assert_error::<ParenParser<SymbolParser>>(b"(a", 2, 2);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
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
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    // unclosed list ends at EOF inside the element parser
    let err = assert_error::<ClosedMultipleParser<SymbolParser>>(b"a", 1, 1);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
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
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // the element parser's error is reported for a bad element
    let err = assert_error::<ParenMultipleParser<SymbolParser>>(b"(a 1)", 3, 4);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    // unclosed list ends at EOF inside the element parser
    let err = assert_error::<ParenMultipleParser<SymbolParser>>(b"(a", 2, 2);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
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
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
}

//! Tests of the generic combinators.

use super::*;

#[test]
fn pair_parser() {
    let (first, second) = parse_all::<PairParser<Printing, SymbolParser, SymbolParser>>(b"a b");
    assert_eq!(first.as_slice(), b"a");
    assert_eq!(second.as_slice(), b"b");

    // the error of the second element points at its token
    let err = assert_error::<PairParser<Printing, SymbolParser, SymbolParser>>(b"a 1", 2, 3);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
}

#[test]
fn closed_parser() {
    let symbol = parse_all::<ClosedParser<Printing, SymbolParser>>(b"a)");
    assert_eq!(symbol.as_slice(), b"a");

    let err = assert_error::<ClosedParser<Printing, SymbolParser>>(b"a b", 2, 3);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
    // EOF instead of the closing parenthesis
    let err = assert_error::<ClosedParser<Printing, SymbolParser>>(b"a", 1, 1);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
}

#[test]
fn open_closed_parser() {
    let symbol = parse_all::<OpenClosedParser<Printing, SymbolParser>>(b"(a)");
    assert_eq!(symbol.as_slice(), b"a");

    let err = assert_error::<OpenClosedParser<Printing, SymbolParser>>(b"a)", 0, 1);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
        ),
        "{err:?}"
    );
    let err = assert_error::<OpenClosedParser<Printing, SymbolParser>>(b"(a", 2, 2);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
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
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
        ),
        "{err:?}"
    );
    // the element parser's error is reported for a bad element
    let err = assert_error::<MultipleParser<Printing, SymbolParser>>(b"(a 1)", 3, 4);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
    // unclosed list ends at EOF inside the element parser
    let err = assert_error::<MultipleParser<Printing, SymbolParser>>(b"(a", 2, 2);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
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
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
}

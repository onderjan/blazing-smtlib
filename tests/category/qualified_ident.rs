//! Tests of the qualified-identifier parser.

use super::*;

fn name(qualified_ident: &SmtQualifiedIdent<Printing>) -> &[u8] {
    qualified_ident.ident.name.as_slice()
}

#[test]
fn simple_symbol() {
    let qi = parse_all::<QualifiedIdentParser<Printing>>(b"x");
    assert_eq!(name(&qi), b"x");
    assert!(qi.ident.indices.is_empty());
    assert_eq!(qi.sort, None);

    // a plain symbol is a single token; the rest is left for the caller
    let (qi, left) = run::<QualifiedIdentParser<Printing>>(b"x y").expect("valid");
    assert_eq!(name(&qi), b"x");
    assert_eq!(left, 1);
}

#[test]
fn unqualified_indexed() {
    let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(_ extract 7 0)");
    assert_eq!(name(&qi), b"extract");
    assert_eq!(qi.ident.indices.len(), 2);
    assert_eq!(qi.sort, None);

    // the ident's own closing parenthesis ends the qualified ident;
    // the parser must not wait for another token after it
    let (qi, left) = run::<QualifiedIdentParser<Printing>>(b"(_ bv5 8) y").expect("valid");
    assert_eq!(name(&qi), b"bv5");
    assert_eq!(left, 1);
}

#[test]
fn qualified_simple_ident() {
    let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(as x Bool)");
    assert_eq!(name(&qi), b"x");
    assert!(qi.ident.indices.is_empty());
    assert_eq!(qi.sort.as_deref(), Some("Bool"));
}

#[test]
fn qualified_indexed_ident() {
    // the inner ident parser continues over multiple tokens
    let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(as (_ f 1) Bool)");
    assert_eq!(name(&qi), b"f");
    assert_eq!(qi.ident.indices.len(), 1);
    assert_eq!(qi.sort.as_deref(), Some("Bool"));
}

#[test]
fn qualified_indexed_sort() {
    let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(as x (_ BitVec 8))");
    assert_eq!(name(&qi), b"x");
    assert_eq!(qi.sort.as_deref(), Some("(_ BitVec 8)"));
}

#[test]
fn qualified_applied_sort() {
    // the sort parser handles applied sorts inside `as` as well
    let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(as x (Array Int Int))");
    assert_eq!(name(&qi), b"x");
    assert_eq!(qi.sort.as_deref(), Some("(Array Int Int)"));
}

#[test]
fn entry_points() {
    // the callers that already consumed `(`, `( _` or `( as`
    // start in the corresponding state, so the parser accepts
    // the rest of the qualified identifier
    let mut parser = QualifiedIdentParser::<Printing>::new();
    parser.move_after_open_paren();
    let qi = parse_all_from(parser, b"_ f 1)");
    assert_eq!(name(&qi), b"f");
    assert_eq!(qi.ident.indices.len(), 1);
    assert_eq!(qi.sort, None);

    // regression: the entry point must put the inner ident parser after
    // the underscore as well, or `f` alone would finish the identifier
    let mut parser = QualifiedIdentParser::<Printing>::new();
    parser.move_after_underscore();
    let qi = parse_all_from(parser, b"f 1)");
    assert_eq!(name(&qi), b"f");
    assert_eq!(qi.ident.indices.len(), 1);
    assert_eq!(qi.sort, None);

    let mut parser = QualifiedIdentParser::<Printing>::new();
    parser.move_after_as();
    let qi = parse_all_from(parser, b"x Bool)");
    assert_eq!(name(&qi), b"x");
    assert_eq!(qi.sort.as_deref(), Some("Bool"));
}

#[test]
fn errors() {
    let err = assert_error::<QualifiedIdentParser<Printing>>(b"1", 0, 1);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedIdent),
        "{err:?}"
    );

    // after `(` only `_` or `as` may follow
    let err = assert_error::<QualifiedIdentParser<Printing>>(b"(f 1)", 1, 2);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[
                TokenType::Reserved(Reserved::Underscore),
                TokenType::Reserved(Reserved::As)
            ])
        ),
        "{err:?}"
    );

    // `as` must be followed by an identifier
    let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as)", 3, 4);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedIdent),
        "{err:?}"
    );
    let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as 1 Bool)", 4, 5);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedIdent),
        "{err:?}"
    );

    // ... and a sort
    let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as x)", 5, 6);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedSort),
        "{err:?}"
    );

    // ... and the closing parenthesis
    let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as x Bool z)", 11, 12);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );

    // EOF while waiting for the closing parenthesis
    let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as x Bool", 10, 10);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
}

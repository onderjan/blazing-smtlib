//! Tests of the qualified-identifier parser.

use super::*;

fn name(qualified_ident: &SmtQualifiedIdent<Printing>) -> &[u8] {
    qualified_ident.ident.name.as_slice()
}

#[test]
fn simple_symbol() {
    let qi = parse_all::<SmtQualifiedIdentParser<Printing>>(b"x");
    assert_eq!(name(&qi), b"x");
    assert!(qi.ident.indices.is_empty());
    assert_eq!(qi.sort, None);

    // a plain symbol is a single token; the rest is left for the caller
    let (qi, left) = run::<SmtQualifiedIdentParser<Printing>>(b"x y").expect("valid");
    assert_eq!(name(&qi), b"x");
    assert_eq!(left, 1);
}

#[test]
fn unqualified_indexed() {
    let qi = parse_all::<SmtQualifiedIdentParser<Printing>>(b"(_ extract 7 0)");
    assert_eq!(name(&qi), b"extract");
    assert_eq!(qi.ident.indices.len(), 2);
    assert_eq!(qi.sort, None);

    // the ident's own closing parenthesis ends the qualified ident;
    // the parser must not wait for another token after it
    let (qi, left) = run::<SmtQualifiedIdentParser<Printing>>(b"(_ bv5 8) y").expect("valid");
    assert_eq!(name(&qi), b"bv5");
    assert_eq!(left, 1);
}

#[test]
fn qualified_simple_ident() {
    let qi = parse_all::<SmtQualifiedIdentParser<Printing>>(b"(as x Bool)");
    assert_eq!(name(&qi), b"x");
    assert!(qi.ident.indices.is_empty());
    assert_eq!(qi.sort.as_deref(), Some("Bool"));
}

#[test]
fn qualified_indexed_ident() {
    // the inner ident parser continues over multiple tokens
    let qi = parse_all::<SmtQualifiedIdentParser<Printing>>(b"(as (_ f 1) Bool)");
    assert_eq!(name(&qi), b"f");
    assert_eq!(qi.ident.indices.len(), 1);
    assert_eq!(qi.sort.as_deref(), Some("Bool"));
}

#[test]
fn qualified_indexed_sort() {
    let qi = parse_all::<SmtQualifiedIdentParser<Printing>>(b"(as x (_ BitVec 8))");
    assert_eq!(name(&qi), b"x");
    assert_eq!(qi.sort.as_deref(), Some("(_ BitVec 8)"));
}

#[test]
fn qualified_applied_sort() {
    // the sort parser handles applied sorts inside `as` as well
    let qi = parse_all::<SmtQualifiedIdentParser<Printing>>(b"(as x (Array Int Int))");
    assert_eq!(name(&qi), b"x");
    assert_eq!(qi.sort.as_deref(), Some("(Array Int Int)"));
}

#[test]
fn errors() {
    let err = assert_error::<SmtQualifiedIdentParser<Printing>>(b"1", 0, 1);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedIdent), "{err:?}");

    // after `(` only `_` or `as` may follow
    let err = assert_error::<SmtQualifiedIdentParser<Printing>>(b"(f 1)", 1, 2);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedUnderscoreOrAs),
        "{err:?}"
    );

    // `as` must be followed by an identifier
    let err = assert_error::<SmtQualifiedIdentParser<Printing>>(b"(as)", 3, 4);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedIdent), "{err:?}");
    let err = assert_error::<SmtQualifiedIdentParser<Printing>>(b"(as 1 Bool)", 4, 5);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedIdent), "{err:?}");

    // ... and a sort
    let err = assert_error::<SmtQualifiedIdentParser<Printing>>(b"(as x)", 5, 6);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSort), "{err:?}");

    // ... and the closing parenthesis
    let err = assert_error::<SmtQualifiedIdentParser<Printing>>(b"(as x Bool z)", 11, 12);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );

    // EOF while waiting for the closing parenthesis
    let err = assert_error::<SmtQualifiedIdentParser<Printing>>(b"(as x Bool", 10, 10);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
}

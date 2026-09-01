//! Tests of the closed attribute parser.

use super::*;

type P = ClosedAttributeParser<Printing>;

#[test]
fn attribute_without_value() {
    assert_eq!(parse_all::<P>(b":produce-models)"), ":produce-models");
}

#[test]
fn attribute_with_value() {
    assert_eq!(parse_all::<P>(b":status sat)"), ":status sat");
    assert_eq!(parse_all::<P>(b":timeout 1000)"), ":timeout 1000");
    assert_eq!(parse_all::<P>(b":ratio 0.5)"), ":ratio 0.5");
    assert_eq!(parse_all::<P>(b":mask #xff)"), ":mask #xff");
    assert_eq!(parse_all::<P>(b":bits #b01)"), ":bits #b01");
    assert_eq!(parse_all::<P>(b":source \"me\")"), ":source \"me\"");
    assert_eq!(parse_all::<P>(b":name |a b|)"), ":name a b");
}

#[test]
fn stops_after_closing_paren() {
    let (attribute, left) = run::<P>(b":status sat) x").expect("valid");
    assert_eq!(attribute, ":status sat");
    assert_eq!(left, 1);
}

#[test]
fn errors() {
    let err = assert_error::<P>(b"status sat)", 0, 6);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword])
        ),
        "{err:?}"
    );

    let err = assert_error::<P>(b"", 0, 0);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword])
        ),
        "{err:?}"
    );

    // a keyword is not a valid value
    let err = assert_error::<P>(b":a :b)", 3, 5);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedAttribute),
        "{err:?}"
    );

    // only one value
    let err = assert_error::<P>(b":a 1 2)", 5, 6);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );

    // EOF after the value
    let err = assert_error::<P>(b":a 1", 4, 4);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
}

#[test]
fn attribute_with_s_expr_list_value() {
    assert_eq!(parse_all::<P>(b":pattern ((f x)))"), ":pattern ((f x))");
    // the empty list is a valid value
    assert_eq!(parse_all::<P>(b":a ())"), ":a ()");
    // every atom kind, including reserved words, is a valid element
    assert_eq!(
        parse_all::<P>(b":a (1 0.5 #xff #b01 \"s\" sym :kw let _ ()))"),
        ":a (1 0.5 #xff #b01 \"s\" sym :kw let _ ())"
    );
    assert_eq!(
        parse_all::<P>(b":a ((nested (deeper ())) atom))"),
        ":a ((nested (deeper ())) atom)"
    );
}

#[test]
fn s_expr_list_value_stops_after_closing_paren() {
    let (attribute, left) = run::<P>(b":a (x)) y").expect("valid");
    assert_eq!(attribute, ":a (x)");
    assert_eq!(left, 1);
}

#[test]
fn s_expr_list_value_errors() {
    // EOF inside the value list
    let err = assert_error::<P>(b":a (1", 5, 5);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedSExpr),
        "{err:?}"
    );

    // EOF after the value list, before the enclosing closing parenthesis
    let err = assert_error::<P>(b":a ()", 5, 5);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );

    // a second value after the list
    let err = assert_error::<P>(b":a () x)", 6, 7);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
}

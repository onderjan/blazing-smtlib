//! Tests of the closed attribute parser.

use super::*;

type P = SmtClosedAttributeParser<Printing>;

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
        matches!(err, SmtSyntaxErrorKind::ExpectedAttribute),
        "{err:?}"
    );

    let err = assert_error::<P>(b"", 0, 0);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedAttribute),
        "{err:?}"
    );

    // a keyword is not a valid value, and the single parser does not
    // accept it starting a second attribute either; the error must point
    // at the second keyword, not at the closing parenthesis
    let err = assert_error::<P>(b":a :b)", 3, 5);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );

    // a second attribute after a valued one is rejected at its keyword
    let err = assert_error::<P>(b":a 5 :b 6)", 5, 7);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );

    // only one value
    let err = assert_error::<P>(b":a 1 2)", 5, 6);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );

    // EOF after the value
    let err = assert_error::<P>(b":a 1", 4, 4);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
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
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSExpr), "{err:?}");

    // EOF after the value list, before the enclosing closing parenthesis
    let err = assert_error::<P>(b":a ()", 5, 5);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );

    // a second value after the list
    let err = assert_error::<P>(b":a () x)", 6, 7);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
}

// --- Multiple attributes ---

type MP = SmtClosedMultipleAttributeParser<Printing>;

#[test]
fn multiple_attributes() {
    assert_eq!(parse_all::<MP>(b":a)"), [":a"]);
    assert_eq!(parse_all::<MP>(b":a :b)"), [":a", ":b"]);
    assert_eq!(parse_all::<MP>(b":a 1 :b 2)"), [":a 1", ":b 2"]);
    // name-only next to valued, in both orders
    assert_eq!(parse_all::<MP>(b":a :b 2)"), [":a", ":b 2"]);
    assert_eq!(parse_all::<MP>(b":a 1 :b)"), [":a 1", ":b"]);
    assert_eq!(parse_all::<MP>(b":a :b :c)"), [":a", ":b", ":c"]);
}

#[test]
fn multiple_attributes_end_after_a_value() {
    // regression: the closing parenthesis must end the list directly
    // after a valued attribute, not just after a name-only one
    assert_eq!(parse_all::<MP>(b":named foo)"), [":named foo"]);
    assert_eq!(parse_all::<MP>(b":pattern ((f x)))"), [":pattern ((f x))"]);
}

#[test]
fn multiple_attributes_with_s_expr_values() {
    // keywords inside an s-expression value do not start a new attribute
    assert_eq!(parse_all::<MP>(b":a (x :k y) :b)"), [":a (x :k y)", ":b"]);
    assert_eq!(parse_all::<MP>(b":a () :b ())"), [":a ()", ":b ()"]);
}

#[test]
fn no_attributes_are_a_valid_empty_list() {
    // the parser itself is zero-to-multiple by design; grammar positions
    // that require at least one attribute check emptiness at the use site
    let attributes = parse_all::<MP>(b")");
    assert!(attributes.is_empty(), "{attributes:?}");
}

#[test]
fn multiple_attributes_stop_after_closing_paren() {
    let (attributes, left) = run::<MP>(b":a :b) :c").expect("valid");
    assert_eq!(attributes, [":a", ":b"]);
    assert_eq!(left, 1);
}

#[test]
fn multiple_attribute_parser_is_reusable() {
    let (first, second) = parse_two::<MP>(b":a 1) :b (x y) :c)");
    assert_eq!(first, [":a 1"]);
    assert_eq!(second, [":b (x y)", ":c"]);
}

#[test]
fn multiple_attribute_errors() {
    // the list must start with a keyword or the closing parenthesis
    let err = assert_error::<MP>(b"x)", 0, 1);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedAttribute),
        "{err:?}"
    );

    // a second value is rejected where the next attribute or the closing
    // parenthesis is expected
    let err = assert_error::<MP>(b":a 1 2)", 5, 6);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedAttribute),
        "{err:?}"
    );

    // EOF at the start of the list and EOF after an attribute name
    let err = assert_error::<MP>(b"", 0, 0);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedAttribute),
        "{err:?}"
    );
    let err = assert_error::<MP>(b":a", 2, 2);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedAttribute),
        "{err:?}"
    );
}

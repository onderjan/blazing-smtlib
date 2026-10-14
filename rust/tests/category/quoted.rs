//! Tests that a quoted symbol reaches the handler quoted, and an unquoted one
//! unquoted, at every place a symbol can stand: `Printing` renders a symbol
//! in pipes exactly when it arrives quoted. Every symbol below is quoted and
//! needs no quoting, so it would render without pipes if its flag were lost.

use super::*;

#[test]
fn sorts_keep_the_quoting_of_their_names_and_indices() {
    type P = SortParser;
    assert_eq!(parse_all::<P>(b"|S|"), "|S|");
    assert_eq!(parse_all::<P>(b"(|Array| |A| B)"), "(|Array| |A| B)");
    assert_eq!(parse_all::<P>(b"(_ |BitVec| 8)"), "(_ |BitVec| 8)");
    assert_eq!(parse_all::<P>(b"(_ |S| |i| j)"), "(_ |S| |i| j)");
}

#[test]
fn terms_keep_the_quoting_of_their_identifiers() {
    type P = TermParser;
    assert_eq!(parse_all::<P>(b"|x|"), "|x|");
    assert_eq!(parse_all::<P>(b"(|f| |x| y)"), "(|f| |x| y)");
    assert_eq!(parse_all::<P>(b"(_ |f| |i| 1)"), "(_ |f| |i| 1)");
    assert_eq!(parse_all::<P>(b"(as |x| |S|)"), "(as |x| |S|)");
}

#[test]
fn binders_keep_the_quoting_of_their_names() {
    type P = TermParser;
    assert_eq!(
        parse_all::<P>(b"(let ((|a| 1) (b 2)) |a|)"),
        "(let ((|a| 1) (b 2)) |a|)"
    );
    assert_eq!(
        parse_all::<P>(b"(forall ((|v| |S|) (w T)) |v|)"),
        "(forall ((|v| |S|) (w T)) |v|)"
    );
}

#[test]
fn patterns_keep_the_quoting_of_their_constructors_and_variables() {
    type P = TermParser;
    assert_eq!(
        parse_all::<P>(b"(match x (((|C| |y| z) |y|) (|D| 0) (|v| 1)))"),
        "(match x (((|C| |y| z) |y|) (|D| 0) (|v| 1)))"
    );
}

#[test]
fn s_expressions_and_attribute_values_keep_the_quoting_of_their_symbols() {
    assert_eq!(parse_all::<SExprParser>(b"(|a| b (|c|))"), "(|a| b (|c|))");
    assert_eq!(
        parse_all::<TermParser>(b"(! x :named |n|)"),
        "(! x :named |n|)"
    );
}

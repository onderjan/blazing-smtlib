//! Tests of the self-reset contract: after `progress` returns Break,
//! the same parser instance must parse the next element of its category.
//!
//! Every test drives one instance through two consecutive parses via
//! `parse_two`, deliberately ending the first parse in a state that a
//! missed reset would corrupt.

use super::*;

#[test]
fn ident_parser() {
    // the first parse ends inside index reading, where name and indices
    // must be left empty again
    let (first, second) = parse_two::<IdentParser>(b"(_ e 2) x");
    assert_eq!(render_ident(&first), "(_ e 2)");
    assert_eq!(render_ident(&second), "x");
}

#[test]
fn qualified_ident_parser() {
    // the first parse ends inside the qualified pair parser
    let (first, second) = parse_two::<QualifiedIdentParser>(b"(as x Bool) (_ f 2)");
    assert_eq!(render_qualified_ident(&first), "(as x Bool)");
    assert_eq!(render_qualified_ident(&second), "(_ f 2)");
}

#[test]
fn sort_parser() {
    // regression: a root sort that is only an indexed identifier once left
    // the parser in its ident-delegating state instead of resetting it
    let (first, second) = parse_two::<SortParser>(b"(_ BitVec 8) Bool");
    assert_eq!(first, "(_ BitVec 8)");
    assert_eq!(second, "Bool");

    let (first, second) = parse_two::<SortParser>(b"(Array Int Int) (_ BitVec 4)");
    assert_eq!(first, "(Array Int Int)");
    assert_eq!(second, "(_ BitVec 4)");
}

#[test]
fn term_parser() {
    // the first parse ends by closing a let, exercising the pending-term path
    let (first, second) = parse_two::<TermParser>(b"(let ((x 1)) x) (f y 2)");
    assert_eq!(first, "(let ((x 1)) x)");
    assert_eq!(second, "(f y 2)");

    // the first parse ends inside the delegated qualified-ident parser
    let (first, second) = parse_two::<TermParser>(b"((_ extract 3 0) y) 42");
    assert_eq!(first, "((_ extract 3 0) y)");
    assert_eq!(second, "42");
}

#[test]
fn s_expr_parser() {
    let (first, second) = parse_two::<SExprParser>(b"(a 1) b");
    assert_eq!(first, "(a 1)");
    assert_eq!(second, "b");
}

#[test]
fn attribute_parser() {
    // the first parse ends through the awaiting-close marker,
    // the second uses the retained s-expression list parser
    let (first, second) = parse_two::<ClosedAttributeParser>(b":a 1) :b (x y))");
    assert_eq!(first, ":a 1");
    assert_eq!(second, ":b (x y)");
}

#[test]
fn pair_parser() {
    // the stored first result must be moved out, not retained
    let (first, second) = parse_two::<PairParser<SymbolParser, SymbolParser>>(b"a b c d");
    assert_eq!(first.0.as_slice(), b"a");
    assert_eq!(first.1.as_slice(), b"b");
    assert_eq!(second.0.as_slice(), b"c");
    assert_eq!(second.1.as_slice(), b"d");
}

#[test]
fn closed_multiple_parser() {
    // the results vector is drained on break, not carried over
    let (first, second) = parse_two::<ClosedMultipleParser<SymbolParser>>(b"a b) c)");
    let first: Vec<&[u8]> = first.iter().map(|s| s.as_slice()).collect();
    let second: Vec<&[u8]> = second.iter().map(|s| s.as_slice()).collect();
    assert_eq!(first, [b"a" as &[u8], b"b"]);
    assert_eq!(second, [b"c" as &[u8]]);
}

#[test]
fn paren_parser() {
    let (first, second) = parse_two::<ParenParser<SymbolParser>>(b"(a) (b)");
    assert_eq!(first.as_slice(), b"a");
    assert_eq!(second.as_slice(), b"b");
}

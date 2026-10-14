//! Tests of reserved words in the category parsers: a quoted symbol spelled
//! like a reserved word is an ordinary symbol, while the unquoted word keeps
//! its role in the grammar.
//!
//! `Printing` renders a symbol quoted when it was written quoted, so the
//! expected strings tell such a symbol apart from the reserved word itself.

use super::*;

#[test]
fn s_expressions_tell_reserved_words_from_quoted_symbols() {
    assert_eq!(
        parse_all::<SExprParser>(b"(let |let| _ |_| ! |!| STRING |STRING| x |x|)"),
        "(let |let| _ |_| ! |!| STRING |STRING| x |x|)"
    );
}

#[test]
fn s_expressions_treat_command_names_as_reserved_words() {
    assert_eq!(
        parse_all::<SExprParser>(
            b"(assert |assert| check-sat-assuming |check-sat-assuming| pop |pop|)"
        ),
        "(assert |assert| check-sat-assuming |check-sat-assuming| pop |pop|)"
    );
}

#[test]
fn quoted_underscore_in_a_pattern_is_a_variable() {
    assert_eq!(
        parse_all::<TermParser>(b"(match l ((_ 0) (|_| 1) ((cons _ |_|) 2) ((|match| |let|) 3)))"),
        "(match l ((_ 0) (|_| 1) ((cons _ |_|) 2) ((|match| |let|) 3)))"
    );
}

#[test]
fn quoted_reserved_words_are_term_symbols() {
    type P = TermParser;
    assert_eq!(parse_all::<P>(b"|let|"), "|let|");
    assert_eq!(
        parse_all::<P>(b"(|let| |_| |!| |as|)"),
        "(|let| |_| |!| |as|)"
    );
    assert_eq!(
        parse_all::<P>(b"(let ((|let| 1)) |let|)"),
        "(let ((|let| 1)) |let|)"
    );
    assert_eq!(
        parse_all::<P>(b"(forall ((|forall| Int)) |forall|)"),
        "(forall ((|forall| Int)) |forall|)"
    );
    assert_eq!(
        parse_all::<P>(b"(lambda ((|lambda| Int)) |lambda|)"),
        "(lambda ((|lambda| Int)) |lambda|)"
    );
    assert_eq!(parse_all::<P>(b"(as |as| |par|)"), "(as |as| |par|)");
    assert_eq!(
        parse_all::<P>(b"((_ |_| |let| 1) x)"),
        "((_ |_| |let| 1) x)"
    );
    assert_eq!(parse_all::<P>(b"(! |!| :named |!|)"), "(! |!| :named |!|)");
}

#[test]
fn quoted_command_names_are_term_symbols() {
    assert_eq!(
        parse_all::<TermParser>(b"(|assert| |push| (_ |pop| |echo|))"),
        "(|assert| |push| (_ |pop| |echo|))"
    );
}

#[test]
fn quoted_reserved_words_are_sort_symbols() {
    type P = SortParser;
    assert_eq!(parse_all::<P>(b"|STRING|"), "|STRING|");
    assert_eq!(
        parse_all::<P>(b"(|par| |NUMERAL| (_ |_| 8) |set-logic|)"),
        "(|par| |NUMERAL| (_ |_| 8) |set-logic|)"
    );
}

#[test]
fn quoted_reserved_words_are_attribute_symbols() {
    assert_eq!(
        parse_all::<ClosedAttributeParser>(b":named |let|)"),
        ":named |let|"
    );
}

#[test]
fn unquoted_command_names_are_not_symbols() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    assert_error::<SymbolParser>(b"exit", 0, 4);
    assert_error::<TermParser>(b"assert", 0, 6);
    assert_error::<TermParser>(b"(f push)", 3, 7);
    assert_error::<TermParser>(b"(push 1)", 1, 5);
    assert_error::<SortParser>(b"(Array echo Int)", 7, 11);
    assert_error::<IdentParser>(b"(_ get-model 1)", 3, 12);
}

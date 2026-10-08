//! Public-API tests of the plain string-like value types.

use blazing_smtlib::{
    SmtBinDigitsBuf, SmtDecimalBuf, SmtHexDigitsBuf, SmtKeywordBuf, SmtNumeralBuf,
    SmtStringContentBuf, SmtSymbolBuf,
};

#[test]
fn string_content_accepts_any_printable_or_whitespace_bytes() {
    assert!(SmtStringContentBuf::is_allowed(b""));
    assert!(SmtStringContentBuf::is_allowed(
        b"a-simple-symbol~!@$%^&*_-+=<>.?/"
    ));
    assert!(SmtStringContentBuf::is_allowed(
        b"A quick brown fox jumps over a lazy dog."
    ));
    // any non-ASCII bytes are allowed, whether or not they form UTF-8
    assert!(SmtStringContentBuf::is_allowed(
        "Příšerně žluťoučký kůň úpěl ďábelské ódy.".as_bytes()
    ));
    assert!(SmtStringContentBuf::is_allowed(b"\xFF"));
    // unlike symbols, string content may contain pipes and backslashes
    assert!(SmtStringContentBuf::is_allowed(b"a|b"));
    assert!(SmtStringContentBuf::is_allowed(b"a\\b"));
}

#[test]
fn symbol_accepts_everything_a_string_does_except_pipe_and_backslash() {
    assert!(SmtSymbolBuf::is_allowed(b""));
    assert!(SmtSymbolBuf::is_allowed(
        b"a-simple-symbol~!@$%^&*_-+=<>.?/"
    ));
    assert!(SmtSymbolBuf::is_allowed(
        b"A quick brown fox jumps over a lazy dog."
    ));
    assert!(SmtSymbolBuf::is_allowed(
        "Příšerně žluťoučký kůň úpěl ďábelské ódy.".as_bytes()
    ));
    assert!(SmtSymbolBuf::is_allowed(b"\xFF"));

    assert!(!SmtSymbolBuf::is_allowed(b"a|b"));
    assert!(!SmtSymbolBuf::is_allowed(b"a\\b"));
}

#[test]
fn keyword_accepts_only_nonempty_simple_symbol_bytes() {
    assert!(SmtKeywordBuf::is_allowed(
        b"a-simple-symbol~!@$%^&*_-+=<>.?/"
    ));
    assert!(SmtKeywordBuf::is_allowed(b"quick"));
    // unlike a simple symbol, a keyword may spell a reserved word
    // and may start with a digit
    assert!(SmtKeywordBuf::is_allowed(b"let"));
    assert!(SmtKeywordBuf::is_allowed(b"0"));
    assert!(SmtKeywordBuf::is_allowed(b"56"));
    assert!(SmtKeywordBuf::is_allowed(b"0abc"));

    assert!(!SmtKeywordBuf::is_allowed(b""));
    // no whitespace, UTF-8, or non-UTF-8 bytes, unlike strings and symbols
    assert!(!SmtKeywordBuf::is_allowed(
        b"A quick brown fox jumps over a lazy dog."
    ));
    assert!(!SmtKeywordBuf::is_allowed(
        "Příšerně žluťoučký kůň úpěl ďábelské ódy.".as_bytes()
    ));
    assert!(!SmtKeywordBuf::is_allowed("žluťoučký".as_bytes()));
    assert!(!SmtKeywordBuf::is_allowed(b"\xFF"));
}

#[test]
fn del_is_rejected_everywhere() {
    assert!(!SmtStringContentBuf::is_allowed(b"a\x7Fb"));
    assert!(!SmtSymbolBuf::is_allowed(b"a\x7Fb"));
    assert!(!SmtKeywordBuf::is_allowed(b"a\x7Fb"));
}

#[test]
fn digit_kinds_reject_the_empty_string_and_accept_zero() {
    assert!(!SmtNumeralBuf::is_allowed(b""));
    assert!(!SmtHexDigitsBuf::is_allowed(b""));
    assert!(!SmtBinDigitsBuf::is_allowed(b""));

    assert!(SmtNumeralBuf::is_allowed(b"0"));
    assert!(SmtHexDigitsBuf::is_allowed(b"0"));
    assert!(SmtBinDigitsBuf::is_allowed(b"0"));
}

#[test]
fn only_numeral_rejects_leading_zeros() {
    assert!(!SmtNumeralBuf::is_allowed(b"00"));
    assert!(!SmtNumeralBuf::is_allowed(b"01"));
    assert!(SmtHexDigitsBuf::is_allowed(b"00"));
    assert!(SmtHexDigitsBuf::is_allowed(b"01"));
    assert!(SmtBinDigitsBuf::is_allowed(b"00"));
    assert!(SmtBinDigitsBuf::is_allowed(b"01"));
}

#[test]
fn numeral_accepts_numbers_without_leading_zeros() {
    assert!(SmtNumeralBuf::is_allowed(b"10"));
    assert!(SmtNumeralBuf::is_allowed(b"1024"));
    assert!(SmtNumeralBuf::is_allowed(b"70"));
}

#[test]
fn digit_kinds_accept_only_their_own_digits() {
    assert!(SmtHexDigitsBuf::is_allowed(b"1024"));
    assert!(SmtHexDigitsBuf::is_allowed(b"077"));
    assert!(SmtHexDigitsBuf::is_allowed(b"aF"));
    assert!(!SmtHexDigitsBuf::is_allowed(b"g"));
    assert!(!SmtHexDigitsBuf::is_allowed(b"G"));

    assert!(SmtBinDigitsBuf::is_allowed(b"01101"));
    assert!(!SmtBinDigitsBuf::is_allowed(b"077"));
    assert!(!SmtBinDigitsBuf::is_allowed(b"aF"));
}

#[test]
fn decimals_require_one_dot_between_digit_parts() {
    assert!(SmtDecimalBuf::is_allowed(b"0.0"));
    assert!(SmtDecimalBuf::is_allowed(b"7.5"));
    assert!(SmtDecimalBuf::is_allowed(b"10.25"));

    // the leading-zero restriction applies only to the whole part
    assert!(!SmtDecimalBuf::is_allowed(b"01.5"));
    assert!(SmtDecimalBuf::is_allowed(b"0.5"));
    assert!(SmtDecimalBuf::is_allowed(b"1.05"));
    assert!(SmtDecimalBuf::is_allowed(b"1.00"));
    assert!(SmtDecimalBuf::is_allowed(b"1.500"));

    // both parts and the dot must be present
    assert!(!SmtDecimalBuf::is_allowed(b""));
    assert!(!SmtDecimalBuf::is_allowed(b"1"));
    assert!(!SmtDecimalBuf::is_allowed(b"1."));
    assert!(!SmtDecimalBuf::is_allowed(b".5"));
    assert!(!SmtDecimalBuf::is_allowed(b"."));

    // only a single dot is allowed
    assert!(!SmtDecimalBuf::is_allowed(b"1.2.3"));
    assert!(!SmtDecimalBuf::is_allowed(b"1..2"));

    // nothing but digits around the dot
    assert!(!SmtDecimalBuf::is_allowed(b"a.5"));
    assert!(!SmtDecimalBuf::is_allowed(b"1.5a"));
    assert!(!SmtDecimalBuf::is_allowed(b"-1.5"));
    assert!(!SmtDecimalBuf::is_allowed(b"1. 5"));
}

#[test]
fn decimals_with_trailing_fractional_zeros_are_distinct() {
    fn dec(value: &[u8]) -> SmtDecimalBuf {
        SmtDecimalBuf::new(value.to_vec()).expect("test decimal should be allowed")
    }

    // SMT-LIB does not consider '3.50' an overlong encoding of '3.5',
    // but as two separate things syntactically
    assert_ne!(dec(b"1.0"), dec(b"1.0000"));
    assert_ne!(dec(b"3.5"), dec(b"3.50"));
    assert_eq!(dec(b"3.50"), dec(b"3.50"));
}

#[test]
fn owned_newtypes_key_maps_looked_up_by_bytes() {
    use std::collections::HashMap;

    let mut map: HashMap<SmtSymbolBuf, u32> = HashMap::new();
    map.insert(SmtSymbolBuf::new(b"x".to_vec()).expect("a symbol"), 1);
    map.insert(
        SmtSymbolBuf::new(b"quoted name".to_vec()).expect("a symbol"),
        2,
    );
    assert_eq!(map.get(b"x".as_slice()), Some(&1));
    assert_eq!(map.get(b"quoted name".as_slice()), Some(&2));
    assert_eq!(map.get(b"y".as_slice()), None);
}

#[test]
fn newtypes_compare_with_bytes_strings_and_each_other() {
    let owned = SmtSymbolBuf::new(b"bvadd".to_vec()).expect("a symbol");
    let view = owned.as_view();
    assert!(owned == "bvadd" && owned == b"bvadd"[..] && owned == b"bvadd".as_slice());
    assert!(view == "bvadd" && view == b"bvadd"[..] && view == b"bvadd".as_slice());
    assert!(owned == view);
    assert!(view == owned);
    assert!(owned != "bvsub" && view != "bvsub");
    let numeral = SmtNumeralBuf::new(b"32".to_vec()).expect("a numeral");
    assert!(numeral == "32" && numeral.as_view() == "32" && numeral != "3");
}

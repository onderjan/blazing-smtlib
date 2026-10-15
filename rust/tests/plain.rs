//! Public-API tests of the plain string-like value types.

use blazing_smtlib::{
    SmtBinDigitsBuf, SmtBytesBuf, SmtDecimalBuf, SmtHexDigitsBuf, SmtKeywordBuf, SmtNumeral,
    SmtNumeralBuf, SmtNumeralOverflow, SmtStringContentBuf, SmtSymbolBuf,
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
fn quoted_symbol_accepts_everything_a_string_does_except_pipe_and_backslash() {
    assert!(SmtSymbolBuf::is_quoted_allowed(b""));
    assert!(SmtSymbolBuf::is_quoted_allowed(
        b"a-simple-symbol~!@$%^&*_-+=<>.?/"
    ));
    assert!(SmtSymbolBuf::is_quoted_allowed(
        b"A quick brown fox jumps over a lazy dog."
    ));
    assert!(SmtSymbolBuf::is_quoted_allowed(
        "Příšerně žluťoučký kůň úpěl ďábelské ódy.".as_bytes()
    ));
    assert!(SmtSymbolBuf::is_quoted_allowed(b"\xFF"));
    assert!(SmtSymbolBuf::is_quoted_allowed(b"0abc"));

    assert!(!SmtSymbolBuf::is_quoted_allowed(b"a|b"));
    assert!(!SmtSymbolBuf::is_quoted_allowed(b"a\\b"));
}

#[test]
fn unquoted_symbol_accepts_only_nonempty_simple_symbol_bytes_not_starting_with_a_digit() {
    assert!(SmtSymbolBuf::is_unquoted_allowed(
        b"a-simple-symbol~!@$%^&*_-+=<>.?/"
    ));
    assert!(SmtSymbolBuf::is_unquoted_allowed(b"x0"));
    // whether a word is reserved depends on the version, which a symbol
    // does not know
    assert!(SmtSymbolBuf::is_unquoted_allowed(b"let"));

    assert!(!SmtSymbolBuf::is_unquoted_allowed(b""));
    assert!(!SmtSymbolBuf::is_unquoted_allowed(b"0"));
    assert!(!SmtSymbolBuf::is_unquoted_allowed(b"0abc"));
    assert!(!SmtSymbolBuf::is_unquoted_allowed(b"quoted name"));
    assert!(!SmtSymbolBuf::is_unquoted_allowed("žluťoučký".as_bytes()));
    assert!(!SmtSymbolBuf::is_unquoted_allowed(b"\xFF"));
    assert!(!SmtSymbolBuf::is_unquoted_allowed(b"a|b"));
    assert!(!SmtSymbolBuf::is_unquoted_allowed(b"a\\b"));
}

#[test]
fn a_symbol_is_built_quoted_or_unquoted_under_its_own_rule() {
    let quoted = SmtSymbolBuf::new_quoted(b"quoted name".to_vec()).expect("a quoted symbol");
    assert!(quoted.is_quoted() && quoted.as_view().is_quoted());
    let unquoted = SmtSymbolBuf::new_unquoted(b"x".to_vec()).expect("an unquoted symbol");
    assert!(!unquoted.is_quoted() && !unquoted.as_view().is_quoted());
    assert!(SmtSymbolBuf::new_quoted(b"".to_vec()).is_ok());
    assert!(SmtSymbolBuf::new_unquoted(b"quoted name".to_vec()).is_err());
    assert!(SmtSymbolBuf::new_unquoted(b"".to_vec()).is_err());
    // the flag survives into the view and back
    assert!(quoted.as_view().into_owned().is_quoted());
    assert!(!unquoted.as_view().into_owned().is_quoted());
}

#[test]
fn a_symbol_prints_its_pipes_when_debugged() {
    let quoted = SmtSymbolBuf::new_quoted(b"a b".to_vec()).expect("a quoted symbol");
    let unquoted = SmtSymbolBuf::new_unquoted(b"ab".to_vec()).expect("an unquoted symbol");
    assert_eq!(format!("{quoted:?}"), "|\"a b\"|");
    assert_eq!(format!("{:?}", quoted.as_view()), "|\"a b\"|");
    assert_eq!(format!("{unquoted:?}"), "\"ab\"");
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
    assert!(!SmtSymbolBuf::is_quoted_allowed(b"a\x7Fb"));
    assert!(!SmtSymbolBuf::is_unquoted_allowed(b"a\x7Fb"));
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
fn symbols_key_maps_by_their_bytes_whether_quoted_or_not() {
    use std::collections::HashMap;

    // a symbol is the same symbol quoted or not, so its bytes are the key
    let mut map: HashMap<SmtBytesBuf, u32> = HashMap::new();
    let x = SmtSymbolBuf::new_unquoted(b"x".to_vec()).expect("a symbol");
    map.insert(x.into_bytes_buf(), 1);
    let name = SmtSymbolBuf::new_quoted(b"quoted name".to_vec()).expect("a symbol");
    map.insert(name.into_bytes_buf(), 2);
    let quoted_x = SmtSymbolBuf::new_quoted(b"x".to_vec()).expect("a symbol");
    assert_eq!(map.get(quoted_x.as_slice()), Some(&1));
    assert_eq!(map.get(quoted_x.as_view().as_slice()), Some(&1));
    assert_eq!(map.get(b"quoted name".as_slice()), Some(&2));
    assert_eq!(map.get(b"y".as_slice()), None);
    // and the bytes compare equal across the two spellings
    let unquoted_x = SmtSymbolBuf::new_unquoted(b"x".to_vec()).expect("a symbol");
    assert_eq!(quoted_x.bytes(), unquoted_x.bytes());
    assert_eq!(quoted_x.as_view().bytes(), unquoted_x.as_view().bytes());
}

#[test]
fn newtypes_compare_with_bytes_strings_and_each_other() {
    let owned = SmtNumeralBuf::new(b"32".to_vec()).expect("a numeral");
    let view = owned.as_view();
    assert!(owned == "32" && owned == b"32"[..] && owned == b"32".as_slice());
    assert!(view == "32" && view == b"32"[..] && view == b"32".as_slice());
    assert!(owned == view);
    assert!(view == owned);
    assert!(owned != "3" && view != "3");
}

/// The conversions of a numeral into one integer type, widened to `u128` so
/// that one property covers every type.
struct NumeralConversions {
    name: &'static str,
    max: u128,
    buf_to: fn(&SmtNumeralBuf) -> Option<u128>,
    view_to: fn(SmtNumeral<'_>) -> Option<u128>,
    buf_try_from: fn(&SmtNumeralBuf) -> Result<u128, SmtNumeralOverflow>,
    view_try_from: fn(SmtNumeral<'_>) -> Result<u128, SmtNumeralOverflow>,
    from_method: fn(u128) -> SmtNumeralBuf,
    from_trait: fn(u128) -> SmtNumeralBuf,
}

/// Widens a value of any of the converted integer types to `u128`.
fn widen<T: TryInto<u128>>(value: T) -> u128 {
    value
        .try_into()
        .unwrap_or_else(|_| panic!("every converted integer type fits into u128"))
}

/// Narrows a `u128` known to fit into the integer type.
fn narrow<T: TryFrom<u128>>(value: u128) -> T {
    T::try_from(value).unwrap_or_else(|_| panic!("{value} should fit into the integer type"))
}

macro_rules! numeral_conversions {
    ($int:ty, $to:ident, $from:ident) => {
        NumeralConversions {
            name: stringify!($int),
            max: widen(<$int>::MAX),
            buf_to: |numeral| numeral.$to().map(widen),
            view_to: |numeral| numeral.$to().map(widen),
            buf_try_from: |numeral| <$int>::try_from(numeral).map(widen),
            view_try_from: |numeral| <$int>::try_from(numeral).map(widen),
            from_method: |value| SmtNumeralBuf::$from(narrow::<$int>(value)),
            from_trait: |value| SmtNumeralBuf::from(narrow::<$int>(value)),
        }
    };
}

fn all_numeral_conversions() -> [NumeralConversions; 4] {
    [
        numeral_conversions!(u32, to_u32, from_u32),
        numeral_conversions!(u64, to_u64, from_u64),
        numeral_conversions!(u128, to_u128, from_u128),
        numeral_conversions!(usize, to_usize, from_usize),
    ]
}

fn numeral(digits: &str) -> SmtNumeralBuf {
    SmtNumeralBuf::new(digits.as_bytes().to_vec()).expect("test numeral should be allowed")
}

/// Every conversion of the numeral into the integer type, owned and viewed,
/// by method and by `TryFrom`; all must agree.
fn convert(conversions: &NumeralConversions, digits: &str) -> Option<u128> {
    let owned = numeral(digits);
    let by_method = (conversions.buf_to)(&owned);
    assert_eq!(
        (conversions.view_to)(owned.as_view()),
        by_method,
        "{} view of {digits}",
        conversions.name
    );
    assert_eq!(
        (conversions.buf_try_from)(&owned),
        by_method.ok_or(SmtNumeralOverflow),
        "{} TryFrom of the owned {digits}",
        conversions.name
    );
    assert_eq!(
        (conversions.view_try_from)(owned.as_view()),
        by_method.ok_or(SmtNumeralOverflow),
        "{} TryFrom of the viewed {digits}",
        conversions.name
    );
    by_method
}

#[test]
fn a_numeral_converts_into_an_integer_type_exactly_when_it_fits() {
    // one more than the largest u128, which no type here holds
    const ABOVE_U128: &str = "340282366920938463463374607431768211456";
    for conversions in all_numeral_conversions() {
        let name = conversions.name;
        let max = conversions.max;
        for value in [0, 1, 9, 10, 42, max - 1, max] {
            assert_eq!(
                convert(&conversions, &value.to_string()),
                Some(value),
                "{name} of {value}"
            );
        }
        let above_max = max
            .checked_add(1)
            .map_or(ABOVE_U128.to_string(), |above| above.to_string());
        for digits in [
            above_max.as_str(),
            ABOVE_U128,
            "100000000000000000000000000000000000000000000000000",
        ] {
            assert_eq!(convert(&conversions, digits), None, "{name} of {digits}");
        }
    }
}

#[test]
fn a_numeral_built_from_an_integer_is_its_decimal_spelling_and_converts_back() {
    for conversions in all_numeral_conversions() {
        let name = conversions.name;
        let max = conversions.max;
        for value in [0, 1, 9, 10, 42, max - 1, max] {
            for built in [
                (conversions.from_method)(value),
                (conversions.from_trait)(value),
            ] {
                assert!(
                    SmtNumeralBuf::is_allowed(built.as_slice()),
                    "{name} {value} built as {built:?}"
                );
                assert_eq!(built, value.to_string().as_str(), "{name} {value}");
                assert_eq!((conversions.buf_to)(&built), Some(value), "{name} {value}");
            }
        }
    }
}

#[test]
fn a_decimal_splits_at_its_dot_into_a_whole_numeral_and_fraction_digits() {
    for (decimal, whole, fraction) in [
        ("0.0", "0", &b"0"[..]),
        ("7.5", "7", b"5"),
        ("10.050", "10", b"050"),
        ("1.00", "1", b"00"),
        ("123.0001", "123", b"0001"),
    ] {
        let owned = SmtDecimalBuf::new(decimal.as_bytes().to_vec()).expect("a decimal");
        let view = owned.as_view();
        assert_eq!(owned.whole(), whole, "whole part of the owned {decimal}");
        assert_eq!(view.whole(), whole, "whole part of the viewed {decimal}");
        assert_eq!(
            owned.fraction(),
            fraction,
            "fraction of the owned {decimal}"
        );
        assert_eq!(
            view.fraction(),
            fraction,
            "fraction of the viewed {decimal}"
        );
        // the whole part is a numeral, with the conversions of one
        assert_eq!(
            view.whole().to_u32(),
            Some(whole.parse().expect("the whole part is a number")),
            "{decimal}"
        );
    }
}

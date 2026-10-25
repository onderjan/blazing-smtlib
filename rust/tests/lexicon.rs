//! Public-API tests of the plain string-like value types.

use blazing_smtlib::{
    lexicon::{
        SmtBinDigits, SmtBinDigitsBuf, SmtBytesBuf, SmtComment, SmtCommentBuf, SmtDecimal,
        SmtDecimalBuf, SmtDisallowedBytesError, SmtHexDigits, SmtHexDigitsBuf, SmtKeyword,
        SmtKeywordBuf, SmtNumeral, SmtNumeralBuf, SmtNumericOverflow, SmtStringContent,
        SmtStringContentBuf, SmtSymbol, SmtSymbolBuf, SmtWhitespace, SmtWhitespaceBuf,
    },
    version::SmtVersion,
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
    assert!(quoted.is_quoted() && quoted.view().is_quoted());
    let unquoted = SmtSymbolBuf::new_unquoted(b"x".to_vec()).expect("an unquoted symbol");
    assert!(!unquoted.is_quoted() && !unquoted.view().is_quoted());
    assert!(SmtSymbolBuf::new_quoted(b"".to_vec()).is_ok());
    assert!(SmtSymbolBuf::new_unquoted(b"quoted name".to_vec()).is_err());
    assert!(SmtSymbolBuf::new_unquoted(b"".to_vec()).is_err());
    // the flag survives into the view and back
    assert!(quoted.view().into_owned().is_quoted());
    assert!(!unquoted.view().into_owned().is_quoted());
}

#[test]
fn a_symbol_prints_its_pipes_when_debugged() {
    let quoted = SmtSymbolBuf::new_quoted(b"a b".to_vec()).expect("a quoted symbol");
    let unquoted = SmtSymbolBuf::new_unquoted(b"ab".to_vec()).expect("an unquoted symbol");
    assert_eq!(format!("{quoted:?}"), "|\"a b\"|");
    assert_eq!(format!("{:?}", quoted.view()), "|\"a b\"|");
    assert_eq!(format!("{unquoted:?}"), "\"ab\"");
}

/// Bytes that every check below is tried on: some allowed by each plain type,
/// some by none.
const SAMPLES: &[&[u8]] = &[
    b"", b"0", b"00", b"12", b"1.5", b"1F", b"01", b"x", b"let", b"a b", b"a|b", b"a\\b", b"\xFF",
    b"a\x7Fb", b" \n", b"; c\n", b"\r\n", b"-",
];

/// Each plain view is built from borrowed bytes exactly when its owned type
/// allows them, and then borrows those very bytes.
#[test]
fn a_plain_view_is_built_from_borrowed_bytes_under_its_owned_rule() {
    macro_rules! check {
        ($view:ident, $buf:ident) => {
            for &sample in SAMPLES {
                match $view::new(sample) {
                    Ok(view) => {
                        assert!($buf::is_allowed(sample), "{} {sample:?}", stringify!($view));
                        assert!(std::ptr::eq(view.as_slice(), sample));
                    }
                    Err(SmtDisallowedBytesError) => {
                        assert!(
                            !$buf::is_allowed(sample),
                            "{} {sample:?}",
                            stringify!($view)
                        );
                    }
                }
            }
        };
    }
    check!(SmtStringContent, SmtStringContentBuf);
    check!(SmtKeyword, SmtKeywordBuf);
    check!(SmtNumeral, SmtNumeralBuf);
    check!(SmtHexDigits, SmtHexDigitsBuf);
    check!(SmtBinDigits, SmtBinDigitsBuf);
    check!(SmtDecimal, SmtDecimalBuf);
    check!(SmtWhitespace, SmtWhitespaceBuf);
    check!(SmtComment, SmtCommentBuf);
}

/// A symbol view is built quoted or unquoted from borrowed bytes exactly when
/// the owned symbol's rule for that form allows them.
#[test]
fn a_symbol_view_is_built_quoted_or_unquoted_under_its_own_rule() {
    for &sample in SAMPLES {
        match SmtSymbol::new_unquoted(sample) {
            Ok(symbol) => {
                assert!(SmtSymbolBuf::is_unquoted_allowed(sample), "{sample:?}");
                assert!(!symbol.is_quoted() && std::ptr::eq(symbol.as_slice(), sample));
            }
            Err(SmtDisallowedBytesError) => {
                assert!(!SmtSymbolBuf::is_unquoted_allowed(sample), "{sample:?}")
            }
        }
        match SmtSymbol::new_quoted(sample) {
            Ok(symbol) => {
                assert!(SmtSymbolBuf::is_quoted_allowed(sample), "{sample:?}");
                assert!(symbol.is_quoted() && std::ptr::eq(symbol.as_slice(), sample));
            }
            Err(SmtDisallowedBytesError) => {
                assert!(!SmtSymbolBuf::is_quoted_allowed(sample), "{sample:?}")
            }
        }
    }
}

const VERSIONS: [SmtVersion; 4] = [
    SmtVersion::V2_0,
    SmtVersion::V2_5,
    SmtVersion::V2_6,
    SmtVersion::V2_7,
];

/// Whether `match`, `lambda` and `_` are reserved words of each version.
fn reserved_in(word: &[u8], version: SmtVersion) -> bool {
    match word {
        b"match" => matches!(version, SmtVersion::V2_6 | SmtVersion::V2_7),
        b"lambda" => version == SmtVersion::V2_7,
        b"_" => true,
        _ => false,
    }
}

/// A symbol built for a version is simple if its bytes are allowed in a simple
/// symbol and are not a reserved word of the version, quoted if they are
/// allowed only quoted, and refused if they are allowed in neither.
#[test]
fn a_symbol_built_for_a_version_is_simple_unless_it_would_not_read_back() {
    for version in VERSIONS {
        for word in [&b"x"[..], b"match", b"lambda", b"_"] {
            let simple = !reserved_in(word, version);
            assert_eq!(
                SmtSymbolBuf::is_unquoted_allowed_in(word, version),
                simple,
                "{word:?} in {version:?}"
            );
            let view = SmtSymbol::new(word, version).expect("allowed bytes");
            let owned = SmtSymbolBuf::new(word.to_vec(), version).expect("allowed bytes");
            assert_eq!(view.is_quoted(), !simple, "{word:?} in {version:?}");
            assert_eq!(owned.is_quoted(), !simple, "{word:?} in {version:?}");
            assert!(view.as_slice() == word && owned.as_slice() == word);
        }
        // allowed only quoted
        for word in [&b"1x"[..], b"a b", b""] {
            assert!(!SmtSymbolBuf::is_unquoted_allowed_in(word, version));
            assert!(SmtSymbol::new(word, version).expect("quotable").is_quoted());
            let owned = SmtSymbolBuf::new(word.to_vec(), version).expect("quotable");
            assert!(owned.is_quoted());
        }
        // allowed in neither form
        assert_eq!(
            SmtSymbol::new(b"a|b", version).err(),
            Some(SmtDisallowedBytesError)
        );
        let refused = SmtSymbolBuf::new(b"a|b".to_vec(), version).expect_err("not quotable");
        assert_eq!(refused.into_vec(), b"a|b");
    }
}

/// A symbol is allowed in a version unless it is simple and a reserved word
/// there; making it versioned quotes exactly such a symbol and never unquotes.
#[test]
fn a_versioned_symbol_is_quoted_exactly_where_it_would_not_read_back() {
    for version in VERSIONS {
        for word in [&b"x"[..], b"match", b"lambda", b"_"] {
            let reserved = reserved_in(word, version);
            let simple = SmtSymbol::new_unquoted(word).expect("a simple symbol");
            let quoted = SmtSymbol::new_quoted(word).expect("a quoted symbol");
            assert_eq!(
                simple.is_allowed_in(version),
                !reserved,
                "{word:?} in {version:?}"
            );
            assert!(quoted.is_allowed_in(version), "{word:?} in {version:?}");
            assert_eq!(simple.into_versioned(version).is_quoted(), reserved);
            assert!(quoted.into_versioned(version).is_quoted());
            assert!(simple.into_versioned(version).is_allowed_in(version));
            assert_eq!(simple.into_versioned(version).as_slice(), word);

            let simple = simple.into_owned();
            let quoted = quoted.into_owned();
            assert_eq!(
                simple.is_allowed_in(version),
                !reserved,
                "{word:?} in {version:?}"
            );
            assert!(quoted.is_allowed_in(version), "{word:?} in {version:?}");
            let versioned = simple.into_versioned(version);
            assert_eq!(versioned.is_quoted(), reserved, "{word:?} in {version:?}");
            assert!(versioned.is_allowed_in(version) && versioned.as_slice() == word);
            assert!(quoted.into_versioned(version).is_quoted());
        }
    }
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
    assert_eq!(map.get(quoted_x.view().as_slice()), Some(&1));
    assert_eq!(map.get(b"quoted name".as_slice()), Some(&2));
    assert_eq!(map.get(b"y".as_slice()), None);
    // and the bytes compare equal across the two spellings
    let unquoted_x = SmtSymbolBuf::new_unquoted(b"x".to_vec()).expect("a symbol");
    assert_eq!(quoted_x.bytes(), unquoted_x.bytes());
    assert_eq!(quoted_x.view().bytes(), unquoted_x.view().bytes());
}

#[test]
fn newtypes_compare_with_bytes_strings_and_each_other() {
    let owned = SmtNumeralBuf::new(b"32".to_vec()).expect("a numeral");
    let view = owned.view();
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
    buf_try_from: fn(&SmtNumeralBuf) -> Result<u128, SmtNumericOverflow>,
    view_try_from: fn(SmtNumeral<'_>) -> Result<u128, SmtNumericOverflow>,
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
        (conversions.view_to)(owned.view()),
        by_method,
        "{} view of {digits}",
        conversions.name
    );
    assert_eq!(
        (conversions.buf_try_from)(&owned),
        by_method.ok_or(SmtNumericOverflow),
        "{} TryFrom of the owned {digits}",
        conversions.name
    );
    assert_eq!(
        (conversions.view_try_from)(owned.view()),
        by_method.ok_or(SmtNumericOverflow),
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
        let view = owned.view();
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

/// The conversions of hexadecimal and binary digits into one integer type,
/// owned and viewed, by method and by `TryFrom`, widened to `u128`.
struct DigitConversions {
    name: &'static str,
    max: u128,
    hex_buf: fn(&SmtHexDigitsBuf) -> Option<u128>,
    hex_view: fn(SmtHexDigits<'_>) -> Option<u128>,
    hex_buf_try_from: fn(&SmtHexDigitsBuf) -> Result<u128, SmtNumericOverflow>,
    hex_view_try_from: fn(SmtHexDigits<'_>) -> Result<u128, SmtNumericOverflow>,
    bin_buf: fn(&SmtBinDigitsBuf) -> Option<u128>,
    bin_view: fn(SmtBinDigits<'_>) -> Option<u128>,
    bin_buf_try_from: fn(&SmtBinDigitsBuf) -> Result<u128, SmtNumericOverflow>,
    bin_view_try_from: fn(SmtBinDigits<'_>) -> Result<u128, SmtNumericOverflow>,
}

macro_rules! digit_conversions {
    ($int:ty, $to:ident) => {
        DigitConversions {
            name: stringify!($int),
            max: widen(<$int>::MAX),
            hex_buf: |digits| digits.$to().map(widen),
            hex_view: |digits| digits.$to().map(widen),
            hex_buf_try_from: |digits| <$int>::try_from(digits).map(widen),
            hex_view_try_from: |digits| <$int>::try_from(digits).map(widen),
            bin_buf: |digits| digits.$to().map(widen),
            bin_view: |digits| digits.$to().map(widen),
            bin_buf_try_from: |digits| <$int>::try_from(digits).map(widen),
            bin_view_try_from: |digits| <$int>::try_from(digits).map(widen),
        }
    };
}

fn all_digit_conversions() -> [DigitConversions; 4] {
    [
        digit_conversions!(u32, to_u32),
        digit_conversions!(u64, to_u64),
        digit_conversions!(u128, to_u128),
        digit_conversions!(usize, to_usize),
    ]
}

/// Converts the hexadecimal digits owned and viewed, by method and by
/// `TryFrom`; all must agree.
fn convert_hex(conversions: &DigitConversions, digits: &str) -> Option<u128> {
    let owned = SmtHexDigitsBuf::new(digits.as_bytes().to_vec())
        .expect("test hexadecimal digits should be allowed");
    let value = (conversions.hex_buf)(&owned);
    let name = conversions.name;
    assert_eq!(
        (conversions.hex_view)(owned.view()),
        value,
        "{name} view of #x{digits}"
    );
    let by_try_from = value.ok_or(SmtNumericOverflow);
    assert_eq!(
        (conversions.hex_buf_try_from)(&owned),
        by_try_from,
        "{name} TryFrom of the owned #x{digits}"
    );
    assert_eq!(
        (conversions.hex_view_try_from)(owned.view()),
        by_try_from,
        "{name} TryFrom of the viewed #x{digits}"
    );
    value
}

/// Converts the binary digits owned and viewed, by method and by `TryFrom`;
/// all must agree.
fn convert_bin(conversions: &DigitConversions, digits: &str) -> Option<u128> {
    let owned = SmtBinDigitsBuf::new(digits.as_bytes().to_vec())
        .expect("test binary digits should be allowed");
    let value = (conversions.bin_buf)(&owned);
    let name = conversions.name;
    assert_eq!(
        (conversions.bin_view)(owned.view()),
        value,
        "{name} view of #b{digits}"
    );
    let by_try_from = value.ok_or(SmtNumericOverflow);
    assert_eq!(
        (conversions.bin_buf_try_from)(&owned),
        by_try_from,
        "{name} TryFrom of the owned #b{digits}"
    );
    assert_eq!(
        (conversions.bin_view_try_from)(owned.view()),
        by_try_from,
        "{name} TryFrom of the viewed #b{digits}"
    );
    value
}

/// Digits convert by their value: leading zeros add nothing, and the
/// conversion fails exactly when the value does not fit, however many
/// digits spell it.
#[test]
fn digits_convert_into_an_integer_type_exactly_when_their_value_fits() {
    let zeros = "0".repeat(200);
    for conversions in all_digit_conversions() {
        let name = conversions.name;
        let max = conversions.max;
        for value in [0, 1, 9, 10, 15, 16, 42, 255, max - 1, max] {
            let lower = format!("{value:x}");
            let upper = format!("{value:X}");
            let binary = format!("{value:b}");
            for hex in [&lower, &upper, &format!("{zeros}{lower}")] {
                assert_eq!(
                    convert_hex(&conversions, hex),
                    Some(value),
                    "{name} of #x{hex}"
                );
            }
            for bin in [&binary, &format!("{zeros}{binary}")] {
                assert_eq!(
                    convert_bin(&conversions, bin),
                    Some(value),
                    "{name} of #b{bin}"
                );
            }
        }
        // one more than the largest value, and one more than the largest u128
        let above_hex = max
            .checked_add(1)
            .map_or(format!("1{}", "0".repeat(32)), |above| format!("{above:x}"));
        let above_bin = max
            .checked_add(1)
            .map_or(format!("1{}", "0".repeat(128)), |above| {
                format!("{above:b}")
            });
        // a mixed-case spelling has its value too
        assert_eq!(convert_hex(&conversions, "fF"), Some(255), "{name} of #xfF");
        for hex in [above_hex.as_str(), "1abcdef0123456789abcdef0123456789"] {
            assert_eq!(convert_hex(&conversions, hex), None, "{name} of #x{hex}");
        }
        let above_u128 = format!("1{}", "0".repeat(128));
        for bin in [above_bin.as_str(), above_u128.as_str()] {
            assert_eq!(convert_bin(&conversions, bin), None, "{name} of #b{bin}");
        }
    }
}

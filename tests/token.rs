//! Public-API tests of the token vocabulary in `token`.

mod reserved_words;

use smt_parser_rs::String8;
use smt_parser_rs::token::Reserved;

/// Returns every `Reserved` variant, in declaration order.
///
/// Built from an exhaustive successor match, so adding a variant
/// fails compilation here instead of leaving the list stale.
fn all_reserved() -> Vec<Reserved> {
    let mut all = vec![Reserved::Binary];
    loop {
        let next = match all.last().expect("the list starts non-empty") {
            Reserved::Binary => Reserved::Decimal,
            Reserved::Decimal => Reserved::Hexadecimal,
            Reserved::Hexadecimal => Reserved::Numeral,
            Reserved::Numeral => Reserved::String,
            Reserved::String => Reserved::Underscore,
            Reserved::Underscore => Reserved::ExclamationMark,
            Reserved::ExclamationMark => Reserved::As,
            Reserved::As => Reserved::Lambda,
            Reserved::Lambda => Reserved::Let,
            Reserved::Let => Reserved::Exists,
            Reserved::Exists => Reserved::Forall,
            Reserved::Forall => Reserved::Match,
            Reserved::Match => Reserved::Par,
            Reserved::Par => return all,
        };
        all.push(next);
    }
}

/// `as_str` and `from_symbol_opt` are inverse hand-written matches;
/// the round trip catches them drifting apart. It also implies all
/// spellings are distinct: two variants sharing one would make
/// `from_symbol_opt` return the wrong variant for one of them.
#[test]
fn reserved_as_str_round_trips_through_from_symbol_opt() {
    for reserved in all_reserved() {
        let symbol = String8::from_vec(reserved.as_str().as_bytes().to_vec());
        assert_eq!(
            Reserved::from_symbol_opt(&symbol),
            Some(reserved),
            "as_str/from_symbol_opt disagree for {reserved:?}"
        );
    }
}

/// Near-misses of reserved words are ordinary symbols: matching is
/// case-sensitive and exact, with no prefix or extension matching.
#[test]
fn non_reserved_symbols_are_rejected() {
    let near_misses: [&[u8]; 32] = [
        b"",
        // case changes
        b"binary",
        b"Decimal",
        b"hexadecimal",
        b"numeral",
        b"String",
        b"As",
        b"AS",
        b"LAMBDA",
        b"Let",
        b"LET",
        b"EXISTS",
        b"Forall",
        b"MATCH",
        b"Par",
        // truncations
        b"BINAR",
        b"a",
        b"le",
        b"exist",
        b"foral",
        b"matc",
        b"pa",
        b"lambd",
        // extensions
        b"BINARYX",
        b"ass",
        b"lets",
        b"existss",
        b"matchx",
        b"parr",
        b"__",
        b"!!",
        // unrelated
        b"x",
    ];
    for text in near_misses {
        let symbol = String8::from_vec(text.to_vec());
        assert_eq!(
            Reserved::from_symbol_opt(&symbol),
            None,
            "{:?} should not be a reserved word",
            text.escape_ascii().to_string()
        );
    }
}

/// Every spelling the standard reserves, the command names included,
/// is recognized from bytes and from a string, and spells itself back.
#[test]
fn every_reserved_spelling_is_recognized() {
    for word in reserved_words::reserved_words() {
        let reserved = Reserved::from_bytes_opt(word.as_bytes())
            .unwrap_or_else(|| panic!("{word:?} should be a reserved word"));
        assert_eq!(reserved.as_str(), word, "as_str of {reserved:?}");
        let symbol = String8::from_vec(word.as_bytes().to_vec());
        assert_eq!(
            Reserved::from_symbol_opt(&symbol),
            Some(reserved),
            "from_symbol_opt and from_bytes_opt disagree for {word:?}"
        );
    }
}

/// The variants and the spellings correspond one to one, so neither list
/// can gain an entry the other lacks.
#[test]
fn every_reserved_variant_has_a_standard_spelling() {
    let all = all_reserved();
    for reserved in &all {
        assert!(
            reserved_words::reserved_words().any(|word| word == reserved.as_str()),
            "{reserved:?} is spelled {:?}, which the standard does not reserve",
            reserved.as_str()
        );
    }
    assert_eq!(
        all.len(),
        reserved_words::reserved_words().count(),
        "one variant per reserved word"
    );
}

/// Near-misses of command names are ordinary symbols, as for the
/// grammar's reserved words.
#[test]
fn non_reserved_command_like_symbols_are_rejected() {
    let near_misses: [&[u8]; 24] = [
        // case changes
        b"Assert",
        b"ASSERT",
        b"Check-Sat",
        b"PUSH",
        // separators
        b"check_sat",
        b"checksat",
        b"declare_fun",
        // truncations
        b"asser",
        b"declare",
        b"declare-",
        b"get-",
        b"check-sat-assum",
        b"define-fun-re",
        // extensions
        b"asserts",
        b"check-sat-",
        b"-check-sat",
        b"define-funs",
        b"define-fun-recs",
        b"get-values",
        b"set-logics",
        b"push1",
        b"pops",
        b"echo!",
        b"reset-assertion",
    ];
    for text in near_misses {
        assert_eq!(
            Reserved::from_bytes_opt(text),
            None,
            "{:?} should not be a reserved word",
            text.escape_ascii().to_string()
        );
    }
}

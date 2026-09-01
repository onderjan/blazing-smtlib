//! Public-API tests of the token vocabulary in `token`.

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

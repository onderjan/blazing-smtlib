//! Public-API tests of the token vocabulary in `token`.

mod reserved_words;

use smt_parser_rs::String8;
use smt_parser_rs::token::{CommandNameReserved, GeneralReserved, Reserved, SmtVersion};

/// Returns every `GeneralReserved` variant, in declaration order.
///
/// Built from an exhaustive successor match, so adding a variant
/// fails compilation here instead of leaving the list stale.
fn all_general() -> Vec<GeneralReserved> {
    let mut all = vec![GeneralReserved::Binary];
    loop {
        let next = match all.last().expect("the list starts non-empty") {
            GeneralReserved::Binary => GeneralReserved::Decimal,
            GeneralReserved::Decimal => GeneralReserved::Hexadecimal,
            GeneralReserved::Hexadecimal => GeneralReserved::Numeral,
            GeneralReserved::Numeral => GeneralReserved::String,
            GeneralReserved::String => GeneralReserved::Underscore,
            GeneralReserved::Underscore => GeneralReserved::ExclamationMark,
            GeneralReserved::ExclamationMark => GeneralReserved::As,
            GeneralReserved::As => GeneralReserved::Lambda,
            GeneralReserved::Lambda => GeneralReserved::Let,
            GeneralReserved::Let => GeneralReserved::Exists,
            GeneralReserved::Exists => GeneralReserved::Forall,
            GeneralReserved::Forall => GeneralReserved::Match,
            GeneralReserved::Match => GeneralReserved::Par,
            GeneralReserved::Par => return all,
        };
        all.push(next);
    }
}

/// Returns every `CommandNameReserved` variant, in declaration order,
/// built like [`all_general`].
fn all_command_names() -> Vec<CommandNameReserved> {
    let mut all = vec![CommandNameReserved::Assert];
    loop {
        let next = match all.last().expect("the list starts non-empty") {
            CommandNameReserved::Assert => CommandNameReserved::CheckSat,
            CommandNameReserved::CheckSat => CommandNameReserved::CheckSatAssuming,
            CommandNameReserved::CheckSatAssuming => CommandNameReserved::DeclareConst,
            CommandNameReserved::DeclareConst => CommandNameReserved::DeclareDatatype,
            CommandNameReserved::DeclareDatatype => CommandNameReserved::DeclareDatatypes,
            CommandNameReserved::DeclareDatatypes => CommandNameReserved::DeclareFun,
            CommandNameReserved::DeclareFun => CommandNameReserved::DeclareSort,
            CommandNameReserved::DeclareSort => CommandNameReserved::DeclareSortParameter,
            CommandNameReserved::DeclareSortParameter => CommandNameReserved::DefineConst,
            CommandNameReserved::DefineConst => CommandNameReserved::DefineFun,
            CommandNameReserved::DefineFun => CommandNameReserved::DefineFunRec,
            CommandNameReserved::DefineFunRec => CommandNameReserved::DefineFunsRec,
            CommandNameReserved::DefineFunsRec => CommandNameReserved::DefineSort,
            CommandNameReserved::DefineSort => CommandNameReserved::Echo,
            CommandNameReserved::Echo => CommandNameReserved::Exit,
            CommandNameReserved::Exit => CommandNameReserved::GetAssertions,
            CommandNameReserved::GetAssertions => CommandNameReserved::GetAssignment,
            CommandNameReserved::GetAssignment => CommandNameReserved::GetInfo,
            CommandNameReserved::GetInfo => CommandNameReserved::GetModel,
            CommandNameReserved::GetModel => CommandNameReserved::GetOption,
            CommandNameReserved::GetOption => CommandNameReserved::GetProof,
            CommandNameReserved::GetProof => CommandNameReserved::GetUnsatAssumptions,
            CommandNameReserved::GetUnsatAssumptions => CommandNameReserved::GetUnsatCore,
            CommandNameReserved::GetUnsatCore => CommandNameReserved::GetValue,
            CommandNameReserved::GetValue => CommandNameReserved::Pop,
            CommandNameReserved::Pop => CommandNameReserved::Push,
            CommandNameReserved::Push => CommandNameReserved::Reset,
            CommandNameReserved::Reset => CommandNameReserved::ResetAssertions,
            CommandNameReserved::ResetAssertions => CommandNameReserved::SetInfo,
            CommandNameReserved::SetInfo => CommandNameReserved::SetLogic,
            CommandNameReserved::SetLogic => CommandNameReserved::SetOption,
            CommandNameReserved::SetOption => return all,
        };
        all.push(next);
    }
}

/// Returns every `Reserved` word: the general ones, then the command names.
fn all_reserved() -> Vec<Reserved> {
    let general = all_general().into_iter().map(Reserved::General);
    let command_names = all_command_names().into_iter().map(Reserved::CommandName);
    general.chain(command_names).collect()
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
            Reserved::from_symbol_opt(&symbol, SmtVersion::V2_7),
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
            Reserved::from_symbol_opt(&symbol, SmtVersion::V2_7),
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
        let reserved = Reserved::from_bytes_opt(word.as_bytes(), SmtVersion::V2_7)
            .unwrap_or_else(|| panic!("{word:?} should be a reserved word"));
        assert_eq!(reserved.as_str(), word, "as_str of {reserved:?}");
        let symbol = String8::from_vec(word.as_bytes().to_vec());
        assert_eq!(
            Reserved::from_symbol_opt(&symbol, SmtVersion::V2_7),
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
            Reserved::from_bytes_opt(text, SmtVersion::V2_7),
            None,
            "{:?} should not be a reserved word",
            text.escape_ascii().to_string()
        );
    }
}

/// The two kinds of reserved words are told apart by `is_command_name`,
/// and each kind recognizes only its own spellings.
#[test]
fn reserved_words_are_general_or_command_names() {
    for general in all_general() {
        let reserved = Reserved::General(general);
        assert!(!reserved.is_command_name(), "{reserved:?}");
        assert_eq!(
            CommandNameReserved::from_bytes_opt(general.as_str().as_bytes(), SmtVersion::V2_7),
            None
        );
        assert_eq!(reserved.as_str(), general.as_str());
    }
    for command_name in all_command_names() {
        let reserved = Reserved::CommandName(command_name);
        assert!(reserved.is_command_name(), "{reserved:?}");
        assert_eq!(
            GeneralReserved::from_bytes_opt(command_name.as_str().as_bytes(), SmtVersion::V2_7),
            None
        );
        assert_eq!(reserved.as_str(), command_name.as_str());
    }
}

//! Public-API tests of the token vocabulary in `token`.

mod reserved_words;

use blazing_smtlib::SmtBytes;
use blazing_smtlib::token::{SmtCommandNameReserved, SmtGeneralReserved, SmtReserved, SmtVersion};

/// Returns every `SmtGeneralReserved` variant, in declaration order.
///
/// Built from an exhaustive successor match, so adding a variant
/// fails compilation here instead of leaving the list stale.
fn all_general() -> Vec<SmtGeneralReserved> {
    let mut all = vec![SmtGeneralReserved::Binary];
    loop {
        let next = match all.last().expect("the list starts non-empty") {
            SmtGeneralReserved::Binary => SmtGeneralReserved::Decimal,
            SmtGeneralReserved::Decimal => SmtGeneralReserved::Hexadecimal,
            SmtGeneralReserved::Hexadecimal => SmtGeneralReserved::Numeral,
            SmtGeneralReserved::Numeral => SmtGeneralReserved::String,
            SmtGeneralReserved::String => SmtGeneralReserved::Underscore,
            SmtGeneralReserved::Underscore => SmtGeneralReserved::ExclamationMark,
            SmtGeneralReserved::ExclamationMark => SmtGeneralReserved::As,
            SmtGeneralReserved::As => SmtGeneralReserved::Lambda,
            SmtGeneralReserved::Lambda => SmtGeneralReserved::Let,
            SmtGeneralReserved::Let => SmtGeneralReserved::Exists,
            SmtGeneralReserved::Exists => SmtGeneralReserved::Forall,
            SmtGeneralReserved::Forall => SmtGeneralReserved::Match,
            SmtGeneralReserved::Match => SmtGeneralReserved::Par,
            SmtGeneralReserved::Par => return all,
        };
        all.push(next);
    }
}

/// Returns every `SmtCommandNameReserved` variant, in declaration order,
/// built like [`all_general`].
fn all_command_names() -> Vec<SmtCommandNameReserved> {
    let mut all = vec![SmtCommandNameReserved::Assert];
    loop {
        let next = match all.last().expect("the list starts non-empty") {
            SmtCommandNameReserved::Assert => SmtCommandNameReserved::CheckSat,
            SmtCommandNameReserved::CheckSat => SmtCommandNameReserved::CheckSatAssuming,
            SmtCommandNameReserved::CheckSatAssuming => SmtCommandNameReserved::DeclareConst,
            SmtCommandNameReserved::DeclareConst => SmtCommandNameReserved::DeclareDatatype,
            SmtCommandNameReserved::DeclareDatatype => SmtCommandNameReserved::DeclareDatatypes,
            SmtCommandNameReserved::DeclareDatatypes => SmtCommandNameReserved::DeclareFun,
            SmtCommandNameReserved::DeclareFun => SmtCommandNameReserved::DeclareSort,
            SmtCommandNameReserved::DeclareSort => SmtCommandNameReserved::DeclareSortParameter,
            SmtCommandNameReserved::DeclareSortParameter => SmtCommandNameReserved::DefineConst,
            SmtCommandNameReserved::DefineConst => SmtCommandNameReserved::DefineFun,
            SmtCommandNameReserved::DefineFun => SmtCommandNameReserved::DefineFunRec,
            SmtCommandNameReserved::DefineFunRec => SmtCommandNameReserved::DefineFunsRec,
            SmtCommandNameReserved::DefineFunsRec => SmtCommandNameReserved::DefineSort,
            SmtCommandNameReserved::DefineSort => SmtCommandNameReserved::Echo,
            SmtCommandNameReserved::Echo => SmtCommandNameReserved::Exit,
            SmtCommandNameReserved::Exit => SmtCommandNameReserved::GetAssertions,
            SmtCommandNameReserved::GetAssertions => SmtCommandNameReserved::GetAssignment,
            SmtCommandNameReserved::GetAssignment => SmtCommandNameReserved::GetInfo,
            SmtCommandNameReserved::GetInfo => SmtCommandNameReserved::GetModel,
            SmtCommandNameReserved::GetModel => SmtCommandNameReserved::GetOption,
            SmtCommandNameReserved::GetOption => SmtCommandNameReserved::GetProof,
            SmtCommandNameReserved::GetProof => SmtCommandNameReserved::GetUnsatAssumptions,
            SmtCommandNameReserved::GetUnsatAssumptions => SmtCommandNameReserved::GetUnsatCore,
            SmtCommandNameReserved::GetUnsatCore => SmtCommandNameReserved::GetValue,
            SmtCommandNameReserved::GetValue => SmtCommandNameReserved::Pop,
            SmtCommandNameReserved::Pop => SmtCommandNameReserved::Push,
            SmtCommandNameReserved::Push => SmtCommandNameReserved::Reset,
            SmtCommandNameReserved::Reset => SmtCommandNameReserved::ResetAssertions,
            SmtCommandNameReserved::ResetAssertions => SmtCommandNameReserved::SetInfo,
            SmtCommandNameReserved::SetInfo => SmtCommandNameReserved::SetLogic,
            SmtCommandNameReserved::SetLogic => SmtCommandNameReserved::SetOption,
            SmtCommandNameReserved::SetOption => return all,
        };
        all.push(next);
    }
}

/// Returns every `Reserved` word: the general ones, then the command names.
fn all_reserved() -> Vec<SmtReserved> {
    let general = all_general().into_iter().map(SmtReserved::General);
    let command_names = all_command_names()
        .into_iter()
        .map(SmtReserved::CommandName);
    general.chain(command_names).collect()
}

/// `as_str` and `from_symbol_opt` are inverse hand-written matches;
/// the round trip catches them drifting apart. It also implies all
/// spellings are distinct: two variants sharing one would make
/// `from_symbol_opt` return the wrong variant for one of them.
#[test]
fn reserved_as_str_round_trips_through_from_symbol_opt() {
    for reserved in all_reserved() {
        let symbol = SmtBytes::from_vec(reserved.as_str().as_bytes().to_vec());
        assert_eq!(
            SmtReserved::from_symbol_opt(&symbol, SmtVersion::V2_7),
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
        let symbol = SmtBytes::from_vec(text.to_vec());
        assert_eq!(
            SmtReserved::from_symbol_opt(&symbol, SmtVersion::V2_7),
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
        let reserved = SmtReserved::from_bytes_opt(word.as_bytes(), SmtVersion::V2_7)
            .unwrap_or_else(|| panic!("{word:?} should be a reserved word"));
        assert_eq!(reserved.as_str(), word, "as_str of {reserved:?}");
        let symbol = SmtBytes::from_vec(word.as_bytes().to_vec());
        assert_eq!(
            SmtReserved::from_symbol_opt(&symbol, SmtVersion::V2_7),
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
            SmtReserved::from_bytes_opt(text, SmtVersion::V2_7),
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
        let reserved = SmtReserved::General(general);
        assert!(!reserved.is_command_name(), "{reserved:?}");
        assert_eq!(
            SmtCommandNameReserved::from_bytes_opt(general.as_str().as_bytes(), SmtVersion::V2_7),
            None
        );
        assert_eq!(reserved.as_str(), general.as_str());
    }
    for command_name in all_command_names() {
        let reserved = SmtReserved::CommandName(command_name);
        assert!(reserved.is_command_name(), "{reserved:?}");
        assert_eq!(
            SmtGeneralReserved::from_bytes_opt(command_name.as_str().as_bytes(), SmtVersion::V2_7),
            None
        );
        assert_eq!(reserved.as_str(), command_name.as_str());
    }
}

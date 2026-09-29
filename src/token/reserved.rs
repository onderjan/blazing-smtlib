use crate::String8;

/// Reserved words in SMT-LIB2, including standard command names.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reserved {
    General(GeneralReserved),
    CommandName(CommandNameReserved),
}

/// Every reserved word with its classification.
const RESERVED_WORDS: [(&[u8], Reserved); 46] = [
    (b"as", Reserved::General(GeneralReserved::As)),
    (
        b"assert",
        Reserved::CommandName(CommandNameReserved::Assert),
    ),
    (b"BINARY", Reserved::General(GeneralReserved::Binary)),
    (
        b"check-sat-assuming",
        Reserved::CommandName(CommandNameReserved::CheckSatAssuming),
    ),
    (
        b"check-sat",
        Reserved::CommandName(CommandNameReserved::CheckSat),
    ),
    (b"DECIMAL", Reserved::General(GeneralReserved::Decimal)),
    (
        b"declare-const",
        Reserved::CommandName(CommandNameReserved::DeclareConst),
    ),
    (
        b"declare-datatype",
        Reserved::CommandName(CommandNameReserved::DeclareDatatype),
    ),
    (
        b"declare-datatypes",
        Reserved::CommandName(CommandNameReserved::DeclareDatatypes),
    ),
    (
        b"declare-fun",
        Reserved::CommandName(CommandNameReserved::DeclareFun),
    ),
    (
        b"declare-sort",
        Reserved::CommandName(CommandNameReserved::DeclareSort),
    ),
    (
        b"declare-sort-parameter",
        Reserved::CommandName(CommandNameReserved::DeclareSortParameter),
    ),
    (
        b"define-const",
        Reserved::CommandName(CommandNameReserved::DefineConst),
    ),
    (
        b"define-fun",
        Reserved::CommandName(CommandNameReserved::DefineFun),
    ),
    (
        b"define-fun-rec",
        Reserved::CommandName(CommandNameReserved::DefineFunRec),
    ),
    (
        b"define-funs-rec",
        Reserved::CommandName(CommandNameReserved::DefineFunsRec),
    ),
    (
        b"define-sort",
        Reserved::CommandName(CommandNameReserved::DefineSort),
    ),
    (b"echo", Reserved::CommandName(CommandNameReserved::Echo)),
    (b"exists", Reserved::General(GeneralReserved::Exists)),
    (b"exit", Reserved::CommandName(CommandNameReserved::Exit)),
    (b"forall", Reserved::General(GeneralReserved::Forall)),
    (b"!", Reserved::General(GeneralReserved::ExclamationMark)),
    (b"_", Reserved::General(GeneralReserved::Underscore)),
    (
        b"get-assertions",
        Reserved::CommandName(CommandNameReserved::GetAssertions),
    ),
    (
        b"get-assignment",
        Reserved::CommandName(CommandNameReserved::GetAssignment),
    ),
    (
        b"get-info",
        Reserved::CommandName(CommandNameReserved::GetInfo),
    ),
    (
        b"get-model",
        Reserved::CommandName(CommandNameReserved::GetModel),
    ),
    (
        b"get-option",
        Reserved::CommandName(CommandNameReserved::GetOption),
    ),
    (
        b"get-proof",
        Reserved::CommandName(CommandNameReserved::GetProof),
    ),
    (
        b"get-unsat-assumptions",
        Reserved::CommandName(CommandNameReserved::GetUnsatAssumptions),
    ),
    (
        b"get-unsat-core",
        Reserved::CommandName(CommandNameReserved::GetUnsatCore),
    ),
    (
        b"get-value",
        Reserved::CommandName(CommandNameReserved::GetValue),
    ),
    (
        b"HEXADECIMAL",
        Reserved::General(GeneralReserved::Hexadecimal),
    ),
    (b"lambda", Reserved::General(GeneralReserved::Lambda)),
    (b"let", Reserved::General(GeneralReserved::Let)),
    (b"match", Reserved::General(GeneralReserved::Match)),
    (b"NUMERAL", Reserved::General(GeneralReserved::Numeral)),
    (b"par", Reserved::General(GeneralReserved::Par)),
    (b"pop", Reserved::CommandName(CommandNameReserved::Pop)),
    (b"push", Reserved::CommandName(CommandNameReserved::Push)),
    (
        b"reset-assertions",
        Reserved::CommandName(CommandNameReserved::ResetAssertions),
    ),
    (b"reset", Reserved::CommandName(CommandNameReserved::Reset)),
    (
        b"set-info",
        Reserved::CommandName(CommandNameReserved::SetInfo),
    ),
    (
        b"set-logic",
        Reserved::CommandName(CommandNameReserved::SetLogic),
    ),
    (
        b"set-option",
        Reserved::CommandName(CommandNameReserved::SetOption),
    ),
    (b"STRING", Reserved::General(GeneralReserved::String)),
];

/// Number of slots of the reserved-word table.
const RESERVED_SLOTS: usize = 128;

/// Returns the slot in the reserved-word table corresponding to the symbol.
///
/// A perfect hash of the reserved words over their length and their first, last, and
/// middle byte: no two reserved words share a slot, which the construction of
/// [`RESERVED_TABLE`] checks at compile time. The multipliers were found by the
/// ignored test `search_reserved_hash_multipliers` in this module; if a reserved
/// word is added and the check fails, run it again for new ones.
#[inline(always)]
const fn reserved_slot(symbol: &[u8]) -> usize {
    let len = symbol.len();
    let (first, last, mid) = (
        symbol[0] as usize,
        symbol[len - 1] as usize,
        symbol[len / 2] as usize,
    );
    (first + last * 4 + len * 34 + mid * 54) % RESERVED_SLOTS
}

/// The empty word is used as a sentinel value for empty reserved-word table slots.
const EMPTY_WORD: &[u8] = &[];

/// The reserved words by slot.
static RESERVED_TABLE: [(&[u8], Reserved); RESERVED_SLOTS] = {
    let mut table = [(EMPTY_WORD, Reserved::General(GeneralReserved::Underscore)); RESERVED_SLOTS];
    let mut i = 0;
    while i < RESERVED_WORDS.len() {
        let (word, reserved) = RESERVED_WORDS[i];
        let slot = reserved_slot(word);
        assert!(
            table[slot].0.is_empty(),
            "the reserved-word hash must be perfect"
        );
        table[slot] = (word, reserved);
        i += 1;
    }
    table
};

impl Reserved {
    #[inline]
    pub fn from_symbol_opt(symbol: &String8) -> Option<Reserved> {
        Self::from_bytes_opt(symbol.as_slice())
    }

    #[inline]
    pub fn from_bytes_opt(symbol: &[u8]) -> Option<Reserved> {
        // make sure that the symbol is not an empty word,
        // which is a sentinel
        if symbol.is_empty() {
            return None;
        }
        // the slot holds a reserved word or a sentinel
        let (word, reserved) = RESERVED_TABLE[reserved_slot(symbol)];
        // if the symbol is equal to the reserved word, return it
        if word == symbol { Some(reserved) } else { None }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            Reserved::General(general) => general.as_str(),
            Reserved::CommandName(command_name) => command_name.as_str(),
        }
    }

    /// Whether the reserved word is the name of a standard command.
    #[inline]
    pub fn is_command_name(&self) -> bool {
        matches!(self, Reserved::CommandName(_))
    }
}

/// General reserved words of the SMT-LIB2 grammar.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GeneralReserved {
    Binary,
    Decimal,
    Hexadecimal,
    Numeral,
    String,
    Underscore,
    ExclamationMark,
    As,
    Lambda,
    Let,
    Exists,
    Forall,
    Match,
    Par,
}

impl GeneralReserved {
    #[inline]
    pub fn from_bytes_opt(symbol: &[u8]) -> Option<GeneralReserved> {
        Some(match symbol {
            b"BINARY" => GeneralReserved::Binary,
            b"DECIMAL" => GeneralReserved::Decimal,
            b"HEXADECIMAL" => GeneralReserved::Hexadecimal,
            b"NUMERAL" => GeneralReserved::Numeral,
            b"STRING" => GeneralReserved::String,
            b"_" => GeneralReserved::Underscore,
            b"!" => GeneralReserved::ExclamationMark,
            b"as" => GeneralReserved::As,
            b"lambda" => GeneralReserved::Lambda,
            b"let" => GeneralReserved::Let,
            b"exists" => GeneralReserved::Exists,
            b"forall" => GeneralReserved::Forall,
            b"match" => GeneralReserved::Match,
            b"par" => GeneralReserved::Par,
            _ => return None,
        })
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            GeneralReserved::Binary => "BINARY",
            GeneralReserved::Decimal => "DECIMAL",
            GeneralReserved::Hexadecimal => "HEXADECIMAL",
            GeneralReserved::Numeral => "NUMERAL",
            GeneralReserved::String => "STRING",
            GeneralReserved::Underscore => "_",
            GeneralReserved::ExclamationMark => "!",
            GeneralReserved::As => "as",
            GeneralReserved::Lambda => "lambda",
            GeneralReserved::Let => "let",
            GeneralReserved::Exists => "exists",
            GeneralReserved::Forall => "forall",
            GeneralReserved::Match => "match",
            GeneralReserved::Par => "par",
        }
    }
}

/// Reserved words naming standard SMT-LIB2 commands.
///
/// Standard SMT-LIB2 commands are reserved words.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommandNameReserved {
    Assert,
    CheckSat,
    CheckSatAssuming,
    DeclareConst,
    DeclareDatatype,
    DeclareDatatypes,
    DeclareFun,
    DeclareSort,
    DeclareSortParameter,
    DefineConst,
    DefineFun,
    DefineFunRec,
    DefineFunsRec,
    DefineSort,
    Echo,
    Exit,
    GetAssertions,
    GetAssignment,
    GetInfo,
    GetModel,
    GetOption,
    GetProof,
    GetUnsatAssumptions,
    GetUnsatCore,
    GetValue,
    Pop,
    Push,
    Reset,
    ResetAssertions,
    SetInfo,
    SetLogic,
    SetOption,
}

impl CommandNameReserved {
    #[inline]
    pub fn from_bytes_opt(symbol: &[u8]) -> Option<CommandNameReserved> {
        Some(match symbol {
            b"assert" => CommandNameReserved::Assert,
            b"check-sat" => CommandNameReserved::CheckSat,
            b"check-sat-assuming" => CommandNameReserved::CheckSatAssuming,
            b"declare-const" => CommandNameReserved::DeclareConst,
            b"declare-datatype" => CommandNameReserved::DeclareDatatype,
            b"declare-datatypes" => CommandNameReserved::DeclareDatatypes,
            b"declare-fun" => CommandNameReserved::DeclareFun,
            b"declare-sort" => CommandNameReserved::DeclareSort,
            b"declare-sort-parameter" => CommandNameReserved::DeclareSortParameter,
            b"define-const" => CommandNameReserved::DefineConst,
            b"define-fun" => CommandNameReserved::DefineFun,
            b"define-fun-rec" => CommandNameReserved::DefineFunRec,
            b"define-funs-rec" => CommandNameReserved::DefineFunsRec,
            b"define-sort" => CommandNameReserved::DefineSort,
            b"echo" => CommandNameReserved::Echo,
            b"exit" => CommandNameReserved::Exit,
            b"get-assertions" => CommandNameReserved::GetAssertions,
            b"get-assignment" => CommandNameReserved::GetAssignment,
            b"get-info" => CommandNameReserved::GetInfo,
            b"get-model" => CommandNameReserved::GetModel,
            b"get-option" => CommandNameReserved::GetOption,
            b"get-proof" => CommandNameReserved::GetProof,
            b"get-unsat-assumptions" => CommandNameReserved::GetUnsatAssumptions,
            b"get-unsat-core" => CommandNameReserved::GetUnsatCore,
            b"get-value" => CommandNameReserved::GetValue,
            b"pop" => CommandNameReserved::Pop,
            b"push" => CommandNameReserved::Push,
            b"reset" => CommandNameReserved::Reset,
            b"reset-assertions" => CommandNameReserved::ResetAssertions,
            b"set-info" => CommandNameReserved::SetInfo,
            b"set-logic" => CommandNameReserved::SetLogic,
            b"set-option" => CommandNameReserved::SetOption,
            _ => return None,
        })
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            CommandNameReserved::Assert => "assert",
            CommandNameReserved::CheckSat => "check-sat",
            CommandNameReserved::CheckSatAssuming => "check-sat-assuming",
            CommandNameReserved::DeclareConst => "declare-const",
            CommandNameReserved::DeclareDatatype => "declare-datatype",
            CommandNameReserved::DeclareDatatypes => "declare-datatypes",
            CommandNameReserved::DeclareFun => "declare-fun",
            CommandNameReserved::DeclareSort => "declare-sort",
            CommandNameReserved::DeclareSortParameter => "declare-sort-parameter",
            CommandNameReserved::DefineConst => "define-const",
            CommandNameReserved::DefineFun => "define-fun",
            CommandNameReserved::DefineFunRec => "define-fun-rec",
            CommandNameReserved::DefineFunsRec => "define-funs-rec",
            CommandNameReserved::DefineSort => "define-sort",
            CommandNameReserved::Echo => "echo",
            CommandNameReserved::Exit => "exit",
            CommandNameReserved::GetAssertions => "get-assertions",
            CommandNameReserved::GetAssignment => "get-assignment",
            CommandNameReserved::GetInfo => "get-info",
            CommandNameReserved::GetModel => "get-model",
            CommandNameReserved::GetOption => "get-option",
            CommandNameReserved::GetProof => "get-proof",
            CommandNameReserved::GetUnsatAssumptions => "get-unsat-assumptions",
            CommandNameReserved::GetUnsatCore => "get-unsat-core",
            CommandNameReserved::GetValue => "get-value",
            CommandNameReserved::Pop => "pop",
            CommandNameReserved::Push => "push",
            CommandNameReserved::Reset => "reset",
            CommandNameReserved::ResetAssertions => "reset-assertions",
            CommandNameReserved::SetInfo => "set-info",
            CommandNameReserved::SetLogic => "set-logic",
            CommandNameReserved::SetOption => "set-option",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Multipliers of a candidate reserved-word hash, see `reserved_slot`.
    type Multipliers = (usize, usize, usize, usize);

    fn candidate_slot(word: &[u8], (a, b, c, d): Multipliers, slots: usize) -> usize {
        let len = word.len();
        let (first, last, mid) = (
            word[0] as usize,
            word[len - 1] as usize,
            word[len / 2] as usize,
        );
        (first * a + last * b + len * c + mid * d) % slots
    }

    /// Whether the multipliers give every reserved word its own slot.
    fn is_perfect(multipliers: Multipliers, slots: usize) -> bool {
        let mut used = vec![false; slots];
        RESERVED_WORDS.iter().all(|(word, _)| {
            let slot = candidate_slot(word, multipliers, slots);
            !std::mem::replace(&mut used[slot], true)
        })
    }

    /// Finds multipliers for `reserved_slot`, to be run when a reserved word is added
    /// and the compile-time check of `RESERVED_TABLE` fails:
    ///
    /// ```text
    /// cargo test --release --lib -- --ignored search_reserved_hash_multipliers --nocapture
    /// ```
    ///
    /// For each table size it prints the smallest multipliers (up to 63 each) under
    /// which no two reserved words share a slot, or that there are none.
    #[test]
    #[ignore]
    fn search_reserved_hash_multipliers() {
        const MAX_MULTIPLIER: usize = 63;
        println!("{} reserved words", RESERVED_WORDS.len());
        for slots in [64usize, 128, 256] {
            let range = 1..=MAX_MULTIPLIER;
            let found = range.clone().find_map(|a| {
                range.clone().find_map(|b| {
                    range.clone().find_map(|c| {
                        range
                            .clone()
                            .find(|&d| is_perfect((a, b, c, d), slots))
                            .map(|d| (a, b, c, d))
                    })
                })
            });
            match found {
                Some((a, b, c, d)) => {
                    println!(
                        "{slots} slots: (first * {a} + last * {b} + len * {c} + mid * {d}) % {slots}"
                    )
                }
                None => println!(
                    "{slots} slots: no perfect hash with multipliers up to {MAX_MULTIPLIER}"
                ),
            }
        }
    }

    #[test]
    fn the_landed_multipliers_are_perfect_and_match_the_search_form() {
        // the table's construction proves this at compile time; the test ties the
        // search's formula to the landed one, so the two cannot drift apart
        assert!(is_perfect((1, 4, 34, 54), RESERVED_SLOTS));
        for (word, _) in RESERVED_WORDS {
            assert_eq!(
                candidate_slot(word, (1, 4, 34, 54), RESERVED_SLOTS),
                reserved_slot(word),
                "slot of {:?}",
                String::from_utf8_lossy(word)
            );
        }
    }
}

use crate::SmtVersion;

/// Reserved word (general or a command name).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtReserved {
    General(SmtGeneralReserved),
    CommandName(SmtCommandNameReserved),
}

/// Defines the reserved words.
///
/// For each group of reserved words, the macro builds an enum with one variant
/// per word, the conversions between the variants and the words, and the table
/// of every reserved word with its classification used to build the perfect hash.
macro_rules! reserved_words {
    ($(
        $(#[$meta:meta])*
        $variant_kind:ident: $enum_name:ident {
            $($variant:ident = $word:literal,)*
        }
    )*) => {
        $(
            $(#[$meta])*
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub enum $enum_name {
                $($variant,)*
            }

            impl $enum_name {
                /// Word of this group that the symbol spells in the version, if any.
                #[inline]
                pub fn from_bytes(symbol: &[u8], version: SmtVersion) -> Option<Self> {
                    match SmtReserved::from_bytes(symbol, version) {
                        Some(SmtReserved::$variant_kind(reserved)) => Some(reserved),
                        _ => None,
                    }
                }

                pub fn as_str(&self) -> &'static str {
                    match self {
                        $(Self::$variant => $word,)*
                    }
                }
            }
        )*

        /// Every reserved word with its classification.
        const RESERVED_WORDS: &[(&[u8], SmtReserved)] = &[
            $($(($word.as_bytes(), SmtReserved::$variant_kind($enum_name::$variant)),)*)*
        ];
    };
}

reserved_words! {
    /// General reserved word.
    General: SmtGeneralReserved {
        Binary = "BINARY",
        Decimal = "DECIMAL",
        Hexadecimal = "HEXADECIMAL",
        Numeral = "NUMERAL",
        String = "STRING",
        Underscore = "_",
        ExclamationMark = "!",
        As = "as",
        Lambda = "lambda",
        Let = "let",
        Exists = "exists",
        Forall = "forall",
        Match = "match",
        Par = "par",
    }
    /// Reserved word that names a standard command.
    ///
    /// Standard SMT-LIB2 commands are reserved words.
    CommandName: SmtCommandNameReserved {
        Assert = "assert",
        CheckSat = "check-sat",
        CheckSatAssuming = "check-sat-assuming",
        DeclareConst = "declare-const",
        DeclareDatatype = "declare-datatype",
        DeclareDatatypes = "declare-datatypes",
        DeclareFun = "declare-fun",
        DeclareSort = "declare-sort",
        DeclareSortParameter = "declare-sort-parameter",
        DefineConst = "define-const",
        DefineFun = "define-fun",
        DefineFunRec = "define-fun-rec",
        DefineFunsRec = "define-funs-rec",
        DefineSort = "define-sort",
        Echo = "echo",
        Exit = "exit",
        GetAssertions = "get-assertions",
        GetAssignment = "get-assignment",
        GetInfo = "get-info",
        GetModel = "get-model",
        GetOption = "get-option",
        GetProof = "get-proof",
        GetUnsatAssumptions = "get-unsat-assumptions",
        GetUnsatCore = "get-unsat-core",
        GetValue = "get-value",
        Pop = "pop",
        Push = "push",
        Reset = "reset",
        ResetAssertions = "reset-assertions",
        SetInfo = "set-info",
        SetLogic = "set-logic",
        SetOption = "set-option",
    }
}

impl SmtReserved {
    /// Returns the version that made the word reserved.
    const fn since(self) -> SmtVersion {
        match self {
            // SMT-LIB 2.7: lambda terms, sort parameters, constant definitions
            SmtReserved::General(SmtGeneralReserved::Lambda)
            | SmtReserved::CommandName(SmtCommandNameReserved::DeclareSortParameter)
            | SmtReserved::CommandName(SmtCommandNameReserved::DefineConst) => SmtVersion::V2_7,
            // SMT-LIB 2.6: datatypes and matching on them
            SmtReserved::General(SmtGeneralReserved::Match)
            | SmtReserved::CommandName(SmtCommandNameReserved::DeclareDatatype)
            | SmtReserved::CommandName(SmtCommandNameReserved::DeclareDatatypes) => {
                SmtVersion::V2_6
            }
            // SMT-LIB 2.5: the remaining special-constant categories and added commands
            SmtReserved::General(SmtGeneralReserved::Binary)
            | SmtReserved::General(SmtGeneralReserved::Hexadecimal)
            | SmtReserved::CommandName(SmtCommandNameReserved::CheckSatAssuming)
            | SmtReserved::CommandName(SmtCommandNameReserved::DeclareConst)
            | SmtReserved::CommandName(SmtCommandNameReserved::DefineFunRec)
            | SmtReserved::CommandName(SmtCommandNameReserved::DefineFunsRec)
            | SmtReserved::CommandName(SmtCommandNameReserved::Echo)
            | SmtReserved::CommandName(SmtCommandNameReserved::GetModel)
            | SmtReserved::CommandName(SmtCommandNameReserved::GetUnsatAssumptions)
            | SmtReserved::CommandName(SmtCommandNameReserved::Reset)
            | SmtReserved::CommandName(SmtCommandNameReserved::ResetAssertions) => SmtVersion::V2_5,
            // everything else is reserved since SMT-LIB 2.0
            _ => SmtVersion::V2_0,
        }
    }

    /// Whether the word is reserved in the given version.
    #[inline]
    pub fn is_in_version(&self, version: SmtVersion) -> bool {
        version >= self.since()
    }
}

/// Number of slots of the reserved-word table.
const RESERVED_SLOTS: usize = 128;

/// Returns the slot in the reserved-word table corresponding to the symbol.
///
/// A perfect hash of the reserved words over their length and their first, last, and
/// middle byte: no two reserved words share a slot, which the construction of
/// [RESERVED_TABLE] checks at compile time. The multipliers were found by the
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

/// The reserved words by slot, each with the version that made it reserved.
static RESERVED_TABLE: [(&[u8], SmtReserved, SmtVersion); RESERVED_SLOTS] = {
    let mut table = [(
        EMPTY_WORD,
        SmtReserved::General(SmtGeneralReserved::Underscore),
        SmtVersion::V2_5,
    ); RESERVED_SLOTS];
    let mut i = 0;
    while i < RESERVED_WORDS.len() {
        let (word, reserved) = RESERVED_WORDS[i];
        let slot = reserved_slot(word);
        assert!(
            table[slot].0.is_empty(),
            "the reserved-word hash must be perfect"
        );
        table[slot] = (word, reserved, reserved.since());
        i += 1;
    }
    table
};

impl SmtReserved {
    /// Reserved word that the symbol spells in the version, if any.
    #[inline]
    pub fn from_bytes(symbol: &[u8], version: SmtVersion) -> Option<SmtReserved> {
        // make sure that the symbol is not an empty word,
        // which is a sentinel
        if symbol.is_empty() {
            return None;
        }
        // the slot holds a reserved word or a sentinel
        let (word, reserved, since) = RESERVED_TABLE[reserved_slot(symbol)];
        // if the symbol is equal to the reserved word and the version has it, return it
        if word == symbol && version >= since {
            Some(reserved)
        } else {
            None
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            SmtReserved::General(general) => general.as_str(),
            SmtReserved::CommandName(command_name) => command_name.as_str(),
        }
    }

    /// Whether the reserved word is the name of a standard command.
    #[inline]
    pub fn is_command_name(&self) -> bool {
        matches!(self, SmtReserved::CommandName(_))
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

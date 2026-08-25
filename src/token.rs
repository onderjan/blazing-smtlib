use crate::string::String8;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    ParenOpen,
    ParenClose,
    Numeral(String8),
    Decimal {
        whole_part: String8,
        fractional_part: String8,
    },
    Hexadecimal(String8),
    Binary(String8),
    Symbol(String8),
    Reserved(Reserved),
    String(String8),
    Keyword(String8),
    End,
}

/// Reserved words in SMT-LIB2.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Reserved {
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

impl Reserved {
    pub fn from_symbol_opt(symbol: &String8) -> Option<Reserved> {
        Some(match symbol.as_slice() {
            b"BINARY" => Reserved::Binary,
            b"DECIMAL" => Reserved::Decimal,
            b"HEXADECIMAL" => Reserved::Hexadecimal,
            b"NUMERAL" => Reserved::Numeral,
            b"STRING" => Reserved::String,
            b"_" => Reserved::Underscore,
            b"!" => Reserved::ExclamationMark,
            b"as" => Reserved::As,
            b"lambda" => Reserved::Lambda,
            b"let" => Reserved::Let,
            b"exists" => Reserved::Exists,
            b"forall" => Reserved::Forall,
            b"match" => Reserved::Match,
            b"par" => Reserved::Par,
            _ => return None,
        })
    }
}

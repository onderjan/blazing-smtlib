use crate::{
    SmtBinDigits, SmtDecimal, SmtHexDigits, SmtKeyword, SmtNumeral, SmtStringContent, SmtSymbol,
    string::String8,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    ParenOpen,
    ParenClose,
    Numeral(SmtNumeral),
    Decimal(SmtDecimal),
    Hexadecimal(SmtHexDigits),
    Binary(SmtBinDigits),
    Symbol(SmtSymbol),
    Reserved(Reserved),
    String(SmtStringContent),
    Keyword(SmtKeyword),
    EndOfFile,
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

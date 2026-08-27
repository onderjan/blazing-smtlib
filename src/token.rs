use crate::{
    SmtBinDigits, SmtDecimal, SmtHexDigits, SmtKeyword, SmtNumeral, SmtStringContent, SmtSymbol,
    TokenSpan, string::String8,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenType {
    ParenOpen,
    ParenClose,
    Numeral,
    Decimal,
    Hexadecimal,
    Binary,
    Symbol,
    Reserved(Reserved),
    String,
    Keyword,
    EndOfFile,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
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

impl TokenKind {
    pub fn ty(&self) -> TokenType {
        match self {
            TokenKind::ParenOpen => TokenType::ParenOpen,
            TokenKind::ParenClose => TokenType::ParenClose,
            TokenKind::Numeral(_) => TokenType::Numeral,
            TokenKind::Decimal(_) => TokenType::Decimal,
            TokenKind::Hexadecimal(_) => TokenType::Hexadecimal,
            TokenKind::Binary(_) => TokenType::Binary,
            TokenKind::Symbol(_) => TokenType::Symbol,
            TokenKind::Reserved(reserved) => TokenType::Reserved(*reserved),
            TokenKind::String(_) => TokenType::String,
            TokenKind::Keyword(_) => TokenType::Keyword,
            TokenKind::EndOfFile => TokenType::EndOfFile,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    kind: TokenKind,
    span: TokenSpan,
}

impl Token {
    pub(crate) fn new(kind: TokenKind, span: TokenSpan) -> Token {
        Self { kind, span }
    }

    pub fn kind(&self) -> &TokenKind {
        &self.kind
    }

    pub fn into_kind(self) -> TokenKind {
        self.kind
    }

    pub(crate) fn span(&self) -> TokenSpan {
        self.span
    }
}

/// Reserved words in SMT-LIB2.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

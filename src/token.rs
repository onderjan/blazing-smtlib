use crate::{
    SmtBinDigitsView, SmtDecimalView, SmtHexDigitsView, SmtKeywordView, SmtNumeralView, SmtSpan,
    SmtStringContentView, SmtSymbolView, string::String8,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind<'a> {
    ParenOpen,
    ParenClose,
    Numeral(SmtNumeralView<'a>),
    Decimal(SmtDecimalView<'a>),
    Hexadecimal(SmtHexDigitsView<'a>),
    Binary(SmtBinDigitsView<'a>),
    Symbol(SmtSymbolView<'a>),
    Reserved(Reserved),
    String(SmtStringContentView<'a>),
    Keyword(SmtKeywordView<'a>),
    EndOfFile,
}

impl TokenKind<'_> {
    #[inline]
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
pub struct Token<'a> {
    kind: TokenKind<'a>,
    span: SmtSpan,
}

impl<'a> Token<'a> {
    #[inline]
    pub(crate) fn new(kind: TokenKind<'a>, span: SmtSpan) -> Token<'a> {
        Self { kind, span }
    }

    #[inline]
    pub fn kind(&self) -> TokenKind<'a> {
        self.kind
    }

    #[inline]
    pub fn span(&self) -> SmtSpan {
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
    #[inline]
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

    pub fn as_str(&self) -> &'static str {
        match self {
            Reserved::Binary => "BINARY",
            Reserved::Decimal => "DECIMAL",
            Reserved::Hexadecimal => "HEXADECIMAL",
            Reserved::Numeral => "NUMERAL",
            Reserved::String => "STRING",
            Reserved::Underscore => "_",
            Reserved::ExclamationMark => "!",
            Reserved::As => "as",
            Reserved::Lambda => "lambda",
            Reserved::Let => "let",
            Reserved::Exists => "exists",
            Reserved::Forall => "forall",
            Reserved::Match => "match",
            Reserved::Par => "par",
        }
    }
}

/// A sequential handler of tokens.
pub trait TokenHandler {
    type Error;

    /// Sequentially handles one token.
    fn handle_token(&mut self, token: Token) -> Result<(), Self::Error>;
}

/// Mutable references over token handlers are token handlers.
impl<T: TokenHandler + ?Sized> TokenHandler for &mut T {
    type Error = T::Error;

    fn handle_token(&mut self, token: Token) -> Result<(), Self::Error> {
        (**self).handle_token(token)
    }
}

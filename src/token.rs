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
    String,
    Keyword,
    UnquotedSymbol,
    QuotedSymbol,
    // PERFORMANCE: leave EOF last for easy construction
    // from a similar enum without EOF in the lexer
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
    String(SmtStringContentView<'a>),
    Keyword(SmtKeywordView<'a>),
    Symbol(SmtSymbolView<'a>),
    Reserved(Reserved),
    EndOfFile,
}

/// Version of the SMT-LIB standard.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SmtVersion {
    V2_7,
}

impl<'a> TokenKind<'a> {
    /// Construct the token kind from the token and version.
    #[inline]
    pub fn from_token(token: &Token<'a>, version: SmtVersion) -> Self {
        let content = token.content();
        match token.ty() {
            TokenType::ParenOpen => TokenKind::ParenOpen,
            TokenType::ParenClose => TokenKind::ParenClose,
            TokenType::Numeral => TokenKind::Numeral(SmtNumeralView::new_unchecked(content)),
            TokenType::Decimal => TokenKind::Decimal(SmtDecimalView::new_unchecked(content)),
            TokenType::Hexadecimal => {
                TokenKind::Hexadecimal(SmtHexDigitsView::new_unchecked(content))
            }
            TokenType::Binary => TokenKind::Binary(SmtBinDigitsView::new_unchecked(content)),
            TokenType::UnquotedSymbol => {
                // process reserved words
                // TODO: multiple versions
                match version {
                    SmtVersion::V2_7 => {
                        match Reserved::from_bytes_opt(content) {
                            Some(reserved) => {
                                // reserved word, not a symbol
                                TokenKind::Reserved(reserved)
                            }
                            None => TokenKind::Symbol(SmtSymbolView::new_unchecked(content)),
                        }
                    }
                }
            }
            TokenType::QuotedSymbol => TokenKind::Symbol(SmtSymbolView::new_unchecked(content)),
            TokenType::String => TokenKind::String(SmtStringContentView::new_unchecked(content)),
            TokenType::Keyword => TokenKind::Keyword(SmtKeywordView::new_unchecked(content)),
            TokenType::EndOfFile => TokenKind::EndOfFile,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token<'a> {
    ty: TokenType,
    content: &'a [u8],
    span: SmtSpan,
}

impl<'a> Token<'a> {
    #[inline]
    pub(crate) fn new(ty: TokenType, content: &'a [u8], span: SmtSpan) -> Token<'a> {
        Self { ty, content, span }
    }

    #[inline]
    pub fn ty(&self) -> TokenType {
        self.ty
    }

    #[inline]
    pub fn content(&self) -> &'a [u8] {
        self.content
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
        Self::from_bytes_opt(symbol.as_slice())
    }

    #[inline]
    pub fn from_bytes_opt(symbol: &[u8]) -> Option<Reserved> {
        Some(match symbol {
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
    fn handle_token(&mut self, token: &Token) -> Result<(), Self::Error>;
}

/// Mutable references over token handlers are token handlers.
impl<T: TokenHandler + ?Sized> TokenHandler for &mut T {
    type Error = T::Error;

    #[inline]
    fn handle_token(&mut self, token: &Token) -> Result<(), Self::Error> {
        (**self).handle_token(token)
    }
}

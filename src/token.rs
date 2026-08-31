use crate::{
    SmtBinDigits, SmtDecimal, SmtHexDigits, SmtKeyword, SmtNumeral, SmtSpan, SmtStringContent,
    SmtSymbol, string::String8,
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
    span: SmtSpan,
}

impl Token {
    pub(crate) fn new(kind: TokenKind, span: SmtSpan) -> Token {
        Self { kind, span }
    }

    pub fn kind(&self) -> &TokenKind {
        &self.kind
    }

    pub fn into_kind(self) -> TokenKind {
        self.kind
    }

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

#[cfg(test)]
mod tests {
    use super::*;

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
}

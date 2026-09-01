use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtKeyword, SmtStringContent, SmtSymbol,
    read::parser::{CategoryParser, CategoryParserErrorKind, ParserError},
    token::{Token, TokenKind, TokenType},
};

macro_rules! token_parser {
    ($parser:ident, $result:ty, $expected:expr, $pattern:pat => $value:expr) => {
        pub struct $parser;

        impl $parser {
            pub fn new() -> Self {
                Self
            }
        }

        impl Default for $parser {
            fn default() -> Self {
                Self::new()
            }
        }

        impl $parser {
            /// Consumes exactly one token, which must match.
            pub(crate) fn expect<H: SmtHandler>(token: Token) -> Result<$result, ParserError<H>> {
                let span = token.span();
                match token.into_kind() {
                    $pattern => Ok($value),
                    _ => Err(ParserError::category_error(
                        CategoryParserErrorKind::ExpectedToken($expected),
                        span,
                    )),
                }
            }
        }

        impl<H: SmtHandler> CategoryParser<H> for $parser {
            type Result = $result;

            fn progress(
                self,
                _handler: &mut H,
                token: Token,
            ) -> Result<ControlFlow<Self::Result, Self>, ParserError<H>> {
                Ok(ControlFlow::Break(Self::expect(token)?))
            }
        }
    };
}

token_parser!(SymbolParser, SmtSymbol, &[TokenType::Symbol],
    TokenKind::Symbol(symbol) => symbol);
token_parser!(OpenParenParser, (), &[TokenType::ParenOpen],
    TokenKind::ParenOpen => ());
token_parser!(CloseParenParser, (), &[TokenType::ParenClose],
    TokenKind::ParenClose => ());
token_parser!(KeywordParser, SmtKeyword, &[TokenType::Keyword],
    TokenKind::Keyword(keyword) => keyword);
token_parser!(StringParser, SmtStringContent, &[TokenType::String],
    TokenKind::String(string) => string);


#[cfg(test)]
mod tests {
    use super::*;
    use crate::read::parser::category::tests::{assert_error, parse_all, run};

    #[test]
    fn symbol_parser() {
        let symbol = parse_all::<SymbolParser>(b"abc");
        assert_eq!(symbol.as_slice(), b"abc");
        let symbol = parse_all::<SymbolParser>(b"|quoted symbol|");
        assert_eq!(symbol.as_slice(), b"quoted symbol");

        let err = assert_error::<SymbolParser>(b"1", 0, 1);
        let expected_symbol = CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol]);
        assert_eq!(err, expected_symbol, "{err:?}");
        let err = assert_error::<SymbolParser>(b"(", 0, 1);
        assert_eq!(err, expected_symbol, "{err:?}");
        // reserved words are not symbols
        let err = assert_error::<SymbolParser>(b"let", 0, 3);
        assert_eq!(err, expected_symbol, "{err:?}");
    }

    #[test]
    fn symbol_parser_consumes_one_token() {
        let (symbol, left) = run::<SymbolParser>(b"a b c").expect("valid");
        assert_eq!(symbol.as_slice(), b"a");
        assert_eq!(left, 2);
    }

    #[test]
    fn open_paren_parser() {
        parse_all::<OpenParenParser>(b"(");

        let expected_open = CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen]);
        let err = assert_error::<OpenParenParser>(b")", 0, 1);
        assert_eq!(err, expected_open, "{err:?}");
        let err = assert_error::<OpenParenParser>(b"x", 0, 1);
        assert_eq!(err, expected_open, "{err:?}");
    }

    #[test]
    fn close_paren_parser() {
        parse_all::<CloseParenParser>(b")");

        let expected_close = CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose]);
        let err = assert_error::<CloseParenParser>(b"x", 0, 1);
        assert_eq!(err, expected_close, "{err:?}");
        // the end-of-file token does not match either; its span is zero-width
        let err = assert_error::<CloseParenParser>(b"", 0, 0);
        assert_eq!(err, expected_close, "{err:?}");
    }

    #[test]
    fn keyword_parser() {
        // the keyword content is stored without the leading colon
        let keyword = parse_all::<KeywordParser>(b":status");
        assert_eq!(keyword.as_slice(), b"status");

        let expected_keyword = CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword]);
        // a bare symbol is not a keyword
        let err = assert_error::<KeywordParser>(b"status", 0, 6);
        assert_eq!(err, expected_keyword, "{err:?}");
        let err = assert_error::<KeywordParser>(b"(", 0, 1);
        assert_eq!(err, expected_keyword, "{err:?}");
    }

    #[test]
    fn string_parser() {
        // the string content is stored without the enclosing quotes
        let string = parse_all::<StringParser>(b"\"hello world\"");
        assert_eq!(string.as_slice(), b"hello world");
        // a doubled quote is the escape for a single quote
        let string = parse_all::<StringParser>(b"\"a\"\"b\"");
        assert_eq!(string.as_slice(), b"a\"b");

        let expected_string = CategoryParserErrorKind::ExpectedToken(&[TokenType::String]);
        // neither a quoted symbol nor a numeral is a string literal
        let err = assert_error::<StringParser>(b"|hello|", 0, 7);
        assert_eq!(err, expected_string, "{err:?}");
        let err = assert_error::<StringParser>(b"1", 0, 1);
        assert_eq!(err, expected_string, "{err:?}");
    }
}

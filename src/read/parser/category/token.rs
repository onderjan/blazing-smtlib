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

        impl<H: SmtHandler> CategoryParser<H> for $parser {
            type Result = $result;

            fn progress(
                self,
                _handler: &mut H,
                token: Token,
            ) -> Result<ControlFlow<Self::Result, Self>, ParserError<H>> {
                let span = token.span();
                match token.into_kind() {
                    $pattern => Ok(ControlFlow::Break($value)),
                    _ => Err(ParserError::category_error(
                        CategoryParserErrorKind::ExpectedToken($expected),
                        span,
                    )),
                }
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

use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtKeyword, SmtNumeral, SmtStringContent, SmtSymbol,
    read::parser::{CategoryErrorKind, CategoryParser, ParserError, ParserResources},
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
            pub(crate) fn expect<E>(token: &Token) -> Result<$result, ParserError<E>> {
                let span = token.span();
                match token.kind() {
                    $pattern => Ok($value),
                    _ => Err(ParserError::category_error(
                        CategoryErrorKind::ExpectedToken($expected),
                        span,
                    )),
                }
            }
        }

        impl<H: SmtHandler> CategoryParser<H> for $parser {
            type Result = $result;

            fn progress(
                &mut self,
                _handler: &mut H,
                _resources: &mut ParserResources,
                token: &Token,
            ) -> Result<ControlFlow<Self::Result, ()>, ParserError<H::Error>> {
                Ok(ControlFlow::Break(Self::expect(token)?))
            }

            fn restart(&mut self) {
                // nothing to restart
            }
        }
    };
}

token_parser!(SymbolParser, SmtSymbol, &[TokenType::Symbol],
    TokenKind::Symbol(symbol) => symbol.into_owned());
token_parser!(NumeralParser, SmtNumeral, &[TokenType::Numeral],
    TokenKind::Numeral(numeral) => numeral.into_owned());

token_parser!(OpenParenParser, (), &[TokenType::ParenOpen],
    TokenKind::ParenOpen => ());
token_parser!(CloseParenParser, (), &[TokenType::ParenClose],
    TokenKind::ParenClose => ());

token_parser!(KeywordParser, SmtKeyword, &[TokenType::Keyword],
    TokenKind::Keyword(keyword) => keyword.into_owned());
token_parser!(StringParser, SmtStringContent, &[TokenType::String],
    TokenKind::String(string) => string.into_owned());

use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtKeywordBuf, SmtNumeralBuf, SmtStringContentBuf, SmtSymbolBuf,
    parser::{SmtParse, SmtParseError, SmtParseState, SmtSyntaxErrorKind, SmtSyntaxExpected},
    token::{SmtCursor, SmtSyntaxToken, SmtTokenCategory},
};

pub struct SmtSymbolParser;

impl SmtSymbolParser {
    pub fn new() -> Self {
        Self
    }
}

impl Default for SmtSymbolParser {
    fn default() -> Self {
        Self::new()
    }
}

impl SmtSymbolParser {
    /// Consumes exactly one token, which must match.
    pub(crate) fn expect<H: SmtHandler + ?Sized, Z: SmtCursor>(
        cursor: &Z,
        token: Z::Token,
    ) -> Result<SmtSymbolBuf, SmtParseError<H::Error>> {
        match cursor.syntax(&token) {
            SmtSyntaxToken::Symbol(symbol) => Ok(symbol.into_owned()),
            _ => Err(SmtParseError::syntax_error(SmtSyntaxErrorKind::Expected(
                &[SmtSyntaxExpected::Symbol],
            ))),
        }
    }
}

impl<H: SmtHandler> SmtParse<H> for SmtSymbolParser {
    type Result = SmtSymbolBuf;

    fn parse<Z: SmtCursor>(
        &mut self,
        _handler: &mut H,
        _parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<Self::Result, ()>, SmtParseError<H::Error>> {
        let Some(token) = cursor.next() else {
            return Ok(ControlFlow::Continue(()));
        };
        Ok(ControlFlow::Break(Self::expect::<H, Z>(cursor, token)?))
    }
}

/// Defines a parser of one token of the given type.
///
/// The parser needs no resources as the decision is made
/// based only on the token itself.
macro_rules! token_parser {
    ($parser:ident, $result:ty, $ty:ident, $pattern:pat => $value:expr) => {
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
            /// Consumes exactly one token, which must be of the parser's type.
            pub(crate) fn expect<Z: SmtCursor, E>(
                cursor: &Z,
                token: Z::Token,
            ) -> Result<$result, SmtParseError<E>> {
                if let $pattern = cursor.syntax(&token) {
                    Ok($value)
                } else {
                    Err(SmtParseError::syntax_error(SmtSyntaxErrorKind::Expected(
                        &[SmtSyntaxExpected::Token(SmtTokenCategory::$ty)],
                    )))
                }
            }
        }

        impl<H: SmtHandler> SmtParse<H> for $parser {
            type Result = $result;

            fn parse<Z: SmtCursor>(
                &mut self,
                _handler: &mut H,
                _parse_state: &mut SmtParseState<H>,
                cursor: &mut Z,
            ) -> Result<ControlFlow<Self::Result, ()>, SmtParseError<H::Error>> {
                let Some(token) = cursor.next() else {
                    return Ok(ControlFlow::Continue(()));
                };
                Ok(ControlFlow::Break(Self::expect(cursor, token)?))
            }
        }
    };
}

token_parser!(SmtOpenParenParser, (), ParenOpen, SmtSyntaxToken::ParenOpen => ());
token_parser!(SmtCloseParenParser, (), ParenClose, SmtSyntaxToken::ParenClose => ());

token_parser!(SmtNumeralParser, SmtNumeralBuf, Numeral, SmtSyntaxToken::Numeral(numeral) => numeral.into_owned());

token_parser!(SmtKeywordParser, SmtKeywordBuf, Keyword, SmtSyntaxToken::Keyword(keyword) => keyword.into_owned());
token_parser!(SmtStringParser, SmtStringContentBuf, String, SmtSyntaxToken::String(string) => string.into_owned());

use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtKeyword, SmtKeywordBuf, SmtNumeral, SmtNumeralBuf, SmtStringContent,
    SmtStringContentBuf, SmtSymbolBuf,
    parser::{SmtParse, SmtParseError, SmtParseState, SmtSyntaxErrorKind},
    token::{SmtProduce, SmtSyntaxToken, SmtToken, SmtTokenCategory, SmtVersion},
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
    pub(crate) fn expect<H: SmtHandler + ?Sized>(
        version: SmtVersion,
        token: SmtToken,
    ) -> Result<SmtSymbolBuf, SmtParseError<H::Error>> {
        match token.syntax(version) {
            SmtSyntaxToken::Symbol(symbol) => Ok(symbol.into_owned()),
            _ => Err(SmtParseError::category_error(
                SmtSyntaxErrorKind::ExpectedSymbol,
            )),
        }
    }
}

impl<H: SmtHandler> SmtParse<H> for SmtSymbolParser {
    type Result = SmtSymbolBuf;

    fn parse<'a, C: SmtProduce<'a>>(
        &mut self,
        _handler: &mut H,
        _parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<Self::Result, ()>, SmtParseError<H::Error>> {
        let Some(token) = cursor.next() else {
            return Ok(ControlFlow::Continue(()));
        };
        Ok(ControlFlow::Break(Self::expect::<H>(
            cursor.version(),
            token,
        )?))
    }
}

/// Defines a parser of one token of the given type, whose result is
/// computed from the token's content.
///
/// The type alone decides whether the token matches, so these parsers need
/// neither the resources nor the token kind.
macro_rules! token_parser {
    ($parser:ident, $result:ty, $ty:ident, |$content:pat_param| $value:expr) => {
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
            pub(crate) fn expect<E>(token: SmtToken) -> Result<$result, SmtParseError<E>> {
                if token.category() == SmtTokenCategory::$ty {
                    let $content = token.content();
                    Ok($value)
                } else {
                    Err(SmtParseError::category_error(
                        SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::$ty]),
                    ))
                }
            }
        }

        impl<H: SmtHandler> SmtParse<H> for $parser {
            type Result = $result;

            fn parse<'a, C: SmtProduce<'a>>(
                &mut self,
                _handler: &mut H,
                _parse_state: &mut SmtParseState<H>,
                cursor: &mut C,
            ) -> Result<ControlFlow<Self::Result, ()>, SmtParseError<H::Error>> {
                let Some(token) = cursor.next() else {
                    return Ok(ControlFlow::Continue(()));
                };
                Ok(ControlFlow::Break(Self::expect(token)?))
            }
        }
    };
}

token_parser!(SmtNumeralParser, SmtNumeralBuf, Numeral, |content| {
    SmtNumeral::new_unchecked(content).into_owned()
});

token_parser!(SmtOpenParenParser, (), ParenOpen, |_| ());
token_parser!(SmtCloseParenParser, (), ParenClose, |_| ());

token_parser!(SmtKeywordParser, SmtKeywordBuf, Keyword, |content| {
    SmtKeyword::new_unchecked(content).into_owned()
});
token_parser!(SmtStringParser, SmtStringContentBuf, String, |content| {
    SmtStringContent::new_unchecked(content).into_owned()
});

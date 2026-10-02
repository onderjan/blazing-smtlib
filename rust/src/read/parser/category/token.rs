use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtKeyword, SmtKeywordView, SmtNumeral, SmtNumeralView, SmtStringContent,
    SmtStringContentView, SmtSymbol,
    read::parser::{Parser, ParserError, ParserResources, SyntaxErrorKind},
    token::{SmtVersion, Token, TokenCursor, TokenKind, TokenType},
};

pub struct SymbolParser;

impl SymbolParser {
    pub fn new() -> Self {
        Self
    }
}

impl Default for SymbolParser {
    fn default() -> Self {
        Self::new()
    }
}

impl SymbolParser {
    /// Consumes exactly one token, which must match.
    pub(crate) fn expect<H: SmtHandler + ?Sized>(
        version: SmtVersion,
        token: Token,
    ) -> Result<SmtSymbol, ParserError<H::Error>> {
        let span = token.span();
        match token.kind(version) {
            TokenKind::Symbol(symbol) => Ok(symbol.into_owned()),
            _ => Err(ParserError::category_error(
                SyntaxErrorKind::ExpectedSymbol,
                span,
            )),
        }
    }
}

impl<H: SmtHandler> Parser<H> for SymbolParser {
    type Result = SmtSymbol;

    fn parse(
        &mut self,
        _handler: &mut H,
        _resources: &mut ParserResources<H>,
        cursor: &mut TokenCursor,
    ) -> Result<ControlFlow<Self::Result, ()>, ParserError<H::Error>> {
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
            pub(crate) fn expect<E>(token: Token) -> Result<$result, ParserError<E>> {
                if token.ty() == TokenType::$ty {
                    let $content = token.content();
                    Ok($value)
                } else {
                    Err(ParserError::category_error(
                        SyntaxErrorKind::ExpectedToken(&[TokenType::$ty]),
                        token.span(),
                    ))
                }
            }
        }

        impl<H: SmtHandler> Parser<H> for $parser {
            type Result = $result;

            fn parse(
                &mut self,
                _handler: &mut H,
                _resources: &mut ParserResources<H>,
                cursor: &mut TokenCursor,
            ) -> Result<ControlFlow<Self::Result, ()>, ParserError<H::Error>> {
                let Some(token) = cursor.next() else {
                    return Ok(ControlFlow::Continue(()));
                };
                Ok(ControlFlow::Break(Self::expect(token)?))
            }
        }
    };
}

token_parser!(NumeralParser, SmtNumeral, Numeral, |content| {
    SmtNumeralView::new_unchecked(content).into_owned()
});

token_parser!(OpenParenParser, (), ParenOpen, |_| ());
token_parser!(CloseParenParser, (), ParenClose, |_| ());

token_parser!(KeywordParser, SmtKeyword, Keyword, |content| {
    SmtKeywordView::new_unchecked(content).into_owned()
});
token_parser!(StringParser, SmtStringContent, String, |content| {
    SmtStringContentView::new_unchecked(content).into_owned()
});

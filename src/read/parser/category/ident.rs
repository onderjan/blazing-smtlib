use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIdent, SmtIndex, SmtSymbol,
    read::parser::{
        CategoryParserError, ParserError,
        category::{CategoryParser, CategoryParserErrorKind},
    },
    token::{Reserved, Token, TokenKind, TokenType},
};

pub enum IdentParser {
    Start,
    Open,
    AfterUnderscore,
    Indices {
        name: SmtSymbol,
        indices: Vec<SmtIndex>,
    },
}

impl IdentParser {
    pub fn new() -> Self {
        Self::Start
    }

    pub fn after_open_paren() -> Self {
        Self::Open
    }

    pub fn after_underscore() -> Self {
        Self::AfterUnderscore
    }
}

impl Default for IdentParser {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for IdentParser {
    type Result = SmtIdent;

    fn progress(
        self,
        _handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<SmtIdent, Self>, ParserError<H>> {
        let span = token.span();
        match self {
            IdentParser::Start => match token.into_kind() {
                TokenKind::Symbol(name) => Ok(ControlFlow::Break(SmtIdent {
                    name,
                    indices: Vec::new(),
                })),
                TokenKind::ParenOpen => Ok(ControlFlow::Continue(Self::Open)),
                _ => {
                    let kind = CategoryParserErrorKind::ExpectedIdent;
                    Err(CategoryParserError::new(kind, span).into())
                }
            },
            IdentParser::Open => {
                // this must be an underscore
                if matches!(token.kind(), TokenKind::Reserved(Reserved::Underscore)) {
                    Ok(ControlFlow::Continue(Self::AfterUnderscore))
                } else {
                    let kind = CategoryParserErrorKind::ExpectedToken(&[TokenType::Reserved(
                        Reserved::Underscore,
                    )]);
                    Err(CategoryParserError::new(kind, span).into())
                }
            }
            IdentParser::AfterUnderscore => {
                if let TokenKind::Symbol(name) = token.into_kind() {
                    Ok(ControlFlow::Continue(IdentParser::Indices {
                        name,
                        indices: Vec::new(),
                    }))
                } else {
                    let kind = CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol]);
                    Err(CategoryParserError::new(kind, span).into())
                }
            }
            IdentParser::Indices { name, mut indices } => match token.into_kind() {
                TokenKind::ParenClose => {
                    if indices.is_empty() {
                        let kind = CategoryParserErrorKind::EmptyIdentIndices;
                        return Err(CategoryParserError::new(kind, span).into());
                    }
                    Ok(ControlFlow::Break(SmtIdent { name, indices }))
                }
                TokenKind::Numeral(index_value) => {
                    indices.push(SmtIndex::Numeral(index_value));
                    Ok(ControlFlow::Continue(Self::Indices { name, indices }))
                }
                TokenKind::Symbol(index_symbol) => {
                    indices.push(SmtIndex::Symbol(index_symbol));
                    Ok(ControlFlow::Continue(Self::Indices { name, indices }))
                }
                _ => {
                    let kind = CategoryParserErrorKind::ExpectedIndexOrCloseParen;
                    Err(CategoryParserError::new(kind, span).into())
                }
            },
        }
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::read::parser::category::tests::{assert_error, parse_all, run};

    fn indices(ident: &SmtIdent) -> Vec<String> {
        ident
            .indices
            .iter()
            .map(|index| match index {
                SmtIndex::Numeral(n) => String::from_utf8(n.as_slice().to_vec()).unwrap(),
                SmtIndex::Symbol(s) => {
                    format!("'{}", String::from_utf8(s.as_slice().to_vec()).unwrap())
                }
            })
            .collect()
    }

    #[test]
    fn plain_symbol() {
        let ident = parse_all::<IdentParser>(b"x");
        assert_eq!(ident.name.as_slice(), b"x");
        assert!(ident.indices.is_empty());

        // a plain symbol is a single token; the rest is left for the caller
        let (ident, left) = run::<IdentParser>(b"x y").expect("valid");
        assert_eq!(ident.name.as_slice(), b"x");
        assert_eq!(left, 1);
    }

    #[test]
    fn indexed_with_numerals() {
        let ident = parse_all::<IdentParser>(b"(_ extract 7 0)");
        assert_eq!(ident.name.as_slice(), b"extract");
        assert_eq!(indices(&ident), ["7", "0"]);
    }

    #[test]
    fn indexed_with_symbols_and_numerals() {
        let ident = parse_all::<IdentParser>(b"(_ f a 1 b)");
        assert_eq!(ident.name.as_slice(), b"f");
        assert_eq!(indices(&ident), ["'a", "1", "'b"]);
    }

    #[test]
    fn indexed_over_lines() {
        let ident = parse_all::<IdentParser>(b"(_\n  bv42\n  8)");
        assert_eq!(ident.name.as_slice(), b"bv42");
        assert_eq!(indices(&ident), ["8"]);
    }

    #[test]
    fn continuations_after_open_paren_and_underscore() {
        // the callers that already consumed `(` or `( _` start in the corresponding state
        let ident = parse_all::<IdentParser>(b"(_ f 1)");
        let after_open = IdentParser::after_open_paren();
        let after_underscore = IdentParser::after_underscore();
        assert!(matches!(after_open, IdentParser::Open));
        assert!(matches!(after_underscore, IdentParser::AfterUnderscore));
        assert_eq!(ident.name.as_slice(), b"f");
    }

    #[test]
    fn errors() {
        let err = assert_error::<IdentParser>(b"1", 0, 1);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIdent),
            "{err:?}"
        );

        let err = assert_error::<IdentParser>(b")", 0, 1);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIdent),
            "{err:?}"
        );

        // after `(` only an underscore may follow
        let err = assert_error::<IdentParser>(b"(f 1)", 1, 2);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Reserved(
                    Reserved::Underscore
                )])
            ),
            "{err:?}"
        );

        // the name must be a symbol
        let err = assert_error::<IdentParser>(b"(_ 1 2)", 3, 4);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
            ),
            "{err:?}"
        );

        // at least one index is required
        let err = assert_error::<IdentParser>(b"(_ f)", 4, 5);
        assert!(
            matches!(err, CategoryParserErrorKind::EmptyIdentIndices),
            "{err:?}"
        );

        // indices are numerals or symbols only
        let err = assert_error::<IdentParser>(b"(_ f \"s\")", 5, 8);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIndexOrCloseParen),
            "{err:?}"
        );
        let err = assert_error::<IdentParser>(b"(_ f (a))", 5, 6);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIndexOrCloseParen),
            "{err:?}"
        );

        // EOF inside the indexed identifier
        let err = assert_error::<IdentParser>(b"(_ f 1", 6, 6);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIndexOrCloseParen),
            "{err:?}"
        );
    }
}

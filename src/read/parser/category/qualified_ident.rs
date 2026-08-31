use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIdent, SmtQualifiedIdent,
    read::parser::{
        ParserError,
        category::{
            CategoryParser, CategoryParserError, CategoryParserErrorKind, expect_close_paren,
            ident::IdentParser, sort::SortParser,
        },
    },
    token::{Reserved, Token, TokenKind, TokenType},
};

pub enum QualifiedIdentParser<H: SmtHandler> {
    Start,
    Open,
    UnqualifiedIndexed(IdentParser),
    QualifiedIdent(IdentParser),
    QualifiedSort(SmtIdent, SortParser<H>),
    QualifiedClose(SmtIdent, H::Sort),
}

impl<H: SmtHandler> QualifiedIdentParser<H> {
    pub fn new() -> Self {
        Self::Start
    }

    pub fn after_open_paren() -> Self {
        Self::Open
    }

    pub fn after_underscore() -> Self {
        Self::UnqualifiedIndexed(IdentParser::after_underscore())
    }

    pub fn after_as() -> Self {
        Self::QualifiedIdent(IdentParser::new())
    }
}

impl<H: SmtHandler> Default for QualifiedIdentParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for QualifiedIdentParser<H> {
    type Result = SmtQualifiedIdent<H>;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<SmtQualifiedIdent<H>, Self>, ParserError<H>> {
        let span = token.span();
        match self {
            QualifiedIdentParser::Start => match token.into_kind() {
                TokenKind::Symbol(name) => {
                    // simple ident
                    Ok(ControlFlow::Break(SmtQualifiedIdent::new_simple(name)))
                }
                TokenKind::ParenOpen => Ok(ControlFlow::Continue(Self::Open)),
                _ => {
                    let kind = CategoryParserErrorKind::ExpectedIdent;
                    Err(CategoryParserError::new(kind, span).into())
                }
            },
            QualifiedIdentParser::Open => {
                match token.kind() {
                    TokenKind::Reserved(Reserved::Underscore) => {
                        // unqualified indexed ident
                        Ok(ControlFlow::Continue(Self::UnqualifiedIndexed(
                            IdentParser::after_underscore(),
                        )))
                    }
                    TokenKind::Reserved(Reserved::As) => {
                        // qualified ident, parse identifier next
                        Ok(ControlFlow::Continue(Self::QualifiedIdent(
                            IdentParser::new(),
                        )))
                    }
                    _ => {
                        let kind = CategoryParserErrorKind::ExpectedToken(&[
                            TokenType::Reserved(Reserved::Underscore),
                            TokenType::Reserved(Reserved::As),
                        ]);
                        Err(CategoryParserError::new(kind, span).into())
                    }
                }
            }
            QualifiedIdentParser::UnqualifiedIndexed(parser) => {
                match parser.progress(handler, token)? {
                    ControlFlow::Continue(parser) => Ok(ControlFlow::Continue(
                        QualifiedIdentParser::UnqualifiedIndexed(parser),
                    )),
                    ControlFlow::Break(ident) => {
                        // the closing parenthesis was already consumed by the IdentParser
                        Ok(ControlFlow::Break(SmtQualifiedIdent::new_unqualified(
                            ident,
                        )))
                    }
                }
            }
            QualifiedIdentParser::QualifiedIdent(parser) => {
                match parser.progress(handler, token)? {
                    ControlFlow::Continue(parser) => Ok(ControlFlow::Continue(
                        QualifiedIdentParser::QualifiedIdent(parser),
                    )),
                    ControlFlow::Break(ident) => {
                        // we still need to parse the sort and closing parenthesis
                        Ok(ControlFlow::Continue(Self::QualifiedSort(
                            ident,
                            SortParser::new(),
                        )))
                    }
                }
            }
            QualifiedIdentParser::QualifiedSort(ident, parser) => {
                match parser.progress(handler, token)? {
                    ControlFlow::Continue(parser) => Ok(ControlFlow::Continue(
                        QualifiedIdentParser::QualifiedSort(ident, parser),
                    )),
                    ControlFlow::Break(sort) => {
                        // we still need to parse the closing parenthesis
                        Ok(ControlFlow::Continue(Self::QualifiedClose(ident, sort)))
                    }
                }
            }
            QualifiedIdentParser::QualifiedClose(ident, sort) => {
                expect_close_paren(token)?;
                Ok(ControlFlow::Break(SmtQualifiedIdent::new_qualified(
                    ident, sort,
                )))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::read::parser::category::tests::{Printing, assert_error, parse_all, run};

    fn name(qualified_ident: &SmtQualifiedIdent<Printing>) -> &[u8] {
        qualified_ident.ident.name.as_slice()
    }

    #[test]
    fn simple_symbol() {
        let qi = parse_all::<QualifiedIdentParser<Printing>>(b"x");
        assert_eq!(name(&qi), b"x");
        assert!(qi.ident.indices.is_empty());
        assert_eq!(qi.sort, None);

        // a plain symbol is a single token; the rest is left for the caller
        let (qi, left) = run::<QualifiedIdentParser<Printing>>(b"x y").expect("valid");
        assert_eq!(name(&qi), b"x");
        assert_eq!(left, 1);
    }

    #[test]
    fn unqualified_indexed() {
        let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(_ extract 7 0)");
        assert_eq!(name(&qi), b"extract");
        assert_eq!(qi.ident.indices.len(), 2);
        assert_eq!(qi.sort, None);

        // the ident's own closing parenthesis ends the qualified ident;
        // the parser must not wait for another token after it
        let (qi, left) = run::<QualifiedIdentParser<Printing>>(b"(_ bv5 8) y").expect("valid");
        assert_eq!(name(&qi), b"bv5");
        assert_eq!(left, 1);
    }

    #[test]
    fn qualified_simple_ident() {
        let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(as x Bool)");
        assert_eq!(name(&qi), b"x");
        assert!(qi.ident.indices.is_empty());
        assert_eq!(qi.sort.as_deref(), Some("Bool"));
    }

    #[test]
    fn qualified_indexed_ident() {
        // the inner ident parser continues over multiple tokens
        let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(as (_ f 1) Bool)");
        assert_eq!(name(&qi), b"f");
        assert_eq!(qi.ident.indices.len(), 1);
        assert_eq!(qi.sort.as_deref(), Some("Bool"));
    }

    #[test]
    fn qualified_indexed_sort() {
        let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(as x (_ BitVec 8))");
        assert_eq!(name(&qi), b"x");
        assert_eq!(qi.sort.as_deref(), Some("(_ BitVec 8)"));
    }

    #[test]
    fn qualified_applied_sort() {
        // the sort parser handles applied sorts inside `as` as well
        let qi = parse_all::<QualifiedIdentParser<Printing>>(b"(as x (Array Int Int))");
        assert_eq!(name(&qi), b"x");
        assert_eq!(qi.sort.as_deref(), Some("(Array Int Int)"));
    }

    #[test]
    fn entry_points() {
        // the callers that already consumed `(`, `( _` or `( as`
        // start in the corresponding state
        assert!(matches!(
            QualifiedIdentParser::<Printing>::new(),
            QualifiedIdentParser::Start
        ));
        assert!(matches!(
            QualifiedIdentParser::<Printing>::after_open_paren(),
            QualifiedIdentParser::Open
        ));
        assert!(matches!(
            QualifiedIdentParser::<Printing>::after_underscore(),
            QualifiedIdentParser::UnqualifiedIndexed(_)
        ));
        assert!(matches!(
            QualifiedIdentParser::<Printing>::after_as(),
            QualifiedIdentParser::QualifiedIdent(_)
        ));
    }

    #[test]
    fn errors() {
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"1", 0, 1);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIdent),
            "{err:?}"
        );

        // after `(` only `_` or `as` may follow
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"(f 1)", 1, 2);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[
                    TokenType::Reserved(Reserved::Underscore),
                    TokenType::Reserved(Reserved::As)
                ])
            ),
            "{err:?}"
        );

        // `as` must be followed by an identifier
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as)", 3, 4);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIdent),
            "{err:?}"
        );
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as 1 Bool)", 4, 5);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedIdent),
            "{err:?}"
        );

        // ... and a sort
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as x)", 5, 6);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedSort),
            "{err:?}"
        );

        // ... and the closing parenthesis
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as x Bool z)", 11, 12);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );

        // EOF while waiting for the closing parenthesis
        let err = assert_error::<QualifiedIdentParser<Printing>>(b"(as x Bool", 10, 10);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
            ),
            "{err:?}"
        );
    }
}

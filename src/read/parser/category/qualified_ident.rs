use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIdent, SmtQualifiedIdent,
    read::parser::{
        CloseParenParser, ParserError,
        category::{
            CategoryParser, CategoryParserError, CategoryParserErrorKind, ident::IdentParser,
            sort::SortParser,
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
            QualifiedIdentParser::Start => match token.kind() {
                TokenKind::Symbol(name) => {
                    // simple ident
                    Ok(ControlFlow::Break(SmtQualifiedIdent::new_simple(
                        name.into_owned(),
                    )))
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
                CloseParenParser::expect(token)?;
                Ok(ControlFlow::Break(SmtQualifiedIdent::new_qualified(
                    ident, sort,
                )))
            }
        }
    }
}

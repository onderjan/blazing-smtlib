use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIdent, SmtSort,
    read::parser::{
        CategoryParserError, ParserError,
        category::{CategoryParser, ident::IdentParser},
    },
    token::{Reserved, Token, TokenKind},
};

pub enum SortParser {
    Start,
    Open,
    Ident(IdentParser),
}

impl<H: SmtHandler> CategoryParser<H> for SortParser {
    type Result = H::Sort;

    fn init() -> Self {
        Self::Start
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Sort, Self>, ParserError<H>> {
        let sort = match self {
            SortParser::Start => match token.into_kind() {
                TokenKind::Symbol(name) => {
                    // the sort consists just of a non-indexed ident
                    let ident = SmtIdent {
                        name,
                        indices: Vec::new(),
                    };
                    SmtSort::Ident(ident)
                }
                TokenKind::ParenOpen => return Ok(ControlFlow::Continue(Self::Open)),
                _ => return Err(CategoryParserError::ExpectedSort.into()),
            },
            SortParser::Open => match token.into_kind() {
                TokenKind::Reserved(Reserved::Underscore) => {
                    return Ok(ControlFlow::Continue(SortParser::Ident(
                        IdentParser::after_underscore(),
                    )));
                }
                _ => {
                    // TODO: should parse sort ident here
                    return Err(CategoryParserError::ExpectedSortInner.into());
                }
            },

            SortParser::Ident(state) => match state.progress(handler, token)? {
                ControlFlow::Continue(state) => {
                    return Ok(ControlFlow::Continue(SortParser::Ident(state)));
                }
                ControlFlow::Break(ident) => SmtSort::Ident(ident),
            },
        };

        let sort = handler
            .handle_sort(sort)
            .map_err(ParserError::HandlerError)?;
        Ok(ControlFlow::Break(sort))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::read::parser::category::tests::{assert_error, parse_all, run};

    #[test]
    fn simple_sort() {
        assert_eq!(parse_all::<SortParser>(b"Bool"), "Bool");
        assert_eq!(parse_all::<SortParser>(b"|my sort|"), "my sort");

        let (sort, left) = run::<SortParser>(b"Int Bool").expect("valid");
        assert_eq!(sort, "Int");
        assert_eq!(left, 1);
    }

    #[test]
    fn indexed_sort() {
        assert_eq!(parse_all::<SortParser>(b"(_ BitVec 8)"), "(_ BitVec 8)");
        assert_eq!(
            parse_all::<SortParser>(b"(_ FloatingPoint 8 24)"),
            "(_ FloatingPoint 8 24)"
        );
    }

    #[test]
    fn errors() {
        let err = assert_error::<SortParser>(b"1", 0, 1);
        assert!(matches!(err, CategoryParserError::ExpectedSort), "{err:?}");

        let err = assert_error::<SortParser>(b")", 0, 1);
        assert!(matches!(err, CategoryParserError::ExpectedSort), "{err:?}");

        let err = assert_error::<SortParser>(b"", 0, 0);
        assert!(matches!(err, CategoryParserError::ExpectedSort), "{err:?}");

        // sort applications like (Array Int Int) are not supported yet
        let err = assert_error::<SortParser>(b"(Array Int Int)", 1, 6);
        assert!(matches!(err, CategoryParserError::ExpectedSortInner), "{err:?}");

        // errors inside the indexed identifier are reported by the identifier parser
        let err = assert_error::<SortParser>(b"(_ BitVec)", 9, 10);
        assert!(matches!(err, CategoryParserError::RequiredIndices), "{err:?}");
    }
}

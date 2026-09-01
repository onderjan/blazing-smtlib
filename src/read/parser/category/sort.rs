use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtIdent, SmtSort,
    read::parser::{
        ParserError,
        category::{CategoryParser, CategoryParserErrorKind, ident::IdentParser},
        handle_err,
    },
    token::{Reserved, Token, TokenKind},
};

enum SortState {
    Start,
    Open,
    IdentOnly(IdentParser),
    StartingIdent(IdentParser),
}

struct SortLevel<H: SmtHandler> {
    ident: SmtIdent,
    applied: Vec<H::Sort>,
}

pub struct SortParser<H: SmtHandler> {
    state: SortState,
    levels: Vec<SortLevel<H>>,
}

impl<H: SmtHandler> SortParser<H> {
    pub fn new() -> Self {
        Self {
            state: SortState::Start,
            levels: Vec::new(),
        }
    }
}

impl<H: SmtHandler> Default for SortParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for SortParser<H> {
    type Result = H::Sort;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Sort, Self>, ParserError<H>> {
        let (mut levels, sort) = match self.progress_last_level(handler, token)? {
            ControlFlow::Continue(parser) => return Ok(ControlFlow::Continue(parser)),
            ControlFlow::Break((levels, sort)) => (levels, sort),
        };
        if let Some(last_level) = levels.last_mut() {
            // we need to append to the last level
            last_level.applied.push(sort);
            let state = SortState::Start;
            Ok(ControlFlow::Continue(Self { state, levels }))
        } else {
            // this is the root level, we are done
            Ok(ControlFlow::Break(sort))
        }
    }
}

type SortProgressOk<H, P> = ControlFlow<(Vec<SortLevel<H>>, <H as SmtHandler>::Sort), P>;

impl<H: SmtHandler> SortParser<H> {
    fn progress_last_level(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<SortProgressOk<H, Self>, ParserError<H>> {
        let span = token.span();
        let mut levels = self.levels;

        let state = match self.state {
            SortState::Start => match token.kind() {
                TokenKind::Symbol(name) => {
                    // the sort consists just of a single-symbol ident
                    let ident = SmtIdent::new_simple(name.into_owned());
                    let sort = handle_err(handler.handle_sort(SmtSort::new_simple(ident)), span)?;

                    return Ok(ControlFlow::Break((levels, sort)));
                }
                TokenKind::ParenOpen => SortState::Open,
                kind => {
                    if matches!(kind, TokenKind::ParenClose) {
                        // closes the last level if it exists
                        if let Some(last_level) = levels.pop() {
                            // if the sort committed to having applications,
                            // there must be at least one of them
                            if last_level.applied.is_empty() {
                                return Err(ParserError::category_error(
                                    CategoryParserErrorKind::EmptySortApplication,
                                    span,
                                ));
                            }

                            let sort = SmtSort::new(last_level.ident, last_level.applied);
                            let sort = handle_err(handler.handle_sort(sort), span)?;
                            return Ok(ControlFlow::Break((levels, sort)));
                        }
                    }

                    let kind = CategoryParserErrorKind::ExpectedSort;
                    return Err(ParserError::category_error(kind, span));
                }
            },
            SortState::Open => match token.kind() {
                TokenKind::Reserved(Reserved::Underscore) => {
                    // this is a sort consisting just of an indexed identifier
                    SortState::IdentOnly(IdentParser::after_underscore())
                }
                TokenKind::Symbol(name) => {
                    // non-indexed ident starting sort
                    let ident = SmtIdent::new_simple(name.into_owned());
                    levels.push(SortLevel {
                        ident,
                        applied: Vec::new(),
                    });
                    SortState::Start
                }
                TokenKind::ParenOpen => {
                    // indexed ident starting sort
                    SortState::StartingIdent(IdentParser::after_open_paren())
                }
                _ => {
                    let kind = CategoryParserErrorKind::ExpectedSortInner;
                    return Err(ParserError::category_error(kind, span));
                }
            },
            SortState::IdentOnly(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => SortState::IdentOnly(parser),
                ControlFlow::Break(ident) => {
                    let sort = handle_err(handler.handle_sort(SmtSort::new_simple(ident)), span)?;
                    return Ok(ControlFlow::Break((levels, sort)));
                }
            },
            SortState::StartingIdent(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => SortState::StartingIdent(parser),
                ControlFlow::Break(ident) => {
                    // add a new level and start parsing the new sort
                    levels.push(SortLevel {
                        ident,
                        applied: Vec::new(),
                    });

                    SortState::Start
                }
            },
        };

        Ok(ControlFlow::Continue(Self { state, levels }))
    }
}

#[cfg(test)]
mod tests {
    use std::convert::Infallible;

    use super::*;
    use crate::{
        SmtAttributeValue, SmtKeyword, SmtSExpr, SmtSymbol, SmtTerm,
        read::{
            lexer::tests::lex_all,
            parser::{
                ParserErrorKind,
                category::tests::{Printing, assert_error, parse_all, run},
            },
        },
        token::TokenType,
    };

    #[test]
    fn simple_sort() {
        assert_eq!(parse_all::<SortParser<Printing>>(b"Bool"), "Bool");
        assert_eq!(parse_all::<SortParser<Printing>>(b"|my sort|"), "my sort");

        let (sort, left) = run::<SortParser<Printing>>(b"Int Bool").expect("valid");
        assert_eq!(sort, "Int");
        assert_eq!(left, 1);
    }

    #[test]
    fn indexed_sort() {
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"(_ BitVec 8)"),
            "(_ BitVec 8)"
        );
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"(_ FloatingPoint 8 24)"),
            "(_ FloatingPoint 8 24)"
        );
    }

    #[test]
    fn applied_sort() {
        assert_eq!(parse_all::<SortParser<Printing>>(b"(Set Int)"), "(Set Int)");
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"(Array Int Int)"),
            "(Array Int Int)"
        );

        // sorts nest in any argument position
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"(Array (Array Int Int) Int)"),
            "(Array (Array Int Int) Int)"
        );
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"(Array Int (Array Int Int))"),
            "(Array Int (Array Int Int))"
        );

        // the closing parenthesis ends the sort; the rest is left for the caller
        let (sort, left) = run::<SortParser<Printing>>(b"(Set Int) Bool").expect("valid");
        assert_eq!(sort, "(Set Int)");
        assert_eq!(left, 1);
    }

    #[test]
    fn applied_indexed_sort() {
        // indexed identifier as an argument sort
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"(Array (_ BitVec 8) Int)"),
            "(Array (_ BitVec 8) Int)"
        );

        // indexed identifier as the applied head
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"((_ FixedSizeList 4) Real)"),
            "((_ FixedSizeList 4) Real)"
        );

        // both at once
        assert_eq!(
            parse_all::<SortParser<Printing>>(b"((_ Tuple 2) (_ BitVec 8) (Set Int))"),
            "((_ Tuple 2) (_ BitVec 8) (Set Int))"
        );
    }

    #[test]
    fn errors() {
        let expected_sort = CategoryParserErrorKind::ExpectedSort;
        assert_eq!(
            assert_error::<SortParser<Printing>>(b"1", 0, 1),
            expected_sort
        );
        assert_eq!(
            assert_error::<SortParser<Printing>>(b")", 0, 1),
            expected_sort
        );
        assert_eq!(
            assert_error::<SortParser<Printing>>(b"", 0, 0),
            expected_sort
        );

        // unterminated applied sort runs into the end of input
        assert_eq!(
            assert_error::<SortParser<Printing>>(b"(Array Int", 10, 10),
            expected_sort
        );

        // after `(`, only `_`, a symbol, or `(` may follow
        let err = assert_error::<SortParser<Printing>>(b"(as x Bool)", 1, 3);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedSortInner),
            "{err:?}"
        );
        let err = assert_error::<SortParser<Printing>>(b"(1 2)", 1, 2);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedSortInner),
            "{err:?}"
        );
        let err = assert_error::<SortParser<Printing>>(b"()", 1, 2);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedSortInner),
            "{err:?}"
        );

        // an applied identifier must be applied to at least one sort
        let err = assert_error::<SortParser<Printing>>(b"(Int)", 4, 5);
        assert!(
            matches!(err, CategoryParserErrorKind::EmptySortApplication),
            "{err:?}"
        );
        let err = assert_error::<SortParser<Printing>>(b"((_ BitVec 8))", 13, 14);
        assert!(
            matches!(err, CategoryParserErrorKind::EmptySortApplication),
            "{err:?}"
        );

        // a parenthesized applied head must be an indexed identifier
        let err = assert_error::<SortParser<Printing>>(b"((Array) Int)", 2, 7);
        assert!(
            matches!(
                err,
                CategoryParserErrorKind::ExpectedToken(&[TokenType::Reserved(
                    Reserved::Underscore
                )])
            ),
            "{err:?}"
        );

        // errors inside the indexed identifier are reported by the identifier parser
        let err = assert_error::<SortParser<Printing>>(b"(_ BitVec)", 9, 10);
        assert!(
            matches!(err, CategoryParserErrorKind::EmptyIdentIndices),
            "{err:?}"
        );
    }

    /// Handler that only counts sorts, so deep nesting does not build huge strings.
    #[derive(Default)]
    struct Counting {
        sorts: usize,
    }

    impl SmtHandler for Counting {
        type Error = Infallible;
        type SExpr = ();
        type Attribute = ();
        type Sort = ();
        type Term = ();

        fn handle_sort(&mut self, _sort: SmtSort<Self>) -> Result<(), Infallible> {
            self.sorts += 1;
            Ok(())
        }
        fn handle_term(&mut self, _term: SmtTerm<Self>) -> Result<(), Infallible> {
            Ok(())
        }
        fn start_let(&mut self, _bindings: Vec<(SmtSymbol, ())>) -> Result<(), Infallible> {
            Ok(())
        }
        fn end_let(&mut self, _term: ()) -> Result<(), Infallible> {
            Ok(())
        }
        fn handle_s_expr(&mut self, _expr: SmtSExpr<Self>) -> Result<(), Infallible> {
            Ok(())
        }
        fn handle_attribute(
            &mut self,
            _name: SmtKeyword,
            _value: Option<SmtAttributeValue<Self>>,
        ) -> Result<(), Infallible> {
            Ok(())
        }
    }

    #[test]
    fn deep_nesting_does_not_overflow_the_stack() {
        // (Array (Array ... Int ... Int) Int) with a depth far beyond what recursion would survive
        const DEPTH: usize = 200_000;
        let mut input = Vec::with_capacity(DEPTH * 12 + 3);
        for _ in 0..DEPTH {
            input.extend_from_slice(b"(Array ");
        }
        input.extend_from_slice(b"Int");
        for _ in 0..DEPTH {
            input.extend_from_slice(b" Int)");
        }

        let mut handler = Counting::default();
        let mut parser = SortParser::<Counting>::default();
        let mut finished = false;
        for token in lex_all(&input).expect("valid input") {
            match parser.progress(&mut handler, token.as_token()) {
                Ok(ControlFlow::Continue(next)) => parser = next,
                Ok(ControlFlow::Break(())) => {
                    finished = true;
                    break;
                }
                Err(err) => {
                    let span = err.span();
                    match err.into_kind() {
                        ParserErrorKind::Category(kind) => panic!("{kind:?} at {span:?}"),
                        // the `Counting` handler never fails
                        ParserErrorKind::Handler(err) => match err {},
                    }
                }
            }
        }
        assert!(finished);
        // every applied `Array` sort plus every `Int` leaf
        assert_eq!(handler.sorts, 2 * DEPTH + 1);
    }
}

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

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

/// A parser that reads an SMT-LIB sort.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct SortParser<H: SmtHandler> {
    state: State,
    levels: Vec<Level<H>>,

    ident_parser: IdentParser,
}

/// Current sort parser state.
enum State {
    /// Waiting for the sort to start.
    Start,
    /// After reading "(".
    Open,
    /// The sort consists of only an identifier.
    ///
    /// Parsing delegates to the identifier parser.
    IdentOnly,
    /// The sort starts with an identifier.
    ///
    /// Parsing delegates to the identifier parser.
    /// After that, the sort will be pushed as a new level.
    StartingIdent,
}

/// A parsed-sort level.
///
/// Sorts here are waiting for a next applied sort
/// or a closing parenthesis.
struct Level<H: SmtHandler> {
    ident: SmtIdent,
    applied: Vec<H::Sort>,
}

impl<H: SmtHandler> SortParser<H> {
    pub fn new() -> Self {
        Self {
            state: State::Start,
            levels: Vec::new(),

            ident_parser: IdentParser::new(),
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
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Sort>, ParserError<H>> {
        let span = token.span();
        let flow = match self.state {
            State::Start => match token.kind() {
                TokenKind::Symbol(name) => {
                    // the sort consists just of a single-symbol ident
                    ControlFlow::Break(SmtSort::new_simple(SmtIdent::new_simple(name.into_owned())))
                }
                TokenKind::ParenOpen => {
                    // move the state to open
                    self.state = State::Open;
                    ControlFlow::Continue(())
                }
                TokenKind::ParenClose => {
                    match self.levels.pop() {
                        Some(last_level) => {
                            // close the last level
                            // if the sort committed to having applications,
                            // there must be at least one of them
                            if last_level.applied.is_empty() {
                                return Err(ParserError::category_error(
                                    CategoryParserErrorKind::EmptySortApplication,
                                    span,
                                ));
                            }
                            ControlFlow::Break(SmtSort::new(last_level.ident, last_level.applied))
                        }
                        None => {
                            // we just received ")"
                            return Err(ParserError::category_error(
                                CategoryParserErrorKind::ExpectedSort,
                                span,
                            ));
                        }
                    }
                }
                _ => {
                    return Err(ParserError::category_error(
                        CategoryParserErrorKind::ExpectedSort,
                        span,
                    ));
                }
            },
            State::Open => {
                // decide how to continue
                let state = match token.kind() {
                    TokenKind::Reserved(Reserved::Underscore) => {
                        // this is a sort consisting just of an indexed identifier
                        // start the ident parser after underscore
                        self.ident_parser = IdentParser::after_underscore();
                        State::IdentOnly
                    }
                    TokenKind::Symbol(name) => {
                        // non-indexed ident starting sort
                        let ident = SmtIdent::new_simple(name.into_owned());
                        self.levels.push(Level {
                            ident,
                            applied: Vec::new(),
                        });
                        State::Start
                    }
                    TokenKind::ParenOpen => {
                        // indexed ident starting sort
                        // start the ident parser after opening parenthesis
                        self.ident_parser = IdentParser::after_open_paren();
                        State::StartingIdent
                    }
                    _ => {
                        return Err(ParserError::category_error(
                            CategoryParserErrorKind::ExpectedSortInner,
                            span,
                        ));
                    }
                };
                self.state = state;
                ControlFlow::Continue(())
            }
            State::IdentOnly => self
                .ident_parser
                .progress(handler, token)?
                .map_break(SmtSort::new_simple),
            State::StartingIdent => match self.ident_parser.progress(handler, token)? {
                ControlFlow::Continue(()) => ControlFlow::Continue(()),
                ControlFlow::Break(ident) => {
                    // add a new level and start parsing the new sort
                    self.levels.push(Level {
                        ident,
                        applied: Vec::new(),
                    });
                    self.state = State::Start;
                    ControlFlow::Continue(())
                }
            },
        };

        let ControlFlow::Break(sort) = flow else {
            return Ok(ControlFlow::Continue(()));
        };

        // we have parsed a sort, reset the state
        self.state = State::Start;
        let sort = handle_err(handler.handle_sort(sort), span)?;

        if let Some(last_level) = self.levels.last_mut() {
            // we need to append to the last level
            last_level.applied.push(sort);
            Ok(ControlFlow::Continue(()))
        } else {
            // this is the root level, we are done
            Ok(ControlFlow::Break(sort))
        }
    }
}

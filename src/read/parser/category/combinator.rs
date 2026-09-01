use std::ops::ControlFlow;

use crate::{
    SmtHandler,
    read::parser::{CategoryParser, CloseParenParser, OpenParenParser, ParserError},
    token::{Token, TokenKind},
};

/// Parses using the first parser, then the second, then returns the result tuple.
///
/// Preserves self-reset: if the inner parsers are self-resetting,
/// moves back into the default state before returning Break.
pub struct PairParser<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> {
    first: P1,
    second: P2,
    first_result: Option<P1::Result>,
}

impl<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> PairParser<H, P1, P2> {
    pub fn new() -> Self {
        Self {
            first: P1::default(),
            second: P2::default(),
            first_result: None,
        }
    }
}

impl<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> Default
    for PairParser<H, P1, P2>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler, P1: CategoryParser<H>, P2: CategoryParser<H>> CategoryParser<H>
    for PairParser<H, P1, P2>
{
    type Result = (P1::Result, P2::Result);

    fn restart(&mut self) {
        self.first.restart();
        self.second.restart();
        self.first_result = None;
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        match self.first_result.take() {
            None => {
                // progress the first parser, emplace the first result if it breaks
                if let ControlFlow::Break(first) = self.first.progress(handler, token)? {
                    self.first_result = Some(first);
                }
            }
            Some(first) => {
                // progress the second parser
                // put the first result back if it continues
                // break with the result tuple if it breaks
                match self.second.progress(handler, token)? {
                    ControlFlow::Continue(()) => self.first_result = Some(first),
                    ControlFlow::Break(second) => return Ok(ControlFlow::Break((first, second))),
                }
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Parses using the inner parser, then parses a closing parenthesis, then returns the inner result.
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub struct ClosedParser<H: SmtHandler, P: CategoryParser<H>> {
    inner: PairParser<H, P, CloseParenParser>,
}

impl<H: SmtHandler, P: CategoryParser<H>> ClosedParser<H, P> {
    pub fn new() -> Self {
        Self {
            inner: PairParser::default(),
        }
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> Default for ClosedParser<H, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for ClosedParser<H, P> {
    type Result = P::Result;

    fn restart(&mut self) {
        self.inner.restart();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        Ok(self
            .inner
            .progress(handler, token)?
            .map_break(|(result, ())| result))
    }
}

/// Parses an opening parenthesis, then parses using the inner parser.
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub struct OpenedParser<H: SmtHandler, P: CategoryParser<H>> {
    inner: PairParser<H, OpenParenParser, P>,
}

impl<H: SmtHandler, P: CategoryParser<H>> OpenedParser<H, P> {
    pub fn new() -> Self {
        Self {
            inner: PairParser::default(),
        }
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> Default for OpenedParser<H, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for OpenedParser<H, P> {
    type Result = P::Result;

    fn restart(&mut self) {
        self.inner.restart();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        Ok(self
            .inner
            .progress(handler, token)?
            .map_break(|((), result)| result))
    }
}

/// Parses tokens enclosed by parentheses using the inner parser, returning the inner result.
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub type ParenParser<H, P> = OpenedParser<H, ClosedParser<H, P>>;

/// Parses multiple items followed by a closing parenthesis, returning the results as a vector.
///
/// Note that this parser does not consume the opening parenthesis the closing would belong to,
/// for that, use `ParenMultipleParser`.
///
/// Keeps the state of the inner parser after break for parsing a next element.
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub struct ClosedMultipleParser<H: SmtHandler, P: CategoryParser<H>> {
    outside: bool,
    inner: P,
    results: Vec<P::Result>,
}

impl<H: SmtHandler, P: CategoryParser<H>> ClosedMultipleParser<H, P> {
    pub fn new() -> Self {
        Self {
            outside: true,
            inner: P::default(),
            results: Vec::new(),
        }
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> Default for ClosedMultipleParser<H, P> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler, P: CategoryParser<H>> CategoryParser<H> for ClosedMultipleParser<H, P> {
    type Result = Vec<P::Result>;

    fn restart(&mut self) {
        self.outside = true;
        self.inner.restart();
        self.results.clear();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<Vec<P::Result>>, ParserError<H::Error>> {
        // if we are outside, closing parenthesis ends processing
        if self.outside && matches!(token.kind(), TokenKind::ParenClose) {
            let results = self.results.drain(..).collect();
            return Ok(ControlFlow::Break(results));
        }

        // we are no longer outside and should parse normally
        self.outside = false;
        if let ControlFlow::Break(element) = self.inner.progress(handler, token)? {
            // add element, we are now outside (if a closing parenthesis arrives, we will break)
            self.results.push(element);
            self.outside = true;
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Parses multiple items enclosed by parentheses, returning the results as a vector.
///
/// Keeps the state of the inner parser after break for parsing a next element.
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub type ParenMultipleParser<H, P> = OpenedParser<H, ClosedMultipleParser<H, P>>;

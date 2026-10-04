use std::ops::ControlFlow;

use crate::{
    SmtHandler,
    read::parser::{
        CloseParenParser, OpenParenParser, Parser, ParserError, ParserResources, SyntaxErrorKind,
        category::resources::ClosedMultipleResource,
    },
    token::{SmtBatchCursor, SmtTokenCategory},
};

/// Parses using the first parser, then the second, then returns the result tuple.
///
/// Preserves self-reset: if the inner parsers are self-resetting,
/// moves back into the default state before returning Break.
pub struct PairParser<H: SmtHandler, P1: Parser<H>, P2: Parser<H>> {
    first: P1,
    second: P2,
    first_result: Option<P1::Result>,
}

impl<H: SmtHandler, P1: Parser<H>, P2: Parser<H>> PairParser<H, P1, P2> {
    pub fn new(first: P1, second: P2) -> Self {
        Self {
            first,
            second,
            first_result: None,
        }
    }
}

impl<H: SmtHandler, P1: Parser<H> + Default, P2: Parser<H> + Default> Default
    for PairParser<H, P1, P2>
{
    fn default() -> Self {
        Self::new(P1::default(), P2::default())
    }
}

impl<H: SmtHandler, P1: Parser<H>, P2: Parser<H>> Parser<H> for PairParser<H, P1, P2> {
    type Result = (P1::Result, P2::Result);

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        // progress the first parser until it breaks or the tokens run out
        if self.first_result.is_none() {
            match self.first.parse(handler, resources, cursor)? {
                ControlFlow::Continue(()) => return Ok(ControlFlow::Continue(())),
                ControlFlow::Break(first) => {
                    self.first_result = Some(first);
                    // move to progressing the second parser
                }
            }
        }
        // progress the second parser; the first result stays until it breaks
        match self.second.parse(handler, resources, cursor)? {
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(second) => {
                let first = self
                    .first_result
                    .take()
                    .expect("the first result is kept until the second parser breaks");
                Ok(ControlFlow::Break((first, second)))
            }
        }
    }
}

/// Parses using the inner parser, then parses a closing parenthesis, then returns the inner result.
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub struct ClosedParser<H: SmtHandler, P: Parser<H>> {
    inner: PairParser<H, P, CloseParenParser>,
}

impl<H: SmtHandler, P: Parser<H>> ClosedParser<H, P> {
    pub fn new(inner: P) -> Self {
        Self {
            inner: PairParser::new(inner, CloseParenParser),
        }
    }
}

impl<H: SmtHandler, P: Parser<H> + Default> Default for ClosedParser<H, P> {
    fn default() -> Self {
        Self::new(P::default())
    }
}

impl<H: SmtHandler, P: Parser<H>> Parser<H> for ClosedParser<H, P> {
    type Result = P::Result;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        Ok(self
            .inner
            .parse(handler, resources, cursor)?
            .map_break(|(result, ())| result))
    }
}

/// Parses an opening parenthesis, then parses using the inner parser.
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub struct OpenedParser<H: SmtHandler, P: Parser<H>> {
    inner: PairParser<H, OpenParenParser, P>,
}

impl<H: SmtHandler, P: Parser<H>> OpenedParser<H, P> {
    pub fn new(inner: P) -> Self {
        Self {
            inner: PairParser::new(OpenParenParser, inner),
        }
    }
}

impl<H: SmtHandler, P: Parser<H> + Default> Default for OpenedParser<H, P> {
    fn default() -> Self {
        Self::new(P::default())
    }
}

impl<H: SmtHandler, P: Parser<H>> Parser<H> for OpenedParser<H, P> {
    type Result = P::Result;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        Ok(self
            .inner
            .parse(handler, resources, cursor)?
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
pub struct ClosedMultipleParser<H: SmtHandler, P: Parser<H>> {
    inner: P,
    resource: ClosedMultipleResource<P::Result>,
}

impl<H: SmtHandler, P: Parser<H>> ClosedMultipleParser<H, P> {
    pub fn new(inner: P) -> Self {
        Self {
            inner,
            resource: ClosedMultipleResource::new(),
        }
    }
}

impl<H: SmtHandler, P: Parser<H> + Default> Default for ClosedMultipleParser<H, P> {
    fn default() -> Self {
        Self::new(P::default())
    }
}

impl<H: SmtHandler, P: Parser<H>> Parser<H> for ClosedMultipleParser<H, P> {
    type Result = Vec<P::Result>;

    #[inline]
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Vec<P::Result>>, ParserError<H::Error>> {
        self.resource.parse(cursor, |cursor| {
            self.inner.parse(handler, resources, cursor)
        })
    }
}

/// Parses multiple items enclosed by parentheses, returning the results as a vector.
///
/// Keeps the state of the inner parser after break for parsing a next element.
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub type ParenMultipleParser<H, P> = OpenedParser<H, ClosedMultipleParser<H, P>>;

/// Parser that parses a number of items ending with a closing parenthesis up to some maximum.
///
/// The maximum can be changed by [`ClosedMaximumParser::set_maximum`].
pub struct ClosedMaximumParser<H: SmtHandler, P: Parser<H>> {
    max_elements: usize,

    outside: bool,
    results: Vec<P::Result>,
    inner: P,
}

impl<H: SmtHandler, P: Parser<H>> ClosedMaximumParser<H, P> {
    pub fn new(inner: P, max_elements: usize) -> Self {
        Self {
            max_elements,

            outside: true,
            results: Vec::new(),
            inner,
        }
    }

    /// Sets the maximum number of items to be parsed.
    ///
    /// The maximum is only applied when deciding whether
    /// parsing a next element is allowed and does not affect
    /// previously parsed elements or the currently parsed element,
    /// meaning the parser may return more elements than
    /// the currently set maximum if this function is called
    /// in the middle of parsing elements.
    pub fn set_maximum(&mut self, max_elements: usize) {
        self.max_elements = max_elements;
    }

    pub fn max_elements(&self) -> usize {
        self.max_elements
    }
}

impl<H: SmtHandler, P: Parser<H>> Parser<H> for ClosedMaximumParser<H, P> {
    type Result = Vec<P::Result>;

    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Vec<P::Result>>, ParserError<H::Error>> {
        while let Some(peeked) = cursor.peek() {
            if self.outside {
                // we are outside, a closing parenthesis ends processing
                if matches!(peeked.category(), SmtTokenCategory::ParenClose) {
                    cursor.advance(1);
                    let results = self.results.drain(..).collect();
                    return Ok(ControlFlow::Break(results));
                }

                if self.results.len() >= self.max_elements {
                    // we cannot allow this element
                    // so the closing parenthesis was the only allowed choice here
                    // as we decided to reject based on the peeked token,
                    // it counts as consumed, so we need to advance
                    cursor.advance(1);
                    return Err(ParserError::category_error(
                        SyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose]),
                        peeked.span(),
                    ));
                }

                // we are no longer outside
                self.outside = false;
            }
            // we are inside, parse the element using the inner parser
            match self.inner.parse(handler, resources, cursor)? {
                ControlFlow::Continue(()) => return Ok(ControlFlow::Continue(())),
                ControlFlow::Break(element) => {
                    // add element, we are back outside
                    self.results.push(element);
                    self.outside = true;
                }
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Parser that parses a number of items enclosed in parentheses up to some maximum.
///
/// The maximum can be changed by [`ParenMaximumParser::set_maximum`].
pub struct ParenMaximumParser<H: SmtHandler, P: Parser<H>> {
    is_opened: bool,
    inner: ClosedMaximumParser<H, P>,
}

impl<H: SmtHandler, P: Parser<H>> ParenMaximumParser<H, P> {
    pub fn new(inner: P, max_elements: usize) -> Self {
        Self {
            is_opened: false,
            inner: ClosedMaximumParser::new(inner, max_elements),
        }
    }

    /// Sets the maximum number of items to be parsed.
    ///
    /// The maximum is only applied when deciding whether
    /// parsing a next element is allowed and does not affect
    /// previously parsed elements or the currently parsed element,
    /// meaning the parser may return more elements than
    /// the currently set maximum if this function is called
    /// in the middle of parsing elements.
    pub fn set_maximum(&mut self, max_elements: usize) {
        self.inner.set_maximum(max_elements);
    }

    pub fn max_elements(&self) -> usize {
        self.inner.max_elements()
    }
}

impl<H: SmtHandler, P: Parser<H>> Parser<H> for ParenMaximumParser<H, P> {
    type Result = Vec<P::Result>;

    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Vec<P::Result>>, ParserError<H::Error>> {
        loop {
            if self.is_opened {
                match self.inner.parse(handler, resources, cursor)? {
                    ControlFlow::Continue(()) => return Ok(ControlFlow::Continue(())),
                    ControlFlow::Break(result) => {
                        // we are done, reset open and break
                        self.is_opened = false;
                        return Ok(ControlFlow::Break(result));
                    }
                }
            } else {
                // not opened yet, expect opening parenthesis
                let Some(token) = cursor.next() else {
                    return Ok(ControlFlow::Continue(()));
                };
                OpenParenParser::expect(token)?;
                self.is_opened = true;
            }
        }
    }
}

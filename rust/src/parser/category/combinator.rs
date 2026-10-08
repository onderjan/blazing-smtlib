use std::ops::ControlFlow;

use crate::{
    SmtHandler,
    parser::{
        SmtCloseParenParser, SmtOpenParenParser, SmtParse, SmtParseError, SmtParseState,
        SmtSyntaxErrorKind,
    },
    token::{SmtProduce, SmtTokenCategory},
};

/// Parses using the first parser, then the second, then returns the result tuple.
///
/// Preserves self-reset: if the inner parsers are self-resetting,
/// moves back into the default state before returning Break.
pub struct SmtPairParser<H: SmtHandler, P1: SmtParse<H>, P2: SmtParse<H>> {
    first: P1,
    second: P2,
    first_result: Option<P1::Result>,
}

impl<H: SmtHandler, P1: SmtParse<H>, P2: SmtParse<H>> SmtPairParser<H, P1, P2> {
    pub fn new(first: P1, second: P2) -> Self {
        Self {
            first,
            second,
            first_result: None,
        }
    }
}

impl<H: SmtHandler, P1: SmtParse<H> + Default, P2: SmtParse<H> + Default> Default
    for SmtPairParser<H, P1, P2>
{
    fn default() -> Self {
        Self::new(P1::default(), P2::default())
    }
}

impl<H: SmtHandler, P1: SmtParse<H>, P2: SmtParse<H>> SmtParse<H> for SmtPairParser<H, P1, P2> {
    type Result = (P1::Result, P2::Result);

    #[inline]
    fn parse<'a, C: SmtProduce<'a>>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        // progress the first parser until it breaks or the tokens run out
        if self.first_result.is_none() {
            match self.first.parse(handler, parse_state, cursor)? {
                ControlFlow::Continue(()) => return Ok(ControlFlow::Continue(())),
                ControlFlow::Break(first) => {
                    self.first_result = Some(first);
                    // move to progressing the second parser
                }
            }
        }
        // progress the second parser; the first result stays until it breaks
        match self.second.parse(handler, parse_state, cursor)? {
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
pub struct SmtClosedParser<H: SmtHandler, P: SmtParse<H>> {
    inner: SmtPairParser<H, P, SmtCloseParenParser>,
}

impl<H: SmtHandler, P: SmtParse<H>> SmtClosedParser<H, P> {
    pub fn new(inner: P) -> Self {
        Self {
            inner: SmtPairParser::new(inner, SmtCloseParenParser),
        }
    }
}

impl<H: SmtHandler, P: SmtParse<H> + Default> Default for SmtClosedParser<H, P> {
    fn default() -> Self {
        Self::new(P::default())
    }
}

impl<H: SmtHandler, S: SmtParse<H>> SmtParse<H> for SmtClosedParser<H, S> {
    type Result = S::Result;

    #[inline]
    fn parse<'a, C: SmtProduce<'a>>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        Ok(self
            .inner
            .parse(handler, parse_state, cursor)?
            .map_break(|(result, ())| result))
    }
}

/// Parses an opening parenthesis, then parses using the inner parser.
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub struct SmtOpenedParser<H: SmtHandler, P: SmtParse<H>> {
    inner: SmtPairParser<H, SmtOpenParenParser, P>,
}

impl<H: SmtHandler, P: SmtParse<H>> SmtOpenedParser<H, P> {
    pub fn new(inner: P) -> Self {
        Self {
            inner: SmtPairParser::new(SmtOpenParenParser, inner),
        }
    }
}

impl<H: SmtHandler, P: SmtParse<H> + Default> Default for SmtOpenedParser<H, P> {
    fn default() -> Self {
        Self::new(P::default())
    }
}

impl<H: SmtHandler, P: SmtParse<H>> SmtParse<H> for SmtOpenedParser<H, P> {
    type Result = P::Result;

    #[inline]
    fn parse<'a, C: SmtProduce<'a>>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        Ok(self
            .inner
            .parse(handler, parse_state, cursor)?
            .map_break(|((), result)| result))
    }
}

/// Parses tokens enclosed by parentheses using the inner parser, returning the inner result.
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub type SmtParenParser<H, P> = SmtOpenedParser<H, SmtClosedParser<H, P>>;

/// Parses multiple items followed by a closing parenthesis, returning the results as a vector.
///
/// Note that this parser does not consume the opening parenthesis the closing would belong to,
/// for that, use `SmtParenMultipleParser`.
///
/// Keeps the state of the inner parser after break for parsing a next element.
///
/// Preserves self-reset: if the inner parser is self-resetting,
/// moves back into the default state before returning Break.
pub struct SmtClosedMultipleParser<H: SmtHandler, P: SmtParse<H>> {
    inner: P,
    resource: ClosedMultipleResource<P::Result>,
}

impl<H: SmtHandler, P: SmtParse<H>> SmtClosedMultipleParser<H, P> {
    pub fn new(inner: P) -> Self {
        Self {
            inner,
            resource: ClosedMultipleResource::new(),
        }
    }
}

impl<H: SmtHandler, P: SmtParse<H> + Default> Default for SmtClosedMultipleParser<H, P> {
    fn default() -> Self {
        Self::new(P::default())
    }
}

impl<H: SmtHandler, P: SmtParse<H>> SmtParse<H> for SmtClosedMultipleParser<H, P> {
    type Result = Vec<P::Result>;

    #[inline]
    fn parse<'a, C: SmtProduce<'a>>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<Vec<P::Result>>, SmtParseError<H::Error>> {
        self.resource.parse(cursor, |cursor| {
            self.inner.parse(handler, parse_state, cursor)
        })
    }
}

/// A resource that stores multiple elements closed by a parenthesis.
pub(crate) struct ClosedMultipleResource<T> {
    outside: bool,
    items: Vec<T>,
}

impl<T> ClosedMultipleResource<T> {
    pub(crate) fn new() -> Self {
        Self {
            outside: true,
            items: Vec::new(),
        }
    }

    pub(crate) fn parse<'a, C: SmtProduce<'a>, E>(
        &mut self,
        cursor: &mut C,
        mut element: impl FnMut(&mut C) -> Result<ControlFlow<T>, SmtParseError<E>>,
    ) -> Result<ControlFlow<Vec<T>>, SmtParseError<E>> {
        while let Some(token) = cursor.peek() {
            if self.outside {
                // we are outside, a closing parenthesis ends processing
                if matches!(token.category(), SmtTokenCategory::ParenClose) {
                    // consume the peeked closing parenthesis
                    let _ = cursor.next();
                    return Ok(ControlFlow::Break(self.items.drain(..).collect()));
                }
                // we are no longer outside
                self.outside = false;
            }
            // we are inside, parse the element using the inner parser
            match element(cursor)? {
                ControlFlow::Continue(()) => return Ok(ControlFlow::Continue(())),
                ControlFlow::Break(item) => {
                    // add element, we are back outside
                    self.items.push(item);
                    self.outside = true;
                }
            }
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
pub type SmtParenMultipleParser<H, P> = SmtOpenedParser<H, SmtClosedMultipleParser<H, P>>;

/// Parser that parses a number of items ending with a closing parenthesis up to some maximum.
///
/// The maximum can be changed by [`SmtClosedMaximumParser::set_maximum`].
pub struct SmtClosedMaximumParser<H: SmtHandler, P: SmtParse<H>> {
    max_elements: usize,

    outside: bool,
    results: Vec<P::Result>,
    inner: P,
}

impl<H: SmtHandler, P: SmtParse<H>> SmtClosedMaximumParser<H, P> {
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

impl<H: SmtHandler, P: SmtParse<H>> SmtParse<H> for SmtClosedMaximumParser<H, P> {
    type Result = Vec<P::Result>;

    fn parse<'a, C: SmtProduce<'a>>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<Vec<P::Result>>, SmtParseError<H::Error>> {
        while let Some(peeked) = cursor.peek() {
            if self.outside {
                // we are outside, a closing parenthesis ends processing
                if matches!(peeked.category(), SmtTokenCategory::ParenClose) {
                    // consume the peeked closing parenthesis
                    let _ = cursor.next();
                    let results = self.results.drain(..).collect();
                    return Ok(ControlFlow::Break(results));
                }

                if self.results.len() >= self.max_elements {
                    // we cannot allow this element
                    // consume the peeked closing parenthesis
                    let _ = cursor.next();
                    return Err(SmtParseError::category_error(
                        SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose]),
                    ));
                }

                // we are no longer outside
                self.outside = false;
            }
            // we are inside, parse the element using the inner parser
            match self.inner.parse(handler, parse_state, cursor)? {
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
/// The maximum can be changed by [`SmtParenMaximumParser::set_maximum`].
pub struct SmtParenMaximumParser<H: SmtHandler, P: SmtParse<H>> {
    is_opened: bool,
    inner: SmtClosedMaximumParser<H, P>,
}

impl<H: SmtHandler, P: SmtParse<H>> SmtParenMaximumParser<H, P> {
    pub fn new(inner: P, max_elements: usize) -> Self {
        Self {
            is_opened: false,
            inner: SmtClosedMaximumParser::new(inner, max_elements),
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

impl<H: SmtHandler, P: SmtParse<H>> SmtParse<H> for SmtParenMaximumParser<H, P> {
    type Result = Vec<P::Result>;

    fn parse<'a, C: SmtProduce<'a>>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<Vec<P::Result>>, SmtParseError<H::Error>> {
        loop {
            if self.is_opened {
                match self.inner.parse(handler, parse_state, cursor)? {
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
                SmtOpenParenParser::expect(token)?;
                self.is_opened = true;
            }
        }
    }
}

use std::ops::ControlFlow;

use crate::{
    SmtHandler,
    parser::{
        SmtCloseParenParser, SmtOpenParenParser, SmtParse, SmtParseError, SmtParseState,
        SmtSyntaxErrorKind, expected,
    },
    token::{SmtCursor, SmtSyntaxToken},
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
    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        // progress the first parser until it breaks or the tokens run out
        if self.first_result.is_none() {
            match self.first.parse(handler, parse_state, cursor)? {
                ControlFlow::Continue(()) => return Ok(ControlFlow::Continue(())),
                ControlFlow::Break(first) => {
                    self.first_result = Some(first);
                    // the second parser must not be handed an empty cursor
                    if cursor.is_empty() {
                        return Ok(ControlFlow::Continue(()));
                    }
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

/// The pair parsers nested to the right over the given parsers.
macro_rules! nested_pair_type {
    ($h:ident; $first:ident, $second:ident) => {
        SmtPairParser<$h, $first, $second>
    };
    ($h:ident; $first:ident, $($rest:ident),+) => {
        SmtPairParser<$h, $first, nested_pair_type!($h; $($rest),+)>
    };
}

/// The nested pair parsers over the given parser values.
macro_rules! nested_pair_new {
    ($first:ident, $second:ident) => {
        SmtPairParser::new($first, $second)
    };
    ($first:ident, $($rest:ident),+) => {
        SmtPairParser::new($first, nested_pair_new!($($rest),+))
    };
}

/// The pattern of the nested result of the nested pair parsers.
macro_rules! nested_pair_pattern {
    ($first:ident, $second:ident) => {
        ($first, $second)
    };
    ($first:ident, $($rest:ident),+) => {
        ($first, nested_pair_pattern!($($rest),+))
    };
}

/// Defines a parser of a fixed number of values in turn.
///
/// It is the pair parsers nested to the right, with the nested result
/// flattened into one tuple when the last parser breaks.
macro_rules! tuple_parser {
    ($name:ident: $($parser:ident $value:ident),+) => {
        /// Parses using each parser in turn, then returns the result tuple.
        ///
        /// Preserves self-reset: if the inner parsers are self-resetting,
        /// moves back into the default state before returning Break.
        pub struct $name<H: SmtHandler, $($parser: SmtParse<H>),+> {
            inner: nested_pair_type!(H; $($parser),+),
        }

        impl<H: SmtHandler, $($parser: SmtParse<H>),+> $name<H, $($parser),+> {
            // one argument per parser, as many as the tuple has
            #[allow(clippy::too_many_arguments)]
            pub fn new($($value: $parser),+) -> Self {
                Self {
                    inner: nested_pair_new!($($value),+),
                }
            }
        }

        impl<H: SmtHandler, $($parser: SmtParse<H> + Default),+> Default for $name<H, $($parser),+> {
            fn default() -> Self {
                Self::new($($parser::default()),+)
            }
        }

        impl<H: SmtHandler, $($parser: SmtParse<H>),+> SmtParse<H> for $name<H, $($parser),+> {
            type Result = ($($parser::Result,)+);

            #[inline]
            fn parse<Z: SmtCursor>(
                &mut self,
                handler: &mut H,
                parse_state: &mut SmtParseState<H>,
                cursor: &mut Z,
            ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
                Ok(self
                    .inner
                    .parse(handler, parse_state, cursor)?
                    .map_break(|nested_pair_pattern!($($value),+)| ($($value,)+)))
            }
        }
    };
}

tuple_parser!(SmtTuple3Parser: P1 p1, P2 p2, P3 p3);
tuple_parser!(SmtTuple4Parser: P1 p1, P2 p2, P3 p3, P4 p4);
tuple_parser!(SmtTuple5Parser: P1 p1, P2 p2, P3 p3, P4 p4, P5 p5);
tuple_parser!(SmtTuple6Parser: P1 p1, P2 p2, P3 p3, P4 p4, P5 p5, P6 p6);
tuple_parser!(SmtTuple7Parser: P1 p1, P2 p2, P3 p3, P4 p4, P5 p5, P6 p6, P7 p7);
tuple_parser!(SmtTuple8Parser: P1 p1, P2 p2, P3 p3, P4 p4, P5 p5, P6 p6, P7 p7, P8 p8);

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
            inner: SmtPairParser::new(inner, SmtCloseParenParser::new()),
        }
    }
}

impl<H: SmtHandler, P: SmtParse<H> + Default> Default for SmtClosedParser<H, P> {
    fn default() -> Self {
        Self::new(P::default())
    }
}

impl<H: SmtHandler, P: SmtParse<H>> SmtParse<H> for SmtClosedParser<H, P> {
    type Result = P::Result;

    #[inline]
    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
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
            inner: SmtPairParser::new(SmtOpenParenParser::new(), inner),
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
    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
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
    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
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

    pub(crate) fn parse<Z: SmtCursor, E>(
        &mut self,
        cursor: &mut Z,
        mut element: impl FnMut(&mut Z) -> Result<ControlFlow<T>, SmtParseError<E>>,
    ) -> Result<ControlFlow<Vec<T>>, SmtParseError<E>> {
        while let Some(token) = cursor.peek() {
            if self.outside {
                // we are outside, a closing parenthesis ends processing
                if matches!(cursor.syntax(&token), SmtSyntaxToken::ParenClose) {
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
/// The maximum can be changed by [`SmtClosedMaximumParser::set_max_elements`].
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
    pub fn set_max_elements(&mut self, max_elements: usize) {
        self.max_elements = max_elements;
    }

    pub fn max_elements(&self) -> usize {
        self.max_elements
    }

    /// The parser of each item.
    pub(crate) fn inner_mut(&mut self) -> &mut P {
        &mut self.inner
    }
}

impl<H: SmtHandler, P: SmtParse<H>> SmtParse<H> for SmtClosedMaximumParser<H, P> {
    type Result = Vec<P::Result>;

    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<Vec<P::Result>>, SmtParseError<H::Error>> {
        while let Some(peeked) = cursor.peek() {
            if self.outside {
                // we are outside, a closing parenthesis ends processing
                if matches!(cursor.syntax(&peeked), SmtSyntaxToken::ParenClose) {
                    // consume the peeked closing parenthesis
                    let _ = cursor.next();
                    let results = self.results.drain(..).collect();
                    return Ok(ControlFlow::Break(results));
                }

                if self.results.len() >= self.max_elements {
                    // we cannot allow this element
                    // consume the peeked closing parenthesis
                    let _ = cursor.next();
                    return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Expected(&[
                        expected::PAREN_CLOSE,
                    ])));
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
/// The maximum can be changed by [`SmtParenMaximumParser::set_max_elements`].
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
    pub fn set_max_elements(&mut self, max_elements: usize) {
        self.inner.set_max_elements(max_elements);
    }

    pub fn max_elements(&self) -> usize {
        self.inner.max_elements()
    }

    /// The parser of each item.
    pub(crate) fn inner_mut(&mut self) -> &mut P {
        self.inner.inner_mut()
    }
}

impl<H: SmtHandler, P: SmtParse<H>> SmtParse<H> for SmtParenMaximumParser<H, P> {
    type Result = Vec<P::Result>;

    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
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
                SmtOpenParenParser::expect(cursor, token)?;
                self.is_opened = true;
                // the inner parser must not be handed an empty cursor
                if cursor.is_empty() {
                    return Ok(ControlFlow::Continue(()));
                }
            }
        }
    }
}

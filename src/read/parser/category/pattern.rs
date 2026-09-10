use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtPattern, SmtSimplePattern, SmtSymbol,
    read::parser::{
        ParserError, ParserResources, SymbolParser,
        category::{CategoryErrorKind, CategoryParser, resources::ClosedMultipleResource},
    },
    token::{Reserved, Token, TokenKind, TokenType},
};

pub struct SimplePatternParser;

impl SimplePatternParser {
    pub fn new() -> Self {
        Self
    }

    /// Consumes exactly one token, which must be a simple pattern.
    pub(crate) fn expect<E>(token: &Token) -> Result<SmtSimplePattern, ParserError<E>> {
        let result = match token.kind() {
            TokenKind::Symbol(symbol) => SmtSimplePattern::Symbol(symbol.into_owned()),
            TokenKind::Reserved(Reserved::Underscore) => SmtSimplePattern::Wildcard,
            _ => {
                return Err(ParserError::category_error(
                    CategoryErrorKind::ExpectedToken(&[
                        TokenType::Symbol,
                        TokenType::Reserved(Reserved::Underscore),
                    ]),
                    token.span(),
                ));
            }
        };
        Ok(result)
    }
}

impl Default for SimplePatternParser {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for SimplePatternParser {
    type Result = SmtSimplePattern;

    fn progress(
        &mut self,
        _handler: &mut H,
        _resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        Ok(ControlFlow::Break(Self::expect(token)?))
    }
}

/// A parser that reads an SMT-LIB match pattern.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct PatternParser<H: SmtHandler> {
    _priv: std::marker::PhantomData<H>,
}

impl<H: SmtHandler> PatternParser<H> {
    pub fn new() -> Self {
        Self {
            _priv: std::marker::PhantomData,
        }
    }
}

impl<H: SmtHandler> Default for PatternParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for PatternParser<H> {
    type Result = SmtPattern;

    #[inline]
    fn progress(
        &mut self,
        _handler: &mut H,
        resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<ControlFlow<SmtPattern, ()>, ParserError<H::Error>> {
        // progress the slot
        resources.pattern_slot.progress(token)
    }
}

pub(crate) struct PatternSlot {
    /// Whether "(" has been read.
    ///
    /// This only matters if not storing anything yet.
    is_open: bool,
    /// The constructor, stored while its arguments are being parsed.
    constructor: Option<SmtSymbol>,
    /// The constructor arguments.
    args: ClosedMultipleResource<SmtSimplePattern>,
}

impl PatternSlot {
    pub(crate) fn new() -> Self {
        Self {
            is_open: false,
            constructor: None,
            args: ClosedMultipleResource::new(),
        }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        !self.is_open && self.constructor.is_none() && self.args.is_pristine()
    }

    pub(crate) fn clear(&mut self) {
        self.is_open = false;
        self.constructor = None;
        self.args.clear();
    }

    #[inline]
    pub(crate) fn progress<E>(
        &mut self,
        token: &Token,
    ) -> Result<ControlFlow<SmtPattern>, ParserError<E>> {
        // The sequential progress is as follows:
        // 1. Not open, expect one of:
        //    - A symbol or "_", immediately break with a simple pattern.
        //    - "(", move to (2).
        // 2. Open, expect a symbol serving as the constructor.
        //    After it is read, move to (3) by storing it.
        // 3. The constructor has been stored,
        //    parse its arguments (simple patterns) until the closing
        //    parenthesis, then break with the constructor application.
        //    The constructor application must have at least one argument.
        // The function handles this in reverse order so that nothing
        // is taken and put back unnecessarily.

        let span = token.span();

        if let Some(constructor) = self.constructor.take() {
            // step 3: parsing the arguments
            match self.args.progress(token, |token| {
                Ok(ControlFlow::Break(SimplePatternParser::expect(token)?))
            })? {
                ControlFlow::Continue(()) => self.constructor = Some(constructor),
                ControlFlow::Break(args) => {
                    // there must be at least one argument to the constructor
                    if args.is_empty() {
                        return Err(ParserError::category_error(
                            CategoryErrorKind::EmptyPatternArguments,
                            span,
                        ));
                    }
                    // the slot is back in its initial state
                    return Ok(ControlFlow::Break(SmtPattern::Application {
                        constructor,
                        args,
                    }));
                }
            }
            return Ok(ControlFlow::Continue(()));
        }

        if self.is_open {
            // step 2: expecting the constructor
            self.constructor = Some(SymbolParser::expect(token)?);
            self.is_open = false;
            return Ok(ControlFlow::Continue(()));
        }

        // step 1: expecting a simple pattern or an opening parenthesis
        debug_assert!(self.is_pristine(), "must be pristine when starting");
        let result = match token.kind() {
            TokenKind::Symbol(symbol) => SmtSimplePattern::Symbol(symbol.into_owned()),
            TokenKind::Reserved(Reserved::Underscore) => SmtSimplePattern::Wildcard,
            TokenKind::ParenOpen => {
                // move to constructor parsing
                self.is_open = true;
                return Ok(ControlFlow::Continue(()));
            }
            _ => {
                return Err(ParserError::category_error(
                    CategoryErrorKind::ExpectedToken(&[
                        TokenType::Symbol,
                        TokenType::Reserved(Reserved::Underscore),
                        TokenType::ParenOpen,
                    ]),
                    span,
                ));
            }
        };
        // this was just a simple pattern, the slot is in its initial state
        Ok(ControlFlow::Break(SmtPattern::Simple(result)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckStandardSyntax, read::parser::category::tests::parse_all_with};

    #[test]
    fn slot_is_pristine_after_every_pattern() {
        // simple patterns break immediately, constructor applications use
        // the stored constructor and the argument list; the slot must be
        // back in its initial state after each
        for input in [&b"x"[..], b"_", b"(cons x xs)", b"(node _ l r)"] {
            let mut resources = ParserResources::new();
            parse_all_with(
                PatternParser::<CheckStandardSyntax>::new(),
                &mut resources,
                input,
            );
            assert!(resources.are_pristine(), "after {input:?}");
        }
    }
}

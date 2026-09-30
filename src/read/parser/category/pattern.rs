use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtPattern, SmtSimplePattern, SmtSimplePatternView,
    read::parser::{
        Arena, CategoryErrorKind, Parser, ParserError, ParserResources, PatternHandle,
        SimplePatternHandle, TextHandle,
    },
    token::{GeneralReserved, Reserved, Token, TokenKind, TokenType},
};

pub struct SimplePatternParser;

impl SimplePatternParser {
    pub fn new() -> Self {
        Self
    }

    /// Consumes exactly one token, which must be a simple pattern.
    pub(crate) fn expect<H: SmtHandler + ?Sized>(
        arena: &Arena<H>,
        token: Token,
    ) -> Result<SmtSimplePattern, ParserError<H::Error>> {
        Ok(Self::expect_view(arena, token)?.into_owned())
    }

    /// Consumes exactly one token, which must be a simple pattern, viewing it.
    pub(crate) fn expect_view<'t, H: SmtHandler + ?Sized>(
        arena: &Arena<H>,
        token: Token<'t>,
    ) -> Result<SmtSimplePatternView<'t>, ParserError<H::Error>> {
        let result = match arena.token_kind(token) {
            TokenKind::Symbol(symbol) => SmtSimplePatternView::Symbol(symbol),
            TokenKind::Reserved(Reserved::General(GeneralReserved::Underscore)) => {
                SmtSimplePatternView::Wildcard
            }
            _ => {
                return Err(ParserError::category_error(
                    CategoryErrorKind::ExpectedSymbolOrUnderscore,
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

impl<H: SmtHandler> Parser<H> for SimplePatternParser {
    type Result = SmtSimplePattern;

    fn progress(
        &mut self,
        _handler: &mut H,
        resources: &mut ParserResources<H>,
        token: Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        Ok(ControlFlow::Break(Self::expect(&resources.store, token)?))
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

impl<H: SmtHandler> Parser<H> for PatternParser<H> {
    type Result = SmtPattern;

    #[inline]
    fn progress(
        &mut self,
        _handler: &mut H,
        resources: &mut ParserResources<H>,
        token: Token,
    ) -> Result<ControlFlow<SmtPattern, ()>, ParserError<H::Error>> {
        // progress the slot
        let ParserResources {
            pattern_slot,
            store,
            ..
        } = resources;
        match pattern_slot.progress(store, token)? {
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(pattern) => {
                // break with the owned pattern
                Ok(ControlFlow::Break(
                    store.hand_over_pattern(pattern, |pattern| pattern.into_owned()),
                ))
            }
        }
    }
}

pub(crate) struct PatternSlot {
    /// Whether "(" has been read.
    ///
    /// This only matters if not storing anything yet.
    is_open: bool,
    /// The constructor, stored in the arena text while its arguments are being parsed.
    constructor: Option<TextHandle>,
    /// The constructor arguments are stored in the arena starting at this position.
    arena_args_start: usize,
}

impl PatternSlot {
    pub(crate) fn new() -> Self {
        Self {
            is_open: false,
            constructor: None,
            arena_args_start: 0,
        }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        !self.is_open && self.constructor.is_none()
    }

    pub(crate) fn clear(&mut self) {
        self.is_open = false;
        self.constructor = None;
    }

    #[inline]
    pub(crate) fn progress<'t, H: SmtHandler + ?Sized>(
        &mut self,
        arena: &mut Arena<H>,
        token: Token<'t>,
    ) -> Result<ControlFlow<PatternHandle<'t>>, ParserError<H::Error>> {
        // The sequential progress is as follows:
        // 1. Not open, expect one of:
        //    - A symbol or "_", immediately break with a simple pattern.
        //    - "(", move to (2).
        // 2. Open, expect a symbol serving as the constructor.
        //    After it is read, move to (3) by storing it in the arena.
        // 3. The constructor has been stored,
        //    parse its arguments (simple patterns) into the arena until the
        //    closing parenthesis, then break with the constructor application.
        //    The constructor application must have at least one argument.
        // The function handles this in reverse order so that nothing
        // is taken and put back unnecessarily.

        let span = token.span();

        if let Some(constructor) = self.constructor.take() {
            // step 3: parsing the arguments
            if matches!(token.ty(), TokenType::ParenClose) {
                // there must be at least one argument to the constructor
                if arena.simple_patterns.len() == self.arena_args_start {
                    return Err(ParserError::category_error(
                        CategoryErrorKind::EmptyPatternArguments,
                        span,
                    ));
                }
                // the slot is back in its initial state, the pattern is in the arena
                return Ok(ControlFlow::Break(PatternHandle::Application {
                    constructor,
                    args_start: self.arena_args_start,
                }));
            }
            // an argument is starting here, it will be stored in the arena
            let argument = match SimplePatternParser::expect_view(arena, token)? {
                SmtSimplePatternView::Symbol(symbol) => {
                    SimplePatternHandle::Symbol(arena.push_text(symbol.as_slice()))
                }
                SmtSimplePatternView::Wildcard => SimplePatternHandle::Wildcard,
            };
            arena.simple_patterns.push(argument);
            self.constructor = Some(constructor);
            return Ok(ControlFlow::Continue(()));
        }

        if self.is_open {
            // step 2: expecting the constructor, which goes to the arena text
            let TokenKind::Symbol(constructor) = arena.token_kind(token) else {
                return Err(ParserError::category_error(
                    CategoryErrorKind::ExpectedSymbol,
                    span,
                ));
            };
            // push the constructor to the arena text and start parsing arguments
            self.constructor = Some(arena.push_text(constructor.as_slice()));
            self.arena_args_start = arena.simple_patterns.len();
            self.is_open = false;
            return Ok(ControlFlow::Continue(()));
        }

        // step 1: expecting a simple pattern or an opening parenthesis
        debug_assert!(self.is_pristine(), "must be pristine when starting");
        let result = match arena.token_kind(token) {
            TokenKind::Symbol(symbol) => SmtSimplePatternView::Symbol(symbol),
            TokenKind::Reserved(Reserved::General(GeneralReserved::Underscore)) => {
                SmtSimplePatternView::Wildcard
            }
            TokenKind::ParenOpen => {
                // move to constructor parsing
                self.is_open = true;
                return Ok(ControlFlow::Continue(()));
            }
            _ => {
                return Err(ParserError::category_error(
                    CategoryErrorKind::ExpectedSymbolUnderscoreOrParenOpen,
                    span,
                ));
            }
        };
        // this was just a simple pattern, the slot is in its initial state
        Ok(ControlFlow::Break(PatternHandle::Simple(result)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckStandardSyntax, read::parser::category::tests::parse_all_with};

    #[test]
    fn slot_is_pristine_after_every_pattern() {
        // simple patterns break immediately, constructor applications use
        // the stored constructor and the arguments in the arena; the slot and
        // the arena must be back in their initial state after each
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

use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtPatternBuf, SmtSimplePattern, SmtSimplePatternBuf,
    parser::{
        Arena, PatternHandle, SimplePatternHandle, SmtParse, SmtParseError, SmtParseState,
        SmtSyntaxErrorKind, SymbolHandle, parse_by_token,
    },
    token::{SmtGeneralReserved, SmtProduce, SmtReserved, SmtSyntaxToken, SmtVersion},
};

pub struct SmtSimplePatternParser;

impl SmtSimplePatternParser {
    pub fn new() -> Self {
        Self
    }

    /// Consumes exactly one token, which must be a simple pattern.
    pub(crate) fn expect<H: SmtHandler + ?Sized, Z: SmtProduce>(
        cursor: &Z,
        token: Z::Token,
    ) -> Result<SmtSimplePatternBuf, SmtParseError<H::Error>> {
        Ok(Self::expect_view::<H, Z>(cursor, &token)?.into_owned())
    }

    /// Consumes exactly one token, which must be a simple pattern, viewing it.
    pub(crate) fn expect_view<'t, H: SmtHandler + ?Sized, Z: SmtProduce>(
        cursor: &Z,
        token: &'t Z::Token,
    ) -> Result<SmtSimplePattern<'t>, SmtParseError<H::Error>> {
        let result = match cursor.syntax(token) {
            SmtSyntaxToken::Symbol(symbol) => Some(SmtSimplePattern::Symbol(symbol)),
            SmtSyntaxToken::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore)) => {
                // the underscore wildcard is not allowed in every version
                if underscore_wildcard_allowed(cursor.version()) {
                    Some(SmtSimplePattern::Wildcard)
                } else {
                    None
                }
            }
            _ => None,
        };
        match result {
            Some(view) => Ok(view),
            None => {
                // the underscore wildcard is not allowed in every version
                let kind = if underscore_wildcard_allowed(cursor.version()) {
                    SmtSyntaxErrorKind::ExpectedSymbolOrUnderscore
                } else {
                    SmtSyntaxErrorKind::ExpectedSymbol
                };

                Err(SmtParseError::category_error(kind))
            }
        }
    }
}

impl Default for SmtSimplePatternParser {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> SmtParse<H> for SmtSimplePatternParser {
    type Result = SmtSimplePatternBuf;

    fn parse<Z: SmtProduce>(
        &mut self,
        _handler: &mut H,
        _parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        let Some(token) = cursor.next() else {
            return Ok(ControlFlow::Continue(()));
        };
        Ok(ControlFlow::Break(Self::expect::<H, Z>(cursor, token)?))
    }
}

/// A parser that reads an SMT-LIB match pattern.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct SmtPatternParser<H: SmtHandler> {
    _priv: std::marker::PhantomData<H>,
}

impl<H: SmtHandler> SmtPatternParser<H> {
    pub fn new() -> Self {
        Self {
            _priv: std::marker::PhantomData,
        }
    }
}

impl<H: SmtHandler> Default for SmtPatternParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> SmtParse<H> for SmtPatternParser<H> {
    type Result = SmtPatternBuf;

    #[inline]
    fn parse<C: SmtProduce>(
        &mut self,
        _handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<SmtPatternBuf, ()>, SmtParseError<H::Error>> {
        // progress the slot
        let SmtParseState {
            pattern_slot,
            arena,
            ..
        } = parse_state;
        parse_by_token(cursor, |cursor, token| {
            match pattern_slot.progress(arena, cursor, &token)? {
                ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
                ControlFlow::Break(pattern) => {
                    // break with the owned pattern
                    Ok(ControlFlow::Break(
                        arena.hand_over_pattern(pattern, |pattern| pattern.into_owned()),
                    ))
                }
            }
        })
    }
}

pub(crate) struct PatternSlot {
    /// Whether "(" has been read.
    ///
    /// This only matters if not storing anything yet.
    is_open: bool,
    /// The constructor, stored in the arena text while its arguments are being parsed.
    constructor: Option<SymbolHandle>,
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
    pub(crate) fn progress<'t, H: SmtHandler + ?Sized, Z: SmtProduce>(
        &mut self,
        arena: &mut Arena<H>,
        cursor: &Z,
        token: &'t Z::Token,
    ) -> Result<ControlFlow<PatternHandle<'t>>, SmtParseError<H::Error>> {
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

        if let Some(constructor) = self.constructor.take() {
            // step 3: parsing the arguments
            if matches!(cursor.syntax(token), SmtSyntaxToken::ParenClose) {
                // there must be at least one argument to the constructor
                let args_end = arena.simple_patterns.len();
                if args_end == self.arena_args_start {
                    return Err(SmtParseError::category_error(
                        SmtSyntaxErrorKind::EmptyPatternArguments,
                    ));
                }
                // the slot is back in its initial state, the pattern is in the arena
                return Ok(ControlFlow::Break(PatternHandle::Application {
                    constructor,
                    args_start: self.arena_args_start,
                    args_end,
                }));
            }
            // an argument is starting here, it will be stored in the arena
            let argument = match SmtSimplePatternParser::expect_view::<H, Z>(cursor, token)? {
                SmtSimplePattern::Symbol(symbol) => {
                    SimplePatternHandle::Symbol(arena.push_symbol(symbol))
                }
                SmtSimplePattern::Wildcard => SimplePatternHandle::Wildcard,
            };
            arena.simple_patterns.push(argument);
            self.constructor = Some(constructor);
            return Ok(ControlFlow::Continue(()));
        }

        if self.is_open {
            // step 2: expecting the constructor, which goes to the arena text
            let SmtSyntaxToken::Symbol(constructor) = cursor.syntax(token) else {
                return Err(SmtParseError::category_error(
                    SmtSyntaxErrorKind::ExpectedSymbol,
                ));
            };
            // push the constructor to the arena text and start parsing arguments
            self.constructor = Some(arena.push_symbol(constructor));
            self.arena_args_start = arena.simple_patterns.len();
            self.is_open = false;
            return Ok(ControlFlow::Continue(()));
        }

        // step 1: expecting a simple pattern or an opening parenthesis
        debug_assert!(self.is_pristine(), "must be pristine when starting");
        let result = match cursor.syntax(token) {
            SmtSyntaxToken::Symbol(symbol) => Some(SmtSimplePattern::Symbol(symbol)),
            SmtSyntaxToken::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore)) => {
                // the underscore wildcard is not allowed in every version
                if underscore_wildcard_allowed(cursor.version()) {
                    Some(SmtSimplePattern::Wildcard)
                } else {
                    None
                }
            }
            SmtSyntaxToken::ParenOpen => {
                // move to constructor parsing
                self.is_open = true;
                return Ok(ControlFlow::Continue(()));
            }
            _ => None,
        };
        match result {
            Some(view) => {
                // this was just a simple pattern, the slot is in its initial state
                Ok(ControlFlow::Break(PatternHandle::Simple(view)))
            }
            None => {
                // the underscore wildcard is not allowed in every version
                let kind = if underscore_wildcard_allowed(cursor.version()) {
                    SmtSyntaxErrorKind::ExpectedSymbolUnderscoreOrParenOpen
                } else {
                    SmtSyntaxErrorKind::ExpectedSymbolOrParenOpen
                };
                Err(SmtParseError::category_error(kind))
            }
        }
    }
}

fn underscore_wildcard_allowed(version: SmtVersion) -> bool {
    // the underscore names a wildcard since SMT-LIB 2.7
    version >= SmtVersion::V2_7
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{SmtSyntaxChecker, parser::category::tests::parse_all_with};

    #[test]
    fn slot_is_pristine_after_every_pattern() {
        // simple patterns break immediately, constructor applications use
        // the stored constructor and the arguments in the arena; the slot and
        // the arena must be back in their initial state after each
        for input in [&b"x"[..], b"_", b"(cons x xs)", b"(node _ l r)"] {
            let mut parse_state = SmtParseState::new();
            parse_all_with(
                SmtPatternParser::<SmtSyntaxChecker>::new(),
                &mut parse_state,
                input,
            );
            assert!(parse_state.is_pristine(), "after {input:?}");
        }
    }
}

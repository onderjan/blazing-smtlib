use std::{fmt, ops::ControlFlow};

use crate::{
    SmtHandler, SmtVersion,
    grammar::SmtSExpr,
    parser::{
        Arena, SmtParse, SmtParseError, SmtParseState, SmtSyntaxErrorKind, SmtSyntaxExpected,
        category::parse_special_constant, handle_err, parse_by_token,
    },
    token::{SmtCursor, SmtToken},
};

/// Parses an S-expression.
pub struct SmtSExprParser<H: SmtHandler> {
    _priv: std::marker::PhantomData<H>,
}

impl<H: SmtHandler> fmt::Debug for SmtSExprParser<H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SmtSExprParser").finish_non_exhaustive()
    }
}

impl<H: SmtHandler> SmtSExprParser<H> {
    /// Creates the parser.
    pub fn new() -> Self {
        Self {
            _priv: std::marker::PhantomData,
        }
    }
}

impl<H: SmtHandler> Default for SmtSExprParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> SmtParse<H> for SmtSExprParser<H> {
    type Result = H::SExpr;

    #[inline]
    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<H::SExpr>, SmtParseError<H::Error>> {
        // progress the slot over the arena
        let SmtParseState {
            s_expr_slot, arena, ..
        } = parse_state;
        parse_by_token(cursor, |cursor, token| {
            s_expr_slot.progress(handler, arena, cursor, token)
        })
    }
}

/// An S-expression list waiting for additional inner S-expressions.
struct Level {
    /// The inner S-expressions are stored in the arena starting at this position.
    arena_s_exprs_start: usize,
}

pub(crate) struct SExprSlot {
    levels: Vec<Level>,
}

impl SExprSlot {
    pub(crate) fn new() -> Self {
        Self { levels: Vec::new() }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        self.levels.is_empty()
    }

    pub(crate) fn clear(&mut self) {
        self.levels.clear();
    }

    #[inline]
    pub(crate) fn progress<H: SmtHandler + ?Sized, Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        arena: &mut Arena<H>,
        cursor: &Z,
        token: Z::Token,
    ) -> Result<ControlFlow<H::SExpr>, SmtParseError<H::Error>> {
        // there is no state besides the levels, so an empty level stack
        // means the category is being entered
        if self.levels.is_empty() {
            debug_assert!(self.is_pristine(), "must be pristine when starting");
        }

        let s_expr = match cursor.syntax(&token) {
            SmtToken::Symbol(symbol) => SmtSExpr::Symbol(symbol),
            SmtToken::Reserved(reserved) => {
                // reserved words are only allowed in S-expressions since SMT-LIB 2.6
                if cursor.version() >= SmtVersion::V2_6 {
                    SmtSExpr::Reserved(reserved)
                } else {
                    return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Expected(&[
                        SmtSyntaxExpected::SExpr,
                    ])));
                }
            }
            SmtToken::Keyword(keyword) => SmtSExpr::Keyword(keyword),
            SmtToken::ParenOpen => {
                // add a new level, remember where its S-expressions will start in the arena
                self.levels.push(Level {
                    arena_s_exprs_start: arena.s_exprs.len(),
                });
                return Ok(ControlFlow::Continue(()));
            }
            SmtToken::ParenClose => {
                // try to pop the last level
                let Some(last_level) = self.levels.pop() else {
                    // no last level, all that we received was ")"
                    return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Expected(&[
                        SmtSyntaxExpected::SExpr,
                    ])));
                };
                // the last level exists, we can close it, handing its S-expressions over
                // (an empty list is allowed)
                let s_expr = arena
                    .hand_over_s_exprs(last_level.arena_s_exprs_start, |s_exprs| {
                        handle_err(handler.handle_s_expr(SmtSExpr::SExprs(s_exprs)))
                    })?;
                return Ok(self.finish(arena, s_expr));
            }
            kind => {
                if let Ok(special_constant) = parse_special_constant(kind) {
                    SmtSExpr::SpecialConstant(special_constant)
                } else {
                    return Err(SmtParseError::syntax(SmtSyntaxErrorKind::Expected(&[
                        SmtSyntaxExpected::SExpr,
                    ])));
                }
            }
        };

        // an atom, handed over straight from the token
        let s_expr = handle_err(handler.handle_s_expr(s_expr))?;
        Ok(self.finish(arena, s_expr))
    }

    #[inline]
    fn finish<H: SmtHandler + ?Sized>(
        &mut self,
        arena: &mut Arena<H>,
        s_expr: H::SExpr,
    ) -> ControlFlow<H::SExpr> {
        if self.levels.is_empty() {
            // this is the root level, we are done
            ControlFlow::Break(s_expr)
        } else {
            // we need to append to the last level
            arena.s_exprs.push(s_expr);
            ControlFlow::Continue(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{SmtSyntaxChecker, parser::category::tests::parse_all_with};

    #[test]
    fn slot_is_pristine_after_every_s_expr() {
        // atoms, empty lists, and nested lists all use the level stack of the
        // slot and the arena, which must be empty again afterwards
        for input in [&b"x"[..], b"()", b"(a (b c) :kw 1)", b"((()))"] {
            let mut parse_state = SmtParseState::new();
            parse_all_with(
                SmtSExprParser::<SmtSyntaxChecker>::new(),
                &mut parse_state,
                input,
            );
            assert!(parse_state.is_pristine(), "after {input:?}");
        }
    }
}

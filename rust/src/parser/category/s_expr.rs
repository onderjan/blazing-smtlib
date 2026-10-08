use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSExpr,
    parser::{
        Arena, SmtParse, SmtParseError, SmtParseState, SmtSyntaxErrorKind,
        category::parse_special_constant, handle_err, parse_by_token,
    },
    token::{SmtBatchCursor, SmtSyntaxToken, SmtToken, SmtVersion},
};

/// A parser that reads an SMT-LIB S-expression.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct SmtSExprParser<H: SmtHandler> {
    _priv: std::marker::PhantomData<H>,
}

impl<H: SmtHandler> SmtSExprParser<H> {
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
    fn parse(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<H::SExpr>, SmtParseError<H::Error>> {
        // progress the slot over the arena
        let SmtParseState {
            s_expr_slot, arena, ..
        } = parse_state;
        parse_by_token(cursor, |version, token| {
            s_expr_slot.progress(handler, arena, version, token)
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
    pub(crate) fn progress<H: SmtHandler + ?Sized>(
        &mut self,
        handler: &mut H,
        arena: &mut Arena<H>,
        version: SmtVersion,
        token: SmtToken,
    ) -> Result<ControlFlow<H::SExpr>, SmtParseError<H::Error>> {
        // there is no state besides the levels, so an empty level stack
        // means the category is being entered
        if self.levels.is_empty() {
            debug_assert!(self.is_pristine(), "must be pristine when starting");
        }

        let s_expr = match token.syntax(version) {
            SmtSyntaxToken::Symbol(symbol) => SmtSExpr::Symbol(symbol),
            SmtSyntaxToken::Reserved(reserved) => {
                // reserved words are only allowed in S-expressions since SMT-LIB 2.6
                if version >= SmtVersion::V2_6 {
                    SmtSExpr::Reserved(reserved)
                } else {
                    return Err(SmtParseError::category_error(
                        SmtSyntaxErrorKind::ExpectedSExpr,
                    ));
                }
            }
            SmtSyntaxToken::Keyword(keyword) => SmtSExpr::Keyword(keyword),
            SmtSyntaxToken::ParenOpen => {
                // add a new level, remember where its S-expressions will start in the arena
                self.levels.push(Level {
                    arena_s_exprs_start: arena.s_exprs.len(),
                });
                return Ok(ControlFlow::Continue(()));
            }
            SmtSyntaxToken::ParenClose => {
                // try to pop the last level
                let Some(last_level) = self.levels.pop() else {
                    // no last level, all that we received was ")"
                    return Err(SmtParseError::category_error(
                        SmtSyntaxErrorKind::ExpectedSExpr,
                    ));
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
                    return Err(SmtParseError::category_error(
                        SmtSyntaxErrorKind::ExpectedSExpr,
                    ));
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

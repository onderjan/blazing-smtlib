use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSExpr,
    read::parser::{
        ParserError, ParserResources,
        category::{CategoryErrorKind, CategoryParser, parse_special_constant},
        handle_err,
    },
    token::{Token, TokenKind},
};

/// A parser that reads an SMT-LIB S-expression.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct SExprParser<H: SmtHandler> {
    levels: Vec<Level<H>>,
}

/// An S-expression waiting for additional inner S-expressions.
struct Level<H: SmtHandler> {
    s_exprs: Vec<H::SExpr>,
}

impl<H: SmtHandler> SExprParser<H> {
    pub fn new() -> Self {
        Self { levels: Vec::new() }
    }
}

impl<H: SmtHandler> Default for SExprParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for SExprParser<H> {
    type Result = H::SExpr;

    fn restart(&mut self) {
        self.levels.clear();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources,
        token: &Token,
    ) -> Result<ControlFlow<H::SExpr>, ParserError<H::Error>> {
        let s_expr = match token.kind() {
            TokenKind::Symbol(symbol) => SmtSExpr::Symbol(symbol.into_owned()),
            TokenKind::Reserved(reserved) => SmtSExpr::Reserved(reserved),
            TokenKind::Keyword(keyword) => SmtSExpr::Keyword(keyword.into_owned()),
            TokenKind::ParenOpen => {
                // add a new level
                self.levels.push(Level {
                    s_exprs: Vec::new(),
                });
                return Ok(ControlFlow::Continue(()));
            }
            TokenKind::ParenClose => {
                // try to pop the last level
                if let Some(last_level) = self.levels.pop() {
                    // the last level exists, we can close it
                    // empty s_expr is allowed
                    SmtSExpr::SExprs(last_level.s_exprs)
                } else {
                    // no last level, all that we received was ")"
                    return Err(ParserError::category_error(
                        CategoryErrorKind::ExpectedSExpr,
                        token.span(),
                    ));
                }
            }
            kind => {
                if let Ok(special_constant) = parse_special_constant(kind) {
                    SmtSExpr::SpecialConstant(special_constant)
                } else {
                    return Err(ParserError::category_error(
                        CategoryErrorKind::ExpectedSExpr,
                        token.span(),
                    ));
                }
            }
        };

        let s_expr = handle_err(handler.handle_s_expr(s_expr), token.span())?;

        if let Some(last_level) = self.levels.last_mut() {
            // we need to append to the last level
            last_level.s_exprs.push(s_expr);
            Ok(ControlFlow::Continue(()))
        } else {
            // this is the root level, we are done
            Ok(ControlFlow::Break(s_expr))
        }
    }
}

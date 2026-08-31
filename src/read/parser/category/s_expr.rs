use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtSExpr, SmtSpan,
    parser::category::{CategoryParserErrorKind, handle_err, parse_special_constant},
    read::parser::{ParserError, category::CategoryParser},
    token::{Token, TokenKind},
};

pub struct SExprLevel<H: SmtHandler> {
    s_exprs: Vec<H::SExpr>,
}

pub struct SExprParser<H: SmtHandler> {
    levels: Vec<SExprLevel<H>>,
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

    fn init() -> Self {
        Self::new()
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::SExpr, Self>, ParserError<H>> {
        let (mut levels, s_expr) = match self.progress_last_level(handler, token)? {
            ControlFlow::Continue(parser) => return Ok(ControlFlow::Continue(parser)),
            ControlFlow::Break((levels, term)) => (levels, term),
        };
        if let Some(last_level) = levels.last_mut() {
            // we need to progress the last level
            last_level.s_exprs.push(s_expr);
            Ok(ControlFlow::Continue(Self { levels }))
        } else {
            // this is the root term level, we are done
            Ok(ControlFlow::Break(s_expr))
        }
    }
}

type SExprProgressOk<H, P> = ControlFlow<(Vec<SExprLevel<H>>, <H as SmtHandler>::SExpr), P>;

impl<H: SmtHandler> SExprParser<H> {
    fn progress_last_level(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<SExprProgressOk<H, Self>, ParserError<H>> {
        let span = token.span();
        let mut levels = self.levels;

        let token = match parse_special_constant(token) {
            Ok(special_constant) => {
                let s_expr = SmtSExpr::SpecialConstant(special_constant);
                return Self::break_with(handler, levels, s_expr, span);
            }
            Err(token) => token,
        };

        match token.into_kind() {
            TokenKind::Symbol(symbol) => {
                let s_expr = SmtSExpr::Symbol(symbol);
                Self::break_with(handler, levels, s_expr, span)
            }
            TokenKind::Reserved(reserved) => {
                let s_expr = SmtSExpr::Reserved(reserved);
                Self::break_with(handler, levels, s_expr, span)
            }
            TokenKind::Keyword(keyword) => {
                let s_expr = SmtSExpr::Keyword(keyword);
                Self::break_with(handler, levels, s_expr, span)
            }
            TokenKind::ParenOpen => {
                // add new level
                levels.push(SExprLevel {
                    s_exprs: Vec::new(),
                });
                Ok(ControlFlow::Continue(Self { levels }))
            }
            kind => {
                if matches!(kind, TokenKind::ParenClose) {
                    // closes the last level if it exists
                    if let Some(last_level) = levels.pop() {
                        // empty s_expr is allowed
                        let s_expr = SmtSExpr::SExprs(last_level.s_exprs);
                        return Self::break_with(handler, levels, s_expr, span);
                    }
                }

                let kind = CategoryParserErrorKind::ExpectedSExpr;
                Err(ParserError::category_error(kind, span))
            }
        }
    }

    fn break_with(
        handler: &mut H,
        levels: Vec<SExprLevel<H>>,
        s_expr: SmtSExpr<H>,
        span: SmtSpan,
    ) -> Result<SExprProgressOk<H, Self>, ParserError<H>> {
        let s_expr = handle_err(handler.handle_s_expr(s_expr), span)?;
        Ok(ControlFlow::Break((levels, s_expr)))
    }
}

mod adapter;
mod category;
mod command;
mod script;

use std::ops::ControlFlow;

pub use adapter::*;
pub use category::*;
pub use command::*;
pub use script::*;

use crate::{
    SmtHandler, SmtSpan,
    token::{Token, TokenCursor, TokenType},
};

pub trait Parser<H: SmtHandler + ?Sized> {
    type Result;

    /// Parses tokens from the cursor, progressing the parser.
    ///
    /// Tokens are consumed until the parser is finished, returning
    /// [`ControlFlow::Break`] with the result and leaving the cursor after the
    /// last consumed token, or until the cursor is empty, returning
    /// [`ControlFlow::Continue`]. After an error, the cursor position is not
    /// specified.
    ///
    /// All standard parsers implementing [`Parser`] are self-resetting:
    /// after returning [`ControlFlow::Break`], they are back in their initial state.
    ///
    /// The `resources` are shared resources of standard category parsers.
    /// To keep resources valid, each [`Parser`] must be progressed
    /// until completion once started, i.e. if [`Parser::parse()`]
    /// returns `Ok(Continue(()))`, the subsequent outer parse call
    /// must call [`Parser::parse()`] on the same parser, and
    /// is forbidden from progressing any other parsers.
    /// Failure to heed this contract may lead to silently wrong parsing
    /// or panics, but never unsafe behaviour.
    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut TokenCursor,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>>;
}

/// Parses the cursor one token at a time with `progress`, until the cursor
/// is empty or `progress` breaks.
///
/// For parsers whose state machine steps by single tokens.
#[inline]
pub(crate) fn parse_by_token<R, E>(
    cursor: &mut TokenCursor,
    mut progress: impl FnMut(Token) -> Result<ControlFlow<R>, E>,
) -> Result<ControlFlow<R>, E> {
    while let Some(token) = cursor.next() {
        if let ControlFlow::Break(result) = progress(token)? {
            return Ok(ControlFlow::Break(result));
        }
    }
    Ok(ControlFlow::Continue(()))
}

/// Error emitted by a parser, including the error span.
#[derive(Debug)]
pub struct ParserError<E>(Box<ParserErrorInner<E>>);

#[derive(Debug)]
pub enum ParserErrorKind<E> {
    Syntax(SyntaxErrorKind),
    Handler(E),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SyntaxErrorKind {
    ExpectedToken(&'static [TokenType]),
    ExpectedSymbol,
    ExpectedUnderscore,
    ExpectedSymbolOrUnderscore,
    ExpectedSymbolUnderscoreOrParenOpen,
    ExpectedUnderscoreOrAs,

    EmptyIdentIndices,
    EmptySortApplication,
    EmptyTermApplication,
    EmptyLetBindings,
    EmptyAnnotation,
    EmptyQuantifierBindings,
    EmptyLambdaBindings,
    ExpectedIndexOrCloseParen,
    ExpectedOperator,
    ExpectedSExpr,
    ExpectedIdent,
    ExpectedSort,
    ExpectedSortInner,
    ExpectedTerm,
    ExpectedAttribute,
    ExpectedCommand,
    ExpectedCommandName,
    ExpectedDatatype,
    ExpectedDatatypeKind,
    ExpectedFunctionBody,
    EmptyFunctionSignatures,
    EmptyDatatypeIntroductions,
    EmptyDatatypeParameters,
    EmptyDatatypeConstructors,
    EmptyPatternArguments,
    EmptyMatchCases,
    EmptyGetValueTerms,
}

impl<E> ParserError<E> {
    #[cold]
    #[inline(never)]
    pub(crate) fn new(kind: ParserErrorKind<E>, span: SmtSpan) -> Self {
        // PERFORMANCE: error kind and span are boxed
        // so that parser results are not unnecessarily large
        // this method boxes them, which forces an allocation
        // so it is is marked cold and never-inline
        Self(Box::new(ParserErrorInner { kind, span }))
    }

    pub(crate) fn handler_error(err: E, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::Handler(err), span)
    }

    pub(crate) fn category_error(err: SyntaxErrorKind, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::Syntax(err), span)
    }

    pub fn kind(&self) -> &ParserErrorKind<E> {
        &self.0.kind
    }

    pub fn span(&self) -> SmtSpan {
        self.0.span
    }

    pub fn into_kind(self) -> ParserErrorKind<E> {
        self.0.kind
    }
}

#[derive(Debug)]
struct ParserErrorInner<E> {
    kind: ParserErrorKind<E>,
    span: SmtSpan,
}

fn handle_err<O, E>(handled: Result<O, E>, span: SmtSpan) -> Result<O, ParserError<E>> {
    match handled {
        Ok(ok) => Ok(ok),
        Err(err) => Err(ParserError::handler_error(err, span)),
    }
}

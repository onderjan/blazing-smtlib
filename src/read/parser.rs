mod category;
mod command;
mod script;

use std::ops::ControlFlow;

pub use category::*;
pub use command::*;
pub use script::*;

use crate::{
    SmtHandler, SmtSpan,
    token::{Token, TokenCursor, TokenType},
};

pub trait Parser<H: SmtHandler + ?Sized> {
    type Result;

    /// Parses a single token, progressing the parser.
    ///
    /// If a non-error result is returned, it either signals that the
    /// parser is finished ([`ControlFlow::Break`] with the result value),
    /// or that it is not finished yet ([`ControlFlow::Continue`]).
    ///
    /// All standard parsers implementing [`CategoryParser`] are self-resetting:
    /// after returning [`ControlFlow::Break`], they are back in their initial state.
    ///
    /// The `resources` are shared resources of standard category parsers.
    /// To keep resources valid, each [`CategoryParser`] must progress
    /// until completion once started, i.e. if [`CategoryParser::progress()`]
    /// returns `Ok(Continue(()))`, the subsequent outer progress call
    /// must call [`CategoryParser::progress()`] on the same parser, and
    /// is forbidden from progressing any other parsers.
    /// Failure to heed this contract may lead to silently wrong parsing
    /// or panics, but never unsafe behaviour.
    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>>;

    /// Parses all tokens from the cursor, progressing the parser.
    ///
    /// Tokens are consumed until the parser is finished, returning
    /// [`ControlFlow::Break`] with the result and leaving the cursor after the
    /// last consumed token, or until the cursor is empty, returning
    /// [`ControlFlow::Continue`]. After an error, the cursor position is not
    /// specified.
    ///
    /// The contract of [`CategoryParser::progress()`] applies: once started,
    /// the parser must be progressed until completion.
    ///
    /// The default implementation loops over [`CategoryParser::progress()`].
    /// If better performance is needed, implement this function and call it
    /// from [`CategoryParser::progress()`] with a cursor over the single token.
    #[inline]
    fn progress_all(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut TokenCursor,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        while let Some(token) = cursor.take() {
            if let ControlFlow::Break(result) = self.progress(handler, resources, token)? {
                return Ok(ControlFlow::Break(result));
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Error emitted by a parser, including the error span.
#[derive(Debug)]
pub struct ParserError<E>(Box<ParserErrorInner<E>>);

#[derive(Debug)]
pub enum ParserErrorKind<E> {
    Category(CategoryErrorKind),
    Handler(E),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CategoryErrorKind {
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

    pub(crate) fn category_error(err: CategoryErrorKind, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::Category(err), span)
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

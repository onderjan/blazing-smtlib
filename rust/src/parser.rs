mod adapter;
mod category;
mod command;
mod script;
mod state;

use std::ops::ControlFlow;

pub use adapter::*;
pub use category::*;
pub use command::*;
pub use script::*;
pub use state::*;

use crate::{
    SmtHandler,
    token::{SmtProduce, SmtTokenCategory},
};

pub trait SmtParse<H: SmtHandler + ?Sized> {
    type Result;

    /// Parses tokens from the cursor, progressing the parser.
    ///
    /// If the parser returns [`ControlFlow::Continue`], it means all tokens
    /// were handled and more are wanted: the cursor must be empty.
    ///
    /// If the parser returns [`ControlFlow::Break`], it means
    /// it finished the input it accepts (consuming exactly its tokens),
    /// is returning a result and waiting for processing of the next value.
    ///
    /// Returning an error means the handler failed at the token after
    /// the consumed ones. The state of the parser, cursor, and resources
    /// is unspecified.
    ///
    /// All library parsers implementing [`SmtParse`] are fully self-resetting:
    /// after returning [`ControlFlow::Break`], they are back in their initial state.
    ///
    /// The `parse_state` holds the shared resources of standard category parsers.
    /// To keep resources valid, each [`SmtParse`] must be progressed
    /// until completion once started, i.e. if [`SmtParse::parse()`]
    /// returns `Ok(Continue(()))`, the subsequent outer parse call
    /// must call [`SmtParse::parse()`] on the same parser, and
    /// is forbidden from progressing any other parsers.
    /// Failure to heed this contract may lead to silently wrong parsing
    /// or panics, but never unsafe behaviour.
    fn parse<C: SmtProduce>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>>;
}

/// Parses the cursor one token at a time with `progress`, until the cursor
/// is empty or `progress` breaks.
///
/// For parsers whose state machine steps by single tokens.
#[inline]
pub(crate) fn parse_by_token<C: SmtProduce, R, E>(
    cursor: &mut C,
    mut progress: impl FnMut(&C, C::Token) -> Result<ControlFlow<R>, E>,
) -> Result<ControlFlow<R>, E> {
    while let Some(token) = cursor.next() {
        if let ControlFlow::Break(result) = progress(cursor, token)? {
            return Ok(ControlFlow::Break(result));
        }
    }
    Ok(ControlFlow::Continue(()))
}

/// Error emitted by a parser.
#[derive(Debug)]
pub struct SmtParseError<E>(Box<SmtParseErrorCause<E>>);

#[derive(Debug)]
pub enum SmtParseErrorCause<E> {
    Syntax(SmtSyntaxErrorKind),
    Handler(E),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtSyntaxErrorKind {
    ExpectedToken(&'static [SmtTokenCategory]),
    ExpectedSymbol,
    ExpectedUnderscore,
    ExpectedSymbolOrUnderscore,
    ExpectedSymbolOrParenOpen,
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
    ExpectedPropositionalLiteral,
    EmptyFunctionSignatures,
    EmptyDatatypeIntroductions,
    EmptyDatatypeParameters,
    EmptyDatatypeConstructors,
    EmptyPatternArguments,
    EmptyMatchCases,
    EmptyGetValueTerms,

    UnsupportedVersion,
    TooManyVersionDeclarations(u64),
}

impl<E> SmtParseError<E> {
    #[cold]
    #[inline(never)]
    pub(crate) fn new(cause: SmtParseErrorCause<E>) -> Self {
        // PERFORMANCE: error cause is boxed
        // so that parser results are not unnecessarily large
        // this method boxes them, which forces an allocation
        // so it is is marked cold and never-inline
        Self(Box::new(cause))
    }

    pub(crate) fn handler_error(err: E) -> Self {
        Self::new(SmtParseErrorCause::Handler(err))
    }

    pub(crate) fn category_error(err: SmtSyntaxErrorKind) -> Self {
        Self::new(SmtParseErrorCause::Syntax(err))
    }

    pub fn cause(&self) -> &SmtParseErrorCause<E> {
        &self.0
    }

    pub fn into_cause(self) -> SmtParseErrorCause<E> {
        *self.0
    }
}

fn handle_err<O, E>(handled: Result<O, E>) -> Result<O, SmtParseError<E>> {
    match handled {
        Ok(ok) => Ok(ok),
        Err(err) => Err(SmtParseError::handler_error(err)),
    }
}

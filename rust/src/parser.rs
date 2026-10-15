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
    token::{SmtCursor, SmtReserved, SmtTokenCategory},
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
    fn parse<Z: SmtCursor>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>>;
}

/// Parses the cursor one token at a time with `progress`, until the cursor
/// is empty or `progress` breaks.
///
/// For parsers whose state machine steps by single tokens.
#[inline]
pub(crate) fn parse_by_token<Z: SmtCursor, R, E>(
    cursor: &mut Z,
    mut progress: impl FnMut(&Z, Z::Token) -> Result<ControlFlow<R>, E>,
) -> Result<ControlFlow<R>, E> {
    while let Some(token) = cursor.next() {
        if let ControlFlow::Break(result) = progress(cursor, token)? {
            return Ok(ControlFlow::Break(result));
        }
    }
    Ok(ControlFlow::Continue(()))
}

/// Error emitted by a parser.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtParseError<E>(Box<SmtParseErrorCause<E>>);

/// Why a parser failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtParseErrorCause<E> {
    /// The tokens do not form the syntax the parser accepts.
    Syntax(SmtSyntaxErrorKind),
    /// The script declares a version that cannot be used.
    Version(SmtVersionErrorKind),
    /// The handler failed.
    Handler(E),
}

/// What is wrong with the syntax.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtSyntaxErrorKind {
    /// One of the items was expected here.
    Expected(&'static [SmtSyntaxExpected]),
    /// A list that must not be empty is empty.
    Empty(SmtNonEmptyList),
    /// Fewer items arrived than were announced.
    Missing(SmtMissingItem),
}

/// An item that a parser expected, in [`SmtSyntaxErrorKind::Expected`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtSyntaxExpected {
    /// A token of the category.
    Token(SmtTokenCategory),
    /// The reserved word.
    Reserved(SmtReserved),
    /// A symbol, simple or quoted.
    Symbol,
    /// An index of an identifier: a numeral or a symbol.
    Index,
    Ident,
    Sort,
    Term,
    SExpr,
    Attribute,
    /// What follows the opening parenthesis of a compound term.
    Operator,
    /// The name of a command.
    CommandName,
    /// A propositional literal: a symbol or its negation.
    PropositionalLiteral,
}

/// A list that must not be empty, in [`SmtSyntaxErrorKind::Empty`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtNonEmptyList {
    IdentIndices,
    SortApplication,
    TermApplication,
    LetBindings,
    Annotation,
    QuantifierBindings,
    LambdaBindings,
    FunctionSignatures,
    DatatypeIntroductions,
    DatatypeParameters,
    DatatypeConstructors,
    PatternArguments,
    MatchCases,
    GetValueTerms,
}

/// An item of which fewer arrived than were announced, in [`SmtSyntaxErrorKind::Missing`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtMissingItem {
    /// A body of a function of `define-funs-rec`.
    FunctionBody,
    /// A datatype of `declare-datatypes`.
    Datatype,
}

/// The items that the library's parsers expect besides syntactic categories.
pub(crate) mod expected {
    use super::SmtSyntaxExpected;
    use crate::token::{SmtGeneralReserved, SmtReserved, SmtTokenCategory};

    pub(crate) const PAREN_OPEN: SmtSyntaxExpected =
        SmtSyntaxExpected::Token(SmtTokenCategory::ParenOpen);
    pub(crate) const PAREN_CLOSE: SmtSyntaxExpected =
        SmtSyntaxExpected::Token(SmtTokenCategory::ParenClose);
    pub(crate) const END_OF_FILE: SmtSyntaxExpected =
        SmtSyntaxExpected::Token(SmtTokenCategory::EndOfFile);
    pub(crate) const UNDERSCORE: SmtSyntaxExpected =
        SmtSyntaxExpected::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore));
    pub(crate) const AS: SmtSyntaxExpected =
        SmtSyntaxExpected::Reserved(SmtReserved::General(SmtGeneralReserved::As));
    pub(crate) const PAR: SmtSyntaxExpected =
        SmtSyntaxExpected::Reserved(SmtReserved::General(SmtGeneralReserved::Par));
}

/// What is wrong with the version a script declares.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtVersionErrorKind {
    /// The version is not one that can be switched to.
    Unsupported,
    /// The script declares its version more times than the limit allows.
    TooManyDeclarations(u64),
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

    pub fn handler(err: E) -> Self {
        Self::new(SmtParseErrorCause::Handler(err))
    }

    pub fn syntax(err: SmtSyntaxErrorKind) -> Self {
        Self::new(SmtParseErrorCause::Syntax(err))
    }

    pub fn version(err: SmtVersionErrorKind) -> Self {
        Self::new(SmtParseErrorCause::Version(err))
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
        Err(err) => Err(SmtParseError::handler(err)),
    }
}

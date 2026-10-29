//! Parsers of syntactic categories, commands, and scripts, and parser
//! combinators.
//!
//! A parser implements [`SmtParse`] and parses [tokens](crate::token), calling
//! a handler that implements [`SmtHandler`] to handle [grammar](crate::grammar)
//! constructs. The parser can be connected to a token producer through
//! [`SmtParseAdapter`] that implements [`SmtConsume`](crate::token::SmtConsume)
//! and [`SmtConsumeFrom`](crate::token::SmtConsumeFrom) for all token cursors,
//! and passes the handler and the parse state ([`SmtParseState`]) to the
//! parser.
//!
//! Parsers for all SMT-LIB grammar nodes are provided. As it is unknown if an
//! attribute is a name-only attribute (`:name`) or a name-value attribute
//! (`:key value`) before the next parsed token, only parsers for attribute and
//! multiple-attribute occurrences followed by a closing parenthesis are
//! provided through [`SmtClosedAttributeParser`] and
//! [`SmtClosedMultipleAttributeParser`]. This is enough to parse all attribute
//! occurrences in standard SMT-LIB.
//!
//! A single SMT-LIB command can be parsed using [`SmtCommandParser`], which
//! requires the handler to also implement
//! [`SmtCommandHandler`](crate::SmtCommandHandler).
//!
//! A whole SMT-LIB script can be parsed using [`SmtScriptParser`]. It
//! automatically discards after `(exit)` by calling [`SmtCursor::discard_rest`]
//! and switches SMT-LIB versions after the SMT-LIB command
//! `(set-info :smt-lib-version <version>)` by requesting the cursor to switch
//! through [`SmtCursor::set_version`] and informing the handler of the new
//! version in force through [`SmtHandler::set_version`] if successful.
//!
//! A custom parser can be crafted using combinators:
//! - sequential combinators [`SmtPairParser`], [`SmtTuple3Parser`] etc.,
//! - parenthesis enclosers [`SmtOpenedParser`], [`SmtClosedParser`],
//!   [`SmtParenParser`],
//! - multiple-item parsers [`SmtClosedMultipleParser`],
//!   [`SmtParenMultipleParser`], [`SmtClosedMaximumParser`] and
//!   [`SmtParenMaximumParser`].
//!
//! Additionally, [`SmtCommandPayloadParser`] is provided to simplify
//! implementing parsing of nonstandard commands for handlers that support
//! them.
//!
//! If needed, a parser can also be implemented manually. For example, a parser
//! that expects a simple symbol `sat`, `unsat`, or `unknown`, and extracts the
//! result:
//! ```
//! # use std::ops::ControlFlow;
//! # use blazing_smtlib::{SmtHandler, parser::{SmtParse, SmtParseState, SmtParseError},
//! # token::{SmtToken, SmtCursor}};
//! enum ResponseHandlerError {
//!     ExpectedSolverResult,
//!     // ... other error kinds ...
//! }
//! struct SolverResultParser;
//! impl<H: SmtHandler<Error = ResponseHandlerError>> SmtParse<H> for SolverResultParser {
//!     type Result = Option<bool>;
//!
//!     fn parse<Z: SmtCursor>(
//!         &mut self,
//!         _handler: &mut H,
//!         _parse_state: &mut SmtParseState<H>,
//!         cursor: &mut Z,
//!     ) -> Result<ControlFlow<Option<bool>>, SmtParseError<H::Error>> {
//!         let token = cursor
//!             .next()
//!             .expect("cursor should provide at least one token");
//!         if let SmtToken::Symbol(symbol) = cursor.syntax(&token)
//!             && !symbol.is_quoted()
//!         {
//!             match symbol.bytes().as_slice() {
//!                 b"sat" => return Ok(ControlFlow::Break(Some(true))),
//!                 b"unsat" => return Ok(ControlFlow::Break(Some(false))),
//!                 b"unknown" => return Ok(ControlFlow::Break(None)),
//!                 _ => {}
//!             }
//!         }
//!         Err(SmtParseError::handler(
//!             ResponseHandlerError::ExpectedSolverResult,
//!         ))
//!     }
//! }
//! ```

mod adapter;
mod category;
mod command;
mod script;
mod state;

use std::{error::Error, fmt, ops::ControlFlow};

pub use adapter::*;
pub use category::*;
pub use command::*;
pub use script::*;
pub use state::*;

use crate::{
    SmtHandler,
    lexicon::SmtReserved,
    token::{SmtCursor, SmtTokenCategory},
};

/// Parses a grammar item.
///
/// A parser is handed tokens through a cursor until it breaks with its result, e.g. by an
/// [`SmtParseAdapter`] or by a parser that contains it. A library parser that has broken with its
/// result can parse the next item.
pub trait SmtParse<H: SmtHandler + ?Sized> {
    /// Result returned by the parser on success.
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
    /// Returning an error means that the tokens do not form what the parser accepts, that
    /// a version switch failed, or that the handler failed. The state of the parser, cursor,
    /// and [`SmtParseState`] is then unspecified.
    ///
    /// All library parsers implementing [`SmtParse`] are fully self-resetting:
    /// after returning [`ControlFlow::Break`], they are back in their initial state.
    ///
    /// The `parse_state` holds the shared resources of library category parsers.
    /// To keep resources valid, each [`SmtParse`] must be progressed
    /// until completion once started, i.e. if [`SmtParse::parse`]
    /// returns `Ok(Continue(()))`, the subsequent outer parse call
    /// must call [`SmtParse::parse`] on the same parser, and
    /// is forbidden from progressing any other parsers.
    /// Failure to heed this contract may lead to silently wrong parsing
    /// or panics.
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

/// Error that forced parsing to stop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SmtParseError<E>(Box<SmtParseErrorKind<E>>);

/// Why parsing failed (syntax, version, or handler error).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SmtParseErrorKind<E> {
    /// The tokens do not form the syntax the parser accepts.
    Syntax(SmtSyntaxErrorKind),
    /// The script declares a version that cannot be used.
    Version(SmtVersionErrorKind),
    /// The handler failed.
    Handler(E),
}

/// Why the syntax was rejected (expected item, empty list, or missing item).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtSyntaxErrorKind {
    /// One of the items was expected here, e.g. a term in `(assert)`.
    Expected(&'static [SmtSyntaxExpected]),
    /// A list that must not be empty is empty, e.g. the indices in `(_ BitVec)`.
    Empty(SmtNonEmptyList),
    /// Fewer items arrived than were announced, e.g. fewer bodies than functions in
    /// `define-funs-rec`.
    Missing(SmtMissingItem),
}

/// Syntax item expected by a parser.
///
/// Used in [`SmtSyntaxErrorKind::Expected`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtSyntaxExpected {
    /// Token of the given category.
    Token(SmtTokenCategory),
    /// Reserved word, e.g. `_` or `as`.
    Reserved(SmtReserved),
    /// Symbol (quoted or unquoted), e.g. `x` or `|a b|`.
    Symbol,
    /// Index of an identifier (a numeral or a symbol), e.g. `32` in `(_ BitVec 32)`.
    Index,
    /// Identifier, e.g. `x` or `(_ bv0 32)`.
    Ident,
    /// Sort, e.g. `Int` or `(Array Int Bool)`.
    Sort,
    /// Term, e.g. `x` or `(+ x 1)`.
    Term,
    /// S-expression, e.g. `a` or `(a (b 1))`.
    SExpr,
    /// Attribute, e.g. `:status sat` or `:named p`.
    Attribute,
    /// What follows the opening parenthesis of a compound term, e.g. `f` in `(f x)` or `let`
    /// in `(let ((x 1)) x)`.
    Operator,
    /// Name of a command, e.g. `assert` or `check-sat`.
    CommandName,
    /// Propositional literal (a symbol or its negation), e.g. `p` or `(not p)`.
    PropositionalLiteral,
}

/// List that was expected to be non-empty.
///
/// Used in [`SmtSyntaxErrorKind::Empty`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtNonEmptyList {
    /// Indices of an identifier, e.g. `32` in `(_ BitVec 32)`.
    IdentIndices,
    /// Arguments of a sort, e.g. `Int Bool` in `(Array Int Bool)`.
    SortApplication,
    /// Arguments of an application, e.g. `x 1` in `(+ x 1)`.
    TermApplication,
    /// Bindings of `let`, e.g. `((x 1))` in `(let ((x 1)) x)`.
    LetBindings,
    /// Attributes of an annotation, e.g. `:named p` in `(! x :named p)`.
    Annotation,
    /// Variables of a quantifier, e.g. `((x Int))` in `(forall ((x Int)) p)`.
    QuantifierVars,
    /// Variables of `lambda`, e.g. `((x Int))` in `(lambda ((x Int)) x)`.
    LambdaVars,
    /// Functions of `define-funs-rec`, e.g. `((f () Int) (g () Int))`.
    FunctionSignatures,
    /// Sorts of `declare-datatypes`, e.g. `((A 0) (B 0))`.
    DatatypeIntroductions,
    /// Parameters of a datatype, e.g. `(T)` in `(par (T) ((c (f T))))`.
    DatatypeParameters,
    /// Constructors of a datatype, e.g. `((c (f T)))` in `(par (T) ((c (f T))))`.
    ///
    /// This arises only in the `par` form: without it, the first `(` opens a constructor.
    DatatypeConstructors,
    /// Arguments of a constructor pattern, e.g. `h t` in `(cons h t)`.
    PatternArguments,
    /// Cases of `match`, e.g. `((nil 0) ((cons h t) h))`.
    MatchCases,
    /// Terms of `get-value`, e.g. `(x y)` in `(get-value (x y))`.
    GetValueTerms,
}

/// Announced item that did not arrive (function body or datatype).
///
/// Used in [`SmtSyntaxErrorKind::Missing`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtMissingItem {
    /// Body of a function of `define-funs-rec`.
    ///
    /// For example, `(define-funs-rec ((f () Int) (g () Int)) (1))` lacks the body of `g`.
    FunctionBody,
    /// Datatype of `declare-datatypes`.
    ///
    /// For example, `(declare-datatypes ((A 0) (B 0)) (((a))))` lacks the datatype `B`.
    Datatype,
}

/// The items that the library's parsers expect besides syntactic categories.
pub(crate) mod expected {
    use super::SmtSyntaxExpected;
    use crate::{
        lexicon::{SmtGeneralReserved, SmtReserved},
        token::SmtTokenCategory,
    };

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

/// Why switching the version failed (unsupported version or too many declarations).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtVersionErrorKind {
    /// The requested version was rejected as not supported, e.g. `3.0`.
    ///
    /// The declared version is unknown (e.g. `3.0` or `foo`), not allowed by the posture, or
    /// refused by the cursor.
    Unsupported,
    /// The script declared its version more times than allowed.
    ///
    /// The number is the maximum that the posture allows.
    TooManyDeclarations(u64),
}

impl<E> SmtParseError<E> {
    #[cold]
    #[inline(never)]
    pub(crate) fn new(kind: SmtParseErrorKind<E>) -> Self {
        // PERFORMANCE: error kind is boxed
        // so that parser results are not unnecessarily large
        // this method boxes them, which forces an allocation
        // so it is is marked cold and never-inline
        Self(Box::new(kind))
    }

    /// Creates a handler error.
    pub fn handler(err: E) -> Self {
        Self::new(SmtParseErrorKind::Handler(err))
    }

    /// Creates a syntax error.
    pub fn syntax(err: SmtSyntaxErrorKind) -> Self {
        Self::new(SmtParseErrorKind::Syntax(err))
    }

    /// Creates a version error.
    pub fn version(err: SmtVersionErrorKind) -> Self {
        Self::new(SmtParseErrorKind::Version(err))
    }

    /// Returns the kind of the error.
    pub fn kind(&self) -> &SmtParseErrorKind<E> {
        &self.0
    }

    /// Converts into the kind of the error.
    pub fn into_kind(self) -> SmtParseErrorKind<E> {
        *self.0
    }
}

impl<E: fmt::Display> fmt::Display for SmtParseError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<E: Error + 'static> Error for SmtParseError<E> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &*self.0 {
            SmtParseErrorKind::Handler(err) => err.source(),
            SmtParseErrorKind::Syntax(_) | SmtParseErrorKind::Version(_) => None,
        }
    }
}

impl<E: fmt::Display> fmt::Display for SmtParseErrorKind<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Syntax(kind) => kind.fmt(f),
            Self::Version(kind) => kind.fmt(f),
            Self::Handler(err) => err.fmt(f),
        }
    }
}

impl fmt::Display for SmtSyntaxErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expected(expected) => {
                let Some((last, rest)) = expected.split_last() else {
                    return f.write_str("unexpected token");
                };
                f.write_str("expected ")?;
                if let Some((first, middle)) = rest.split_first() {
                    first.write_name(f)?;
                    for item in middle {
                        f.write_str(", ")?;
                        item.write_name(f)?;
                    }
                    // two items are joined by "or" alone, more with a serial comma
                    f.write_str(if middle.is_empty() { " or " } else { ", or " })?;
                }
                last.write_name(f)
            }
            Self::Empty(list) => list.fmt(f),
            Self::Missing(item) => item.fmt(f),
        }
    }
}

impl SmtSyntaxExpected {
    /// Writes the name of the item in a message.
    fn write_name(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name = match self {
            Self::Token(category) => match category {
                SmtTokenCategory::ParenOpen => "`(`",
                SmtTokenCategory::ParenClose => "`)`",
                SmtTokenCategory::Numeral => "numeral",
                SmtTokenCategory::Decimal => "decimal",
                SmtTokenCategory::Hexadecimal => "hexadecimal",
                SmtTokenCategory::Binary => "binary",
                SmtTokenCategory::String => "string literal",
                SmtTokenCategory::Keyword => "keyword",
                SmtTokenCategory::UnquotedSymbol => "simple symbol",
                SmtTokenCategory::QuotedSymbol => "quoted symbol",
                SmtTokenCategory::Whitespace => "whitespace",
                SmtTokenCategory::Comment => "comment",
                SmtTokenCategory::EndOfFile => "end of input",
            },
            Self::Reserved(reserved) => return write!(f, "`{}`", reserved.as_str()),
            Self::Symbol => "symbol",
            Self::Index => "index",
            Self::Ident => "identifier",
            Self::Sort => "sort",
            Self::Term => "term",
            Self::SExpr => "s-expression",
            Self::Attribute => "attribute",
            Self::Operator => "operator",
            Self::CommandName => "command name",
            Self::PropositionalLiteral => "propositional literal",
        };
        f.write_str(name)
    }
}

impl fmt::Display for SmtSyntaxExpected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("expected ")?;
        self.write_name(f)
    }
}

impl fmt::Display for SmtNonEmptyList {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let list = match self {
            Self::IdentIndices => "indices of identifier",
            Self::SortApplication => "arguments of sort",
            Self::TermApplication => "arguments of application",
            Self::LetBindings => "bindings of `let`",
            Self::Annotation => "attributes of annotation",
            Self::QuantifierVars => "variables of quantifier",
            Self::LambdaVars => "variables of `lambda`",
            Self::FunctionSignatures => "functions of `define-funs-rec`",
            Self::DatatypeIntroductions => "sorts of `declare-datatypes`",
            Self::DatatypeParameters => "parameters of datatype",
            Self::DatatypeConstructors => "constructors of datatype",
            Self::PatternArguments => "arguments of constructor pattern",
            Self::MatchCases => "cases of `match`",
            Self::GetValueTerms => "terms of `get-value`",
        };
        write!(f, "{list} must not be empty")
    }
}

impl fmt::Display for SmtMissingItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::FunctionBody => "too few function bodies for `define-funs-rec`",
            Self::Datatype => "too few datatypes for `declare-datatypes`",
        })
    }
}

impl fmt::Display for SmtVersionErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsupported => f.write_str("unsupported version"),
            Self::TooManyDeclarations(max) => {
                write!(f, "too many version declarations (at most {max})")
            }
        }
    }
}

fn handle_err<O, E>(handled: Result<O, E>) -> Result<O, SmtParseError<E>> {
    match handled {
        Ok(ok) => Ok(ok),
        Err(err) => Err(SmtParseError::handler(err)),
    }
}

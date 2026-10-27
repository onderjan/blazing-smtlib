//! Parsers of syntactic categories, commands, and scripts, and parser combinators.
//!
//!

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
    token::{SmtCursor, SmtReserved, SmtTokenCategory},
};

/// Parses a grammar item.
pub trait SmtParse<H: SmtHandler + ?Sized> {
    type Result;

    /// Parses tokens from the cursor, progressing the parser.
    ///
    /// If the parser returns [ControlFlow::Continue], it means all tokens
    /// were handled and more are wanted: the cursor must be empty.
    ///
    /// If the parser returns [ControlFlow::Break], it means
    /// it finished the input it accepts (consuming exactly its tokens),
    /// is returning a result and waiting for processing of the next value.
    ///
    /// Returning an error means the handler failed at the token after
    /// the consumed ones. The state of the parser, cursor, and resources
    /// is unspecified.
    ///
    /// All library parsers implementing [SmtParse] are fully self-resetting:
    /// after returning [ControlFlow::Break], they are back in their initial state.
    ///
    /// The `parse_state` holds the shared resources of standard category parsers.
    /// To keep resources valid, each [SmtParse] must be progressed
    /// until completion once started, i.e. if [SmtParse::parse()]
    /// returns `Ok(Continue(()))`, the subsequent outer parse call
    /// must call [SmtParse::parse()] on the same parser, and
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

/// Why a syntax error was returned (expected item, empty list, or missing item).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtSyntaxErrorKind {
    /// One of the items was expected here.
    Expected(&'static [SmtSyntaxExpected]),
    /// A list that must not be empty is empty.
    Empty(SmtNonEmptyList),
    /// Fewer items arrived than were announced.
    Missing(SmtMissingItem),
}

/// Syntax item expected by a parser.
///
/// Used in [SmtSyntaxErrorKind::Expected].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtSyntaxExpected {
    /// Token of the given category.
    Token(SmtTokenCategory),
    /// Reserved word.
    Reserved(SmtReserved),
    /// Symbol (quoted or unquoted).
    Symbol,
    /// Index of an identifier (a numeral or a symbol).
    Index,
    Ident,
    Sort,
    Term,
    SExpr,
    Attribute,
    /// What follows the opening parenthesis of a compound term.
    Operator,
    /// Name of a command.
    CommandName,
    /// Propositional literal (a symbol or its negation).
    PropositionalLiteral,
}

/// List that was expected to be non-empty.
///
/// Used in [SmtSyntaxErrorKind::Empty].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtNonEmptyList {
    IdentIndices,
    SortApplication,
    TermApplication,
    LetBindings,
    Annotation,
    QuantifierVars,
    LambdaVars,
    FunctionSignatures,
    DatatypeIntroductions,
    DatatypeParameters,
    DatatypeConstructors,
    PatternArguments,
    MatchCases,
    GetValueTerms,
}

/// Announced item that did not arrive (function body or datatype).
///
/// Used in [SmtSyntaxErrorKind::Missing].
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtMissingItem {
    /// Body of a function of `define-funs-rec`.
    FunctionBody,
    /// Datatype of `declare-datatypes`.
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

/// Why switching the version failed (unsupported version or too many declarations).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtVersionErrorKind {
    /// The requested version was rejected as not supported.
    ///
    /// This can happen if the parser itself rejects the version or
    /// [SmtCursor] rejects the version switch requested by
    /// [set_version](SmtCursor::set_version), prompting the parser to reject.
    ///
    /// The only parser in the library that switches versions is
    /// [SmtScriptParser], and it rejects on versions of SMT-LIB not supported
    /// by the library, versions not allowed by the posture, and lastly versions
    /// rejected by the cursor.
    ///
    /// [SmtLexerCursor](crate::lexer::SmtLexerCursor) never rejects a
    /// version, and [SmtTokensCursor](crate::token::SmtTokensCursor) rejects
    /// all versions except the one already in force.
    Unsupported,
    /// The script declares its version more times than allowed.
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

    pub fn handler(err: E) -> Self {
        Self::new(SmtParseErrorKind::Handler(err))
    }

    pub fn syntax(err: SmtSyntaxErrorKind) -> Self {
        Self::new(SmtParseErrorKind::Syntax(err))
    }

    pub fn version(err: SmtVersionErrorKind) -> Self {
        Self::new(SmtParseErrorKind::Version(err))
    }

    pub fn kind(&self) -> &SmtParseErrorKind<E> {
        &self.0
    }

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

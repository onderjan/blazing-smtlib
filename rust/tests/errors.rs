//! Public-API tests of the error types as errors: each is a `std::error::Error`,
//! its message is its kind followed by its location counted from one, its
//! location points where to look, and its source is that of the error it
//! carries.
//!
//! They check the Rust interface itself (`Display`, `Error` and `location()`),
//! so they call the reader and the lexer directly whatever `parse_backend`
//! selects. The messages are for people, so they are checked for their shape
//! and distinctness, not for their wording.

use std::collections::HashSet;
use std::error::Error;
use std::fmt::Display;
use std::io::{self, BufRead, Read};
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtNonstandardCommandError, SmtPartialCommandError, SmtReadError, SmtReadErrorKind,
    SmtSyntaxChecker, SmtVersion, SmtWriteError, SmtWriteErrorKind,
    grammar::SmtEmptyArgumentsError,
    lexer::{SmtLexer, SmtLexerCursor, SmtLexerError, SmtLexicalErrorKind, SmtLexicalExpected},
    lexicon::{
        SmtCommandNameReserved, SmtDisallowedByteVecError, SmtDisallowedBytesError,
        SmtGeneralReserved, SmtNumericOverflowError, SmtReserved, SmtSymbolBuf,
    },
    parser::{
        SmtMissingItem, SmtNonEmptyList, SmtParseError, SmtSyntaxErrorKind, SmtSyntaxExpected,
        SmtVersionErrorKind,
    },
    read_smt,
    span::{SmtInvalidLocationError, SmtInvalidSpanError, SmtLocation},
    token::{SmtConsume, SmtConsumeFrom, SmtCursor, SmtToken, SmtTokenCategory, SmtVersionRefused},
};

/// The error of a consumer or handler of the tests' own, with a source of its own.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Rejected;

impl Display for Rejected {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("rejected by the test")
    }
}

impl Error for Rejected {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(&Underlying)
    }
}

/// The source of [`Rejected`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Underlying;

impl Display for Underlying {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("underlying cause in the test")
    }
}

impl Error for Underlying {}

fn assert_error<T: Error + Send + Sync + 'static>() {}

/// Every type returned as an error is a `std::error::Error`, which can be
/// sent between threads when what it carries can, as `Box<dyn Error>` and
/// similar wrappers need.
#[test]
fn the_returned_error_types_are_errors() {
    assert_error::<SmtReadError<Rejected>>();
    assert_error::<SmtLexerError<Rejected>>();
    assert_error::<SmtParseError<Rejected>>();
    assert_error::<SmtPartialCommandError<Rejected>>();
    assert_error::<SmtNonstandardCommandError>();
    assert_error::<SmtWriteError>();
    assert_error::<SmtVersionRefused>();
    assert_error::<SmtDisallowedBytesError>();
    assert_error::<SmtDisallowedByteVecError>();
    assert_error::<SmtEmptyArgumentsError>();
    assert_error::<SmtInvalidLocationError>();
    assert_error::<SmtInvalidSpanError>();
    assert_error::<SmtNumericOverflowError>();
}

/// A location as zero-based `(line, column)`.
type LineColumn = (u64, u64);

fn line_column(location: SmtLocation) -> LineColumn {
    (location.line(), location.column())
}

/// Checks that the message is the kind's message at the location counted from one.
#[track_caller]
fn assert_message(message: String, kind: &impl Display, location: SmtLocation) {
    let expected = format!(
        "{kind} at line {}, column {}",
        location.line() + 1,
        location.column() + 1
    );
    assert_eq!(message, expected);
}

fn read_error(input: &[u8]) -> SmtReadError<SmtNonstandardCommandError> {
    read_smt(&mut SmtSyntaxChecker, input).expect_err("the input should fail to read")
}

/// A read error is located where its cause is to be looked for: at the start
/// of its span, or at the byte at fault: one forbidden in a string literal or
/// quoted symbol, or one that follows a token without delimiting it, which may
/// be lines away from the start of the token.
#[test]
fn a_read_error_reads_as_its_cause_at_its_location_counted_from_one() {
    let cases: &[(&[u8], LineColumn)] = &[
        // lexical errors
        (b"(check-sat)\n  #y", (1, 2)),
        (b"(echo \"ab\ncd\x01\")", (1, 2)),
        (b"(set-logic |a\\b|)", (0, 13)),
        (b"(set-logic |a\n\x01|)", (1, 0)),
        (b"(echo \"ab", (0, 6)),
        (b"(echo \"ab\ncd\"x)", (1, 3)),
        (b"(assert 12x)", (0, 10)),
        // syntax errors
        (b"(check-sat 1)", (0, 11)),
        (b"(get-value ())", (0, 12)),
        // a version error
        (b"(set-info :smt-lib-version 3.0)", (0, 30)),
        // a handler error
        (b"\n(frobnicate)", (1, 1)),
    ];
    for &(input, expected) in cases {
        let err = read_error(input);
        let text = String::from_utf8_lossy(input);
        assert_eq!(line_column(err.location()), expected, "{text:?}");
        assert_message(err.to_string(), err.kind(), err.location());
        // only the kinds where a byte is at fault look elsewhere than the span start
        let byte_at_fault = matches!(
            err.kind(),
            SmtReadErrorKind::Lexical(
                SmtLexicalErrorKind::ForbiddenByteInString
                    | SmtLexicalErrorKind::BackslashInQuotedSymbol
                    | SmtLexicalErrorKind::ForbiddenByteInQuotedSymbol
                    | SmtLexicalErrorKind::MissingDelimiter
            )
        );
        if byte_at_fault {
            // the span covers the token up to and including the byte at fault
            let end = err.span().end();
            assert_eq!(err.location().offset() + 1, end.offset(), "{text:?}");
            assert_eq!(line_column(err.location()), (end.line(), end.column() - 1));
        } else {
            assert_eq!(err.location(), err.span().start(), "{text:?}");
        }
    }
}

/// A token consumer that takes tokens until it is handed a numeral, which it
/// rejects with the error it makes.
struct RejectNumerals<E>(fn() -> E);

impl<E> SmtConsume for RejectNumerals<E> {
    type Result = ();
    type Error = E;
    const IS_CONCRETE: bool = false;
}

impl<'a, E> SmtConsumeFrom<SmtLexerCursor<'a>> for RejectNumerals<E> {
    fn consume(&mut self, cursor: &mut SmtLexerCursor<'a>) -> Result<ControlFlow<()>, E> {
        while let Some(token) = cursor.next() {
            if let SmtToken::Numeral(_) = cursor.syntax(&token) {
                return Err((self.0)());
            }
            if let SmtToken::EndOfFile = cursor.syntax(&token) {
                return Ok(ControlFlow::Break(()));
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

fn lex_error(input: &[u8]) -> SmtLexerError<Rejected> {
    let mut lexer = SmtLexer::new(RejectNumerals(|| Rejected), SmtVersion::V2_7);
    lexer
        .lex_all(input)
        .expect_err("the input should fail to lex")
}

/// A lex error is located as a read error is, and a consumer's error at the
/// token it was handed.
#[test]
fn a_lex_error_reads_as_its_cause_at_its_location_counted_from_one() {
    let cases: &[(&[u8], LineColumn)] = &[
        (b"a\n  #y", (1, 2)),
        (b"\"ab\ncd\x01\"", (1, 2)),
        (b"x |a\\b|", (0, 4)),
        (b"x\n y 42", (1, 3)),
        (b"\"ab\ncd\"x", (1, 3)),
    ];
    for &(input, expected) in cases {
        let err = lex_error(input);
        let text = String::from_utf8_lossy(input);
        assert_eq!(line_column(err.location()), expected, "{text:?}");
        assert_message(err.to_string(), err.kind(), err.location());
    }
}

/// A buffered reader that fails at once.
struct FailingReader;

impl Read for FailingReader {
    fn read(&mut self, _buf: &mut [u8]) -> io::Result<usize> {
        Err(io::Error::other(Rejected))
    }
}

impl BufRead for FailingReader {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        Err(io::Error::other(Rejected))
    }
    fn consume(&mut self, _amount: usize) {}
}

/// The source of an error that carries a handler's, consumer's or I/O error
/// is the source of that error, whose own message the error's message already
/// gives; an error of the library's own has none.
#[test]
fn the_source_is_the_source_of_the_carried_error() {
    let is_underlying = |source: Option<&(dyn Error + 'static)>| {
        source.is_some_and(|source| source.is::<Underlying>())
    };

    // a handler error, through the lexer as the reader meets it
    let mut lexer = SmtLexer::new(
        RejectNumerals(|| SmtParseError::handler(Rejected)),
        SmtVersion::V2_7,
    );
    let read = SmtReadError::from(lexer.lex_all(b"x 42").expect_err("the input should fail"));
    assert!(is_underlying(read.source()));
    assert_message(read.to_string(), &Rejected, read.location());
    // a handler error without a source of its own leaves none
    assert!(read_error(b"(frobnicate)").source().is_none());
    for input in [
        &b"#y"[..],
        b"(check-sat 1)",
        b"(set-info :smt-lib-version 3.0)",
    ] {
        assert!(read_error(input).source().is_none());
    }

    let io = read_smt(&mut SmtSyntaxChecker, FailingReader).expect_err("the reader fails");
    assert!(is_underlying(io.source()));
    assert!(io.to_string().contains(&Rejected.to_string()));
    assert_message(io.to_string(), io.kind(), io.location());

    let consumer = lex_error(b"42");
    assert!(is_underlying(consumer.source()));
    assert_message(consumer.to_string(), &Rejected, consumer.location());
    assert!(lex_error(b"#y").source().is_none());

    let parse = SmtParseError::handler(Rejected);
    assert!(is_underlying(parse.source()));
    assert_eq!(parse.to_string(), Rejected.to_string());
    let syntax: SmtParseError<Rejected> = SmtParseError::syntax(SmtSyntaxErrorKind::Expected(&[]));
    assert!(syntax.source().is_none());

    let partial = SmtPartialCommandError::Handler(Rejected);
    assert!(is_underlying(partial.source()));
    assert_eq!(partial.to_string(), Rejected.to_string());
    let unsupported: SmtPartialCommandError<Rejected> =
        SmtPartialCommandError::Unsupported(SmtCommandNameReserved::CheckSat);
    assert!(unsupported.source().is_none());

    let write = SmtWriteError::from(io::Error::other(Rejected));
    assert!(is_underlying(write.source()));
    assert!(write.to_string().contains(&Rejected.to_string()));
    let lambda = SmtToken::Reserved(SmtReserved::General(SmtGeneralReserved::Lambda));
    let not_in_version = lambda
        .write_smt(&mut Vec::new(), SmtVersion::V2_6)
        .expect_err("lambda is not reserved in 2.6");
    assert!(matches!(
        not_in_version.kind(),
        SmtWriteErrorKind::NotInVersion(_)
    ));
    assert!(not_in_version.source().is_none());
    assert_eq!(
        not_in_version.to_string(),
        not_in_version.kind().to_string()
    );
}

/// Checks that every message is non-empty and differs from the others, so
/// that a message tells which of the values it is.
#[track_caller]
fn assert_distinct(messages: impl IntoIterator<Item = String>) {
    let mut seen = HashSet::new();
    for message in messages {
        assert!(!message.is_empty(), "a message is empty");
        assert!(seen.insert(message.clone()), "{message:?} is not distinct");
    }
}

/// Each kind and item reads as a message of its own.
#[test]
fn every_kind_has_a_message_of_its_own() {
    let expected = [
        SmtLexicalExpected::FractionDigit,
        SmtLexicalExpected::HexadecimalDigit,
        SmtLexicalExpected::BinaryDigit,
        SmtLexicalExpected::Base,
    ];
    let mut lexical = vec![
        SmtLexicalErrorKind::UnexpectedByte,
        SmtLexicalErrorKind::UnclosedString,
        SmtLexicalErrorKind::ForbiddenByteInString,
        SmtLexicalErrorKind::EmptyKeyword,
        SmtLexicalErrorKind::BackslashInQuotedSymbol,
        SmtLexicalErrorKind::ForbiddenByteInQuotedSymbol,
        SmtLexicalErrorKind::UnclosedQuotedSymbol,
        SmtLexicalErrorKind::NumeralLeadingZero,
        SmtLexicalErrorKind::MissingDelimiter,
        SmtLexicalErrorKind::UnexpectedTrailingToken,
    ];
    lexical.extend(expected.map(SmtLexicalErrorKind::Expected));
    assert_distinct(lexical.iter().map(ToString::to_string));
    // the kind reads as the message of its expected item
    for item in expected {
        let message = SmtLexicalErrorKind::Expected(item).to_string();
        assert_eq!(message, item.to_string());
    }

    let categories = [
        SmtTokenCategory::ParenOpen,
        SmtTokenCategory::ParenClose,
        SmtTokenCategory::Numeral,
        SmtTokenCategory::Decimal,
        SmtTokenCategory::Hexadecimal,
        SmtTokenCategory::Binary,
        SmtTokenCategory::String,
        SmtTokenCategory::Keyword,
        SmtTokenCategory::UnquotedSymbol,
        SmtTokenCategory::QuotedSymbol,
        SmtTokenCategory::Whitespace,
        SmtTokenCategory::Comment,
        SmtTokenCategory::EndOfFile,
    ];
    let mut syntax_expected: Vec<SmtSyntaxExpected> =
        categories.map(SmtSyntaxExpected::Token).into();
    syntax_expected.extend([
        SmtSyntaxExpected::Reserved(SmtReserved::General(SmtGeneralReserved::As)),
        SmtSyntaxExpected::Reserved(SmtReserved::CommandName(SmtCommandNameReserved::CheckSat)),
        SmtSyntaxExpected::Symbol,
        SmtSyntaxExpected::Index,
        SmtSyntaxExpected::Ident,
        SmtSyntaxExpected::Sort,
        SmtSyntaxExpected::Term,
        SmtSyntaxExpected::SExpr,
        SmtSyntaxExpected::Attribute,
        SmtSyntaxExpected::Operator,
        SmtSyntaxExpected::CommandName,
        SmtSyntaxExpected::PropositionalLiteral,
    ]);
    assert_distinct(syntax_expected.iter().map(ToString::to_string));
    // a kind with one expected item reads as the message of that item
    for item in &syntax_expected {
        let alone: &'static [SmtSyntaxExpected] = Box::leak(Box::new([*item]));
        let message = SmtSyntaxErrorKind::Expected(alone).to_string();
        assert_eq!(message, item.to_string());
    }

    let lists = [
        SmtNonEmptyList::IdentIndices,
        SmtNonEmptyList::SortApplication,
        SmtNonEmptyList::TermApplication,
        SmtNonEmptyList::LetBindings,
        SmtNonEmptyList::Annotation,
        SmtNonEmptyList::QuantifierVars,
        SmtNonEmptyList::LambdaVars,
        SmtNonEmptyList::FunctionSignatures,
        SmtNonEmptyList::DatatypeIntroductions,
        SmtNonEmptyList::DatatypeParameters,
        SmtNonEmptyList::DatatypeConstructors,
        SmtNonEmptyList::PatternArguments,
        SmtNonEmptyList::MatchCases,
        SmtNonEmptyList::GetValueTerms,
    ];
    assert_distinct(lists.iter().map(ToString::to_string));
    let items = [SmtMissingItem::FunctionBody, SmtMissingItem::Datatype];
    assert_distinct(items.iter().map(ToString::to_string));

    let mut syntax: Vec<SmtSyntaxErrorKind> = lists.map(SmtSyntaxErrorKind::Empty).into();
    syntax.extend(items.map(SmtSyntaxErrorKind::Missing));
    syntax.push(SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Term]));
    assert_distinct(syntax.iter().map(ToString::to_string));
    // the kinds read as the messages of their lists and items
    for list in lists {
        let message = SmtSyntaxErrorKind::Empty(list).to_string();
        assert_eq!(message, list.to_string());
    }
    for item in items {
        let message = SmtSyntaxErrorKind::Missing(item).to_string();
        assert_eq!(message, item.to_string());
    }

    let version = [
        SmtVersionErrorKind::Unsupported,
        SmtVersionErrorKind::TooManyDeclarations(1),
        SmtVersionErrorKind::TooManyDeclarations(2),
    ];
    assert_distinct(version.iter().map(ToString::to_string));

    let partial: [SmtPartialCommandError<Rejected>; 4] = [
        SmtPartialCommandError::Unsupported(SmtCommandNameReserved::CheckSat),
        SmtPartialCommandError::Unsupported(SmtCommandNameReserved::DeclareFun),
        SmtPartialCommandError::UnsupportedNonstandard(
            SmtSymbolBuf::new_unquoted(b"frobnicate".to_vec()).expect("a simple symbol"),
        ),
        SmtPartialCommandError::UnsupportedNonstandard(
            SmtSymbolBuf::new_quoted(b"frobnicate".to_vec()).expect("a quoted symbol"),
        ),
    ];
    assert_distinct(partial.iter().map(ToString::to_string));
    // the command is named in the message
    assert!(partial[0].to_string().contains("check-sat"));
    assert!(partial[2].to_string().contains("frobnicate"));
}

/// An expected-items message differs with the items it lists and their order.
#[test]
fn an_expected_message_differs_with_its_items_and_their_order() {
    const PAREN_CLOSE: SmtSyntaxExpected = SmtSyntaxExpected::Token(SmtTokenCategory::ParenClose);
    let lists: &[&'static [SmtSyntaxExpected]] = &[
        &[],
        &[SmtSyntaxExpected::Term],
        &[SmtSyntaxExpected::Sort],
        &[SmtSyntaxExpected::Term, SmtSyntaxExpected::Sort],
        &[SmtSyntaxExpected::Sort, SmtSyntaxExpected::Term],
        &[SmtSyntaxExpected::Ident, SmtSyntaxExpected::Term],
        &[
            PAREN_CLOSE,
            SmtSyntaxExpected::Term,
            SmtSyntaxExpected::Sort,
        ],
        &[
            SmtSyntaxExpected::Term,
            PAREN_CLOSE,
            SmtSyntaxExpected::Sort,
        ],
        &[
            PAREN_CLOSE,
            SmtSyntaxExpected::Ident,
            SmtSyntaxExpected::Sort,
        ],
    ];
    assert_distinct(
        lists
            .iter()
            .map(|list| SmtSyntaxErrorKind::Expected(list).to_string()),
    );
}

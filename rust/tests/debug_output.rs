//! Tests of what the parsing machinery prints with `Debug`: each parser its
//! name only, and the lexer, its cursor and the reader also the version
//! and, for the lexer, the location they are at.
//!
//! They check the Rust interface itself (`Debug` output) and call the
//! library directly.

use std::convert::Infallible;
use std::fmt::Debug;
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtReader, SmtSyntaxChecker, SmtVersion, SmtVersionPosture,
    lexer::{SmtLexer, SmtLexerCursor},
    parser::{
        SmtCloseParenParser, SmtClosedAttributeParser, SmtClosedMultipleAttributeParser,
        SmtClosedMultipleParser, SmtClosedParser, SmtCommandParser, SmtIdentParser,
        SmtKeywordParser, SmtNumeralParser, SmtOpenParenParser, SmtOpenedParser,
        SmtParenMultipleParser, SmtParenParser, SmtPatternParser, SmtQualifiedIdentParser,
        SmtSExprParser, SmtScriptParser, SmtSimplePatternParser, SmtSortParser, SmtSortedVarParser,
        SmtStringParser, SmtSymbolParser, SmtTermParser, SmtTuple3Parser, SmtTuple8Parser,
    },
    span::SmtLocation,
    token::{SmtConsume, SmtConsumeFrom, SmtCursor, SmtToken},
};

type H = SmtSyntaxChecker;
type S = SmtSymbolParser;

/// What a parser in its initial state prints.
fn printed<P: Debug + Default>() -> String {
    format!("{:?}", P::default())
}

#[test]
fn a_parser_prints_its_name_only() {
    let cases = [
        (printed::<SmtSymbolParser>(), "SmtSymbolParser"),
        (printed::<SmtOpenParenParser>(), "SmtOpenParenParser"),
        (printed::<SmtCloseParenParser>(), "SmtCloseParenParser"),
        (printed::<SmtNumeralParser>(), "SmtNumeralParser"),
        (printed::<SmtKeywordParser>(), "SmtKeywordParser"),
        (printed::<SmtStringParser>(), "SmtStringParser"),
        (printed::<SmtIdentParser>(), "SmtIdentParser"),
        (
            printed::<SmtSimplePatternParser>(),
            "SmtSimplePatternParser",
        ),
        (printed::<SmtPatternParser<H>>(), "SmtPatternParser"),
        (
            printed::<SmtQualifiedIdentParser<H>>(),
            "SmtQualifiedIdentParser",
        ),
        (printed::<SmtSortParser<H>>(), "SmtSortParser"),
        (printed::<SmtSortedVarParser<H>>(), "SmtSortedVarParser"),
        (printed::<SmtSExprParser<H>>(), "SmtSExprParser"),
        (printed::<SmtTermParser<H>>(), "SmtTermParser"),
        (
            printed::<SmtClosedAttributeParser<H>>(),
            "SmtClosedAttributeParser",
        ),
        (
            printed::<SmtClosedMultipleAttributeParser<H>>(),
            "SmtClosedMultipleAttributeParser",
        ),
        (printed::<SmtClosedParser<H, S>>(), "SmtClosedParser"),
        (printed::<SmtOpenedParser<H, S>>(), "SmtOpenedParser"),
        (printed::<SmtParenParser<H, S>>(), "SmtParenParser"),
        (
            printed::<SmtClosedMultipleParser<H, S>>(),
            "SmtClosedMultipleParser",
        ),
        (
            printed::<SmtParenMultipleParser<H, S>>(),
            "SmtParenMultipleParser",
        ),
        (printed::<SmtTuple3Parser<H, S, S, S>>(), "SmtTuple3Parser"),
        (
            printed::<SmtTuple8Parser<H, S, S, S, S, S, S, S, S>>(),
            "SmtTuple8Parser",
        ),
        (printed::<SmtCommandParser<H>>(), "SmtCommandParser"),
        (printed::<SmtScriptParser<H>>(), "SmtScriptParser"),
    ];
    for (printed, name) in cases {
        assert_eq!(printed, format!("{name} {{ .. }}"));
    }
}

/// A consumer that keeps what the cursor of its first batch printed.
#[derive(Default)]
struct PrintedCursor {
    printed: Option<String>,
}

impl SmtConsume for PrintedCursor {
    type Result = ();
    type Error = Infallible;
    const IS_CONCRETE: bool = false;
}

impl<'a> SmtConsumeFrom<SmtLexerCursor<'a>> for PrintedCursor {
    fn consume(&mut self, cursor: &mut SmtLexerCursor<'a>) -> Result<ControlFlow<()>, Infallible> {
        self.printed.get_or_insert_with(|| format!("{cursor:?}"));
        while let Some(token) = cursor.next() {
            if matches!(cursor.syntax(&token), SmtToken::EndOfFile) {
                return Ok(ControlFlow::Break(()));
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

#[test]
fn the_lexer_and_its_cursor_print_their_version_and_the_lexer_its_location() {
    let mut lexer = SmtLexer::new(PrintedCursor::default(), SmtVersion::V2_6);
    lexer
        .lex_slice(b"(check-sat)\n(")
        .unwrap_or_else(|err| panic!("unexpected error {:?}", err.cause()));
    let location = lexer.current_location();
    assert_ne!(location, SmtLocation::initial(), "the lexer has moved on");
    assert_eq!(
        format!("{lexer:?}"),
        format!("SmtLexer {{ version: V2_6, current_location: {location:?}, .. }}")
    );
    assert_eq!(
        lexer.consumer().printed.as_deref(),
        Some("SmtLexerCursor { version: V2_6, .. }")
    );
}

#[test]
fn the_reader_prints_the_version_in_force() {
    let mut handler = SmtSyntaxChecker;
    let mut reader =
        SmtReader::script(&mut handler, SmtVersionPosture::default(), SmtVersion::V2_7);
    assert_eq!(format!("{reader:?}"), "SmtReader { version: V2_7, .. }");
    reader
        .read_slice(b"(set-info :smt-lib-version 2.6)")
        .unwrap_or_else(|err| panic!("unexpected error {:?}", err.cause()));
    assert_eq!(format!("{reader:?}"), "SmtReader { version: V2_6, .. }");
}

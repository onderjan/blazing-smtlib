//! Public-API tests of the top-level reader entry points.

use std::io::{BufRead, Read};

use smt_parser_rs::{
    CheckStandardSyntax, NonstandardCommandError, SmtLocation,
    read::{
        SmtReadError, SmtReadErrorKind, lexer::LexerErrorKind, parser::CategoryParserErrorKind,
        read_smt, read_smt_file,
    },
};

/// Expected location as `(offset, line, column)`.
type Loc = (u64, u64, u64);

fn loc(location: SmtLocation) -> Loc {
    (location.offset(), location.line(), location.column())
}

fn read(input: &[u8]) -> Result<(), SmtReadError<NonstandardCommandError>> {
    read_smt(&mut CheckStandardSyntax, input)
}

#[track_caller]
fn assert_span(err: &SmtReadError<NonstandardCommandError>, start: Loc, end: Loc) {
    let span = err.span();
    assert_eq!(
        (loc(span.start()), loc(span.end())),
        (start, end),
        "span mismatch (start, end) as (offset, line, column)"
    );
}

#[test]
fn valid_input_has_no_error() {
    assert!(read(b"").is_ok());
    assert!(read(b"(set-logic QF_UF)\n(check-sat)\n").is_ok());
    assert!(read(b"; comment only").is_ok());
}

#[test]
fn lexer_error_kind_and_span_are_passed_through() {
    // the string literal starts on line 3, column 3 (offset 15) and is unclosed at EOF
    let err = read(b"(check-sat)\n\n  \"abc").expect_err("expected a lexer error, got Ok");
    assert!(matches!(
        err.kind(),
        SmtReadErrorKind::Lexer(LexerErrorKind::UnclosedStringLiteral)
    ));
    assert_span(&err, (15, 3, 3), (19, 3, 7));
}

#[test]
fn parser_error_span_is_resolved_to_lines() {
    // `(assert )` is missing a term; the offending token is the `)` on line 2
    let err = read(b"(check-sat)\n(assert )").expect_err("expected a parser error, got Ok");
    assert!(matches!(
        err.kind(),
        SmtReadErrorKind::Parser(CategoryParserErrorKind::ExpectedTerm)
    ));
    assert_span(&err, (20, 2, 9), (21, 2, 10));
}

#[test]
fn parser_error_deep_in_the_input_is_resolved_to_lines() {
    // the empty application `(f )` is rejected on its closing parenthesis,
    // which is the ninth byte of the third line
    let input = b"(set-logic QF_UF)\n(declare-const x Bool)\n(assert (f ))\n";
    let err = read(input).expect_err("expected a parser error, got Ok");
    assert!(matches!(
        err.kind(),
        SmtReadErrorKind::Parser(CategoryParserErrorKind::EmptyTermApplication)
    ));
    assert_span(&err, (52, 3, 12), (53, 3, 13));
}

#[test]
fn handler_error_span_is_resolved_to_lines() {
    // the handler rejects the command by name, and the reported span is that
    // of the name symbol on the second line rather than of the whole command
    let err = read(b"(check-sat)\n(frobnicate 1)").expect_err("expected a handler error");
    assert!(matches!(err.kind(), SmtReadErrorKind::Handler(_)));
    assert_span(&err, (13, 2, 2), (23, 2, 12));
}

#[test]
fn span_after_a_token_containing_a_line_break() {
    // the quoted symbol carries the line break, so the offending `x` after it
    // must be reported on the second line
    let err = read(b"(assert |a\nb| x)").expect_err("expected a parser error, got Ok");
    assert!(matches!(err.kind(), SmtReadErrorKind::Parser(_)));
    assert_span(&err, (14, 2, 4), (15, 2, 5));
}

#[test]
fn parser_error_at_eof_is_empty_span() {
    // unclosed command: the error is on the zero-width EOF token after a newline
    let err = read(b"(check-sat\n").expect_err("expected a parser error, got Ok");
    assert!(matches!(err.kind(), SmtReadErrorKind::Parser(_)));
    assert_span(&err, (11, 2, 1), (11, 2, 1));
}

/// Reader that yields the given bytes and then fails.
struct FailingReader<'a> {
    data: &'a [u8],
}

impl Read for FailingReader<'_> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        if self.data.is_empty() {
            return Err(std::io::Error::other("simulated failure"));
        }
        self.data.read(buf)
    }
}

impl BufRead for FailingReader<'_> {
    fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
        if self.data.is_empty() {
            return Err(std::io::Error::other("simulated failure"));
        }
        Ok(self.data)
    }

    fn consume(&mut self, amt: usize) {
        self.data = &self.data[amt..];
    }
}

#[test]
fn io_error_has_empty_span_at_current_location() {
    let reader = FailingReader {
        data: b"(check-sat)\n(",
    };
    let err =
        read_smt(&mut CheckStandardSyntax, reader).expect_err("expected an I/O error, got Ok");
    assert!(matches!(err.kind(), SmtReadErrorKind::Io(_)));
    // 13 bytes were consumed, so the location is line 2, column 2
    assert_span(&err, (13, 2, 2), (13, 2, 2));
}

#[test]
fn file_open_error_has_zero_span() {
    let path = std::path::Path::new("/nonexistent/smt-parser-test/does-not-exist.smt2");
    let err =
        read_smt_file(&mut CheckStandardSyntax, path).expect_err("expected an I/O error, got Ok");
    assert!(matches!(err.kind(), SmtReadErrorKind::Io(_)));
    assert_span(&err, (0, 1, 1), (0, 1, 1));
}

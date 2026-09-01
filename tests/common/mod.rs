//! Shared helpers driving full command streams through the public reader.

use smt_parser_rs::{
    CheckStandardSyntax, CommandHandler, SmtHandler,
    read::{SmtReadError, SmtReadErrorKind, parser::CategoryParserErrorKind, read_smt},
};

/// Parses the whole input, feeding the commands to the given handler.
pub fn parse_with<H: CommandHandler>(handler: &mut H, input: &[u8]) -> Result<(), SmtReadError<H>> {
    read_smt(handler, input)
}

/// Parses the whole input with the standard syntax checker.
pub fn parse(input: &[u8]) -> Result<(), SmtReadError<CheckStandardSyntax>> {
    parse_with(&mut CheckStandardSyntax, input)
}

#[track_caller]
pub fn assert_error_span<H: SmtHandler>(err: &SmtReadError<H>, start: u64, end: u64) {
    let span = err.span();
    assert_eq!(
        (span.start().offset(), span.end().offset()),
        (start, end),
        "error span mismatch (start, end) as byte offsets"
    );
}

/// Parses the input, requires a parser error, checks the byte span the error carries,
/// and returns its kind so that the caller can inspect the variant.
#[track_caller]
pub fn assert_parser_error(input: &[u8], start: u64, end: u64) -> CategoryParserErrorKind {
    let err = parse(input).expect_err("expected a parser error, got Ok");
    assert_error_span(&err, start, end);
    match err.into_kind() {
        SmtReadErrorKind::Parser(kind) => kind,
        SmtReadErrorKind::Handler(err) => {
            panic!("expected parser error, got handler error on {:?}", err.0)
        }
        SmtReadErrorKind::Lexer(kind) => {
            panic!("expected parser error, got lexer error {kind:?}")
        }
        SmtReadErrorKind::Io(err) => panic!("expected parser error, got I/O error {err}"),
    }
}

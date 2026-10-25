//! Tests of lexing a whole input from a buffered reader or a file: it
//! lexes as the same input in one slice does, consumes the buffered reader
//! up to where the consumer discards the rest, and reports an I/O failure
//! with an empty span where reading failed.
//!
//! They check the Rust interface itself (`lex_from` and `lex_file`, which
//! the Lean port does not have yet) and call the lexer directly.

use std::convert::Infallible;
use std::io::{self, BufRead, Read};
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtVersion,
    lexer::{
        SmtLexer, SmtLexerCursor, SmtLexerError, SmtLexerReadError, SmtLexerReadErrorCause,
        SmtLexicalErrorKind,
    },
    span::SmtLocation,
    token::{SmtConsume, SmtConsumeFrom, SmtCursor, SmtSyntaxToken},
};

/// A consumer that keeps the abstract tokens as debugged, and discards the
/// rest of the input after the first `(exit)` if asked to.
#[derive(Default)]
struct Tokens {
    discards_after_exit: bool,
    tokens: Vec<String>,
}

impl SmtConsume for Tokens {
    type Result = Vec<String>;
    type Error = Infallible;
    const IS_CONCRETE: bool = false;
}

impl<'a> SmtConsumeFrom<SmtLexerCursor<'a>> for Tokens {
    fn consume(
        &mut self,
        cursor: &mut SmtLexerCursor<'a>,
    ) -> Result<ControlFlow<Vec<String>>, Infallible> {
        while let Some(token) = cursor.next() {
            let token = cursor.syntax(&token);
            if matches!(token, SmtSyntaxToken::EndOfFile) {
                return Ok(ControlFlow::Break(std::mem::take(&mut self.tokens)));
            }
            self.tokens.push(format!("{token:?}"));
            if self.discards_after_exit && self.tokens.len() >= 3 {
                let last = &self.tokens[self.tokens.len() - 3..];
                if last[1].contains("Exit") && last[2] == "ParenClose" {
                    cursor.discard_rest();
                }
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Where the location is, as `(offset, line, column)`.
fn loc(location: SmtLocation) -> (u64, u64, u64) {
    (location.offset(), location.line(), location.column())
}

/// A buffered reader that hands out the input `size` bytes at a time.
struct Chunks<'a> {
    input: &'a [u8],
    size: usize,
}

impl Read for Chunks<'_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let chunk = self.fill_buf()?;
        let len = chunk.len().min(buf.len());
        buf[..len].copy_from_slice(&chunk[..len]);
        self.consume(len);
        Ok(len)
    }
}

impl BufRead for Chunks<'_> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        Ok(&self.input[..self.size.min(self.input.len())])
    }

    fn consume(&mut self, amount: usize) {
        self.input = &self.input[amount..];
    }
}

/// A buffered reader that hands out the input and then fails.
struct Failing<'a> {
    input: &'a [u8],
}

impl Read for Failing<'_> {
    fn read(&mut self, _buf: &mut [u8]) -> io::Result<usize> {
        Err(io::Error::other(
            "the test reader is read only through its buffer",
        ))
    }
}

impl BufRead for Failing<'_> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        if self.input.is_empty() {
            Err(io::Error::other("the test reader fails after its input"))
        } else {
            Ok(self.input)
        }
    }

    fn consume(&mut self, amount: usize) {
        self.input = &self.input[amount..];
    }
}

const INPUT: &[u8] = b"(set-logic QF_UF)\n(assert (= x #b01))\n; done\n(check-sat)\n";

#[test]
fn lexing_from_a_buffered_reader_lexes_as_the_slice_does_whatever_its_buffers() {
    let whole = SmtLexer::new(Tokens::default(), SmtVersion::V2_7)
        .lex_all(INPUT)
        .expect("the input lexes");
    for size in [1, 2, 3, 7, 64] {
        let mut lexer = SmtLexer::new(Tokens::default(), SmtVersion::V2_7);
        let located = lexer
            .lex_from(Chunks { input: INPUT, size })
            .unwrap_or_else(|err| panic!("unexpected error {:?}", err.cause()));
        assert_eq!(located.location(), whole.location(), "buffers of {size}");
        assert_eq!(located.value(), whole.value(), "buffers of {size}");
    }
}

#[test]
fn lexing_from_a_buffered_reader_consumes_it_up_to_where_the_rest_is_discarded() {
    let input = b"(check-sat) (exit) x ) (";
    let consumer = Tokens {
        discards_after_exit: true,
        ..Tokens::default()
    };
    let mut rest = &input[..];
    let located = SmtLexer::new(consumer, SmtVersion::V2_7)
        .lex_from(&mut rest)
        .unwrap_or_else(|err| panic!("unexpected error {:?}", err.cause()));
    assert_eq!(loc(located.location()), (18, 0, 18));
    assert_eq!(rest, b" x ) (");
    // without discarding, the whole input is consumed
    let mut rest = &input[..];
    let located = SmtLexer::new(Tokens::default(), SmtVersion::V2_7)
        .lex_from(&mut rest)
        .unwrap_or_else(|err| panic!("unexpected error {:?}", err.cause()));
    assert_eq!(loc(located.location()), (24, 0, 24));
    assert!(rest.is_empty());
}

#[test]
fn a_failure_of_the_buffered_reader_is_an_io_error_with_an_empty_span_where_it_failed() {
    let err = SmtLexer::new(Tokens::default(), SmtVersion::V2_7)
        .lex_from(Failing {
            input: b"(check-sat)\n(",
        })
        .expect_err("the reader fails");
    assert!(matches!(err.cause(), SmtLexerReadErrorCause::Io(_)));
    assert_eq!(loc(err.span().start()), (13, 1, 1));
    assert_eq!(loc(err.span().end()), (13, 1, 1));
    assert_eq!(err.location(), err.span().start());
    assert!(
        err.to_string()
            .starts_with("I/O: the test reader fails after its input at line 2, column 2"),
        "{err}"
    );
}

#[test]
fn a_lexical_error_from_a_buffered_reader_is_the_one_of_the_slice() {
    let input = b"(assert (= x #b012))";
    let from_slice: SmtLexerError<Infallible> = SmtLexer::new(Tokens::default(), SmtVersion::V2_7)
        .lex_all(input)
        .expect_err("the input does not lex");
    for size in [1, 4, 64] {
        let err: SmtLexerReadError<Infallible> = SmtLexer::new(Tokens::default(), SmtVersion::V2_7)
            .lex_from(Chunks { input, size })
            .expect_err("the input does not lex");
        assert!(
            matches!(
                err.cause(),
                SmtLexerReadErrorCause::Lexical(SmtLexicalErrorKind::MissingDelimiter)
            ),
            "{:?}",
            err.cause()
        );
        assert_eq!(err.span(), from_slice.span(), "buffers of {size}");
        assert_eq!(err.location(), from_slice.location(), "buffers of {size}");
        assert_eq!(err.to_string(), from_slice.to_string(), "buffers of {size}");
    }
}

#[test]
fn lexing_a_file_lexes_its_content_and_fails_to_open_with_a_zero_span() {
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("lexer-read.smt2");
    std::fs::write(&path, INPUT).expect("the test file can be written");
    let whole = SmtLexer::new(Tokens::default(), SmtVersion::V2_7)
        .lex_all(INPUT)
        .expect("the input lexes");
    let located = SmtLexer::new(Tokens::default(), SmtVersion::V2_7)
        .lex_file(&path)
        .unwrap_or_else(|err| panic!("unexpected error {:?}", err.cause()));
    assert_eq!(located.location(), whole.location());
    assert_eq!(located.value(), whole.value());

    let missing = std::path::Path::new("/nonexistent/blazing-smtlib-test/missing.smt2");
    let err = SmtLexer::new(Tokens::default(), SmtVersion::V2_7)
        .lex_file(missing)
        .expect_err("the file does not exist");
    assert!(matches!(err.cause(), SmtLexerReadErrorCause::Io(_)));
    assert_eq!(loc(err.span().start()), (0, 0, 0));
    assert!(err.span().is_empty());
}

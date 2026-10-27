//! Tests of lexing a whole input from a buffered reader or a file: it
//! lexes as the same input in one slice does, consumes the buffered reader
//! up to where the consumer discards the rest, and reports an I/O failure
//! with an empty span where reading failed.
//!
//! The tests of this behaviour run against `lex_backend`, so that the
//! driver runs them against the Lean port too; there the buffered reader is
//! one of the driver's, which hands out the bytes it is given a number at a
//! time. The tests of the Rust interface itself call the lexer directly and
//! say so.

mod lex_backend;

use std::convert::Infallible;
use std::io::{self, BufRead, Read};
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtVersion,
    lexer::{
        SmtLexer, SmtLexerCursor, SmtLexerError, SmtLexerReadError, SmtLexerReadErrorKind,
        SmtLexicalErrorKind,
    },
    token::{SmtConsume, SmtConsumeFrom, SmtCursor, SmtToken},
};
use lex_backend::{LexedToken, Line, Loc, Options, ReaderEnd};

const INPUT: &[u8] = b"(set-logic QF_UF)\n(assert (= x #b01))\n; done\n(check-sat)\n";

/// The tokens a run reported, and the line of its outcome, which is its last.
fn outcome(mut lines: Vec<Line>) -> (Vec<LexedToken>, Line) {
    let last = lines.pop().expect("a response ends with its outcome");
    let tokens = lines
        .into_iter()
        .map(|line| match line {
            Line::Token(token) => token,
            other => panic!("a line that no option asked for: {other:?}"),
        })
        .collect();
    (tokens, last)
}

/// The tokens of the input lexed in one slice, and where the result is
/// returned: at the end of the input, after the last token.
fn lexed_whole(input: &[u8]) -> (Vec<LexedToken>, Loc) {
    let whole = lex_backend::lex_whole(SmtVersion::V2_7, input);
    assert_eq!(whole.error, None, "the input lexes");
    let end = whole
        .tokens
        .last()
        .expect("the end of the input is handed over")
        .end;
    (whole.tokens, end)
}

#[test]
fn lexing_from_a_buffered_reader_lexes_as_the_slice_does_whatever_its_buffers() {
    let (tokens, end) = lexed_whole(INPUT);
    for size in [1, 2, 3, 7, 64] {
        let (from_reader, last) = outcome(lex_backend::lex_from(
            SmtVersion::V2_7,
            &Options::default(),
            size,
            INPUT,
            ReaderEnd::End,
        ));
        assert_eq!(from_reader, tokens, "buffers of {size}");
        assert_eq!(
            last,
            Line::Done {
                location: end,
                rest: Some(0)
            },
            "buffers of {size}"
        );
    }
}

#[test]
fn lexing_from_a_buffered_reader_consumes_it_up_to_where_the_rest_is_discarded() {
    let input = b"(check-sat) (exit) x ) (";
    // the consumer discards the rest after `(exit)`, its sixth token
    let discarding = Options {
        behaviour: lex_backend::driver::Behaviour::Discard(6),
        ..Options::default()
    };
    let (_, last) = outcome(lex_backend::lex_from(
        SmtVersion::V2_7,
        &discarding,
        input.len(),
        input,
        ReaderEnd::End,
    ));
    assert_eq!(
        last,
        Line::Done {
            location: (18, 0, 18),
            rest: Some(b" x ) (".len() as u64)
        }
    );
    // without discarding, the whole input is consumed
    let (_, last) = outcome(lex_backend::lex_from(
        SmtVersion::V2_7,
        &Options::default(),
        input.len(),
        input,
        ReaderEnd::End,
    ));
    assert_eq!(
        last,
        Line::Done {
            location: (24, 0, 24),
            rest: Some(0)
        }
    );
}

#[test]
fn a_failure_of_the_buffered_reader_is_an_io_error_with_an_empty_span_where_it_failed() {
    let input = b"(check-sat)\n(";
    let (_, last) = outcome(lex_backend::lex_from(
        SmtVersion::V2_7,
        &Options::default(),
        input.len(),
        input,
        ReaderEnd::Fail,
    ));
    assert_eq!(
        last,
        Line::IoError {
            start: (13, 1, 1),
            end: (13, 1, 1),
            message: lex_backend::driver::READER_FAILURE.as_bytes().to_vec(),
        }
    );
}

#[test]
fn a_lexical_error_from_a_buffered_reader_is_the_one_of_the_slice() {
    let input = b"(assert (= x #b012))";
    let from_slice = lex_backend::lex_whole(SmtVersion::V2_7, input)
        .error
        .expect("the input does not lex");
    assert_eq!(from_slice.kind, SmtLexicalErrorKind::MissingDelimiter);
    for size in [1, 4, 64] {
        let (_, last) = outcome(lex_backend::lex_from(
            SmtVersion::V2_7,
            &Options::default(),
            size,
            input,
            ReaderEnd::End,
        ));
        assert_eq!(
            last,
            Line::LexicalError {
                error: from_slice.clone(),
                continues: None
            },
            "buffers of {size}"
        );
    }
}

#[test]
fn lexing_a_file_lexes_its_content_and_fails_to_open_with_a_zero_span() {
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("lexer-read.smt2");
    std::fs::write(&path, INPUT).expect("the test file can be written");
    let (tokens, end) = lexed_whole(INPUT);
    let (from_file, last) = outcome(lex_backend::lex_file(
        SmtVersion::V2_7,
        &Options::default(),
        &path,
    ));
    assert_eq!(from_file, tokens);
    assert_eq!(
        last,
        Line::Done {
            location: end,
            rest: None
        }
    );

    let missing = std::path::Path::new("/nonexistent/blazing-smtlib-test/missing.smt2");
    let (from_file, last) = outcome(lex_backend::lex_file(
        SmtVersion::V2_7,
        &Options::default(),
        missing,
    ));
    assert_eq!(from_file, []);
    match last {
        Line::IoError { start, end, .. } => {
            assert_eq!(start, (0, 0, 0));
            assert_eq!(end, start);
        }
        other => panic!("the file does not exist, got {other:?}"),
    }
}

// --- The Rust interface ---

/// A consumer that keeps the abstract tokens as debugged.
#[derive(Default)]
struct Tokens {
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
            if matches!(token, SmtToken::EndOfFile) {
                return Ok(ControlFlow::Break(std::mem::take(&mut self.tokens)));
            }
            self.tokens.push(format!("{token:?}"));
        }
        Ok(ControlFlow::Continue(()))
    }
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

/// Tests the Rust interface itself: the kind of the error, its location
/// and its `Display`. Calls the lexer directly.
#[test]
fn a_failure_of_the_buffered_reader_is_an_io_cause_shown_where_it_failed() {
    let err = SmtLexer::new(Tokens::default(), SmtVersion::V2_7)
        .lex_from(Failing {
            input: b"(check-sat)\n(",
        })
        .expect_err("the reader fails");
    assert!(matches!(err.kind(), SmtLexerReadErrorKind::Io(_)));
    assert_eq!(err.location(), err.span().start());
    assert!(
        err.to_string()
            .starts_with("I/O: the test reader fails after its input at line 2, column 2"),
        "{err}"
    );
}

/// Tests the Rust interface itself: the type of the error, and that its
/// location and its `Display` are those of the error of the slice. Calls
/// the lexer directly.
#[test]
fn a_lexical_error_from_a_buffered_reader_is_shown_as_the_one_of_the_slice() {
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
                err.kind(),
                SmtLexerReadErrorKind::Lexical(SmtLexicalErrorKind::MissingDelimiter)
            ),
            "{:?}",
            err.kind()
        );
        assert_eq!(err.span(), from_slice.span(), "buffers of {size}");
        assert_eq!(err.location(), from_slice.location(), "buffers of {size}");
        assert_eq!(err.to_string(), from_slice.to_string(), "buffers of {size}");
    }
}

/// Tests the Rust interface itself: the types a path may have. Calls the
/// lexer directly.
#[test]
fn a_file_is_lexed_from_a_path_of_any_of_the_usual_types() {
    let path = std::path::Path::new(env!("CARGO_TARGET_TMPDIR")).join("lexer-read-paths.smt2");
    std::fs::write(&path, INPUT).expect("the test file can be written");
    let text = path.to_str().expect("the test path is UTF-8").to_owned();
    let mut lexer = SmtLexer::new(Tokens::default(), SmtVersion::V2_7);
    for result in [
        lexer.lex_file(&path),
        lexer.lex_file(path.as_path()),
        lexer.lex_file(text.as_str()),
        lexer.lex_file(&text),
        lexer.lex_file(path.clone()),
        lexer.lex_file(text.clone()),
    ] {
        result.unwrap_or_else(|err| panic!("unexpected error {:?}", err.kind()));
    }
}

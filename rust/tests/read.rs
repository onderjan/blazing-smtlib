//! Public-API tests of the top-level reader entry points.
//!
//! They run against the reader that `parse_backend` selects: the Rust
//! library's, or the Lean port's through the Lean driver.

mod parse_backend;

use std::io::{BufRead, Read};

use parse_backend::{
    CommandParser, Location, ReadError, ReadErrorCause, Reader, ScriptParser, SyntaxChecker,
    TermParser, read_smt, read_smt_file,
};

use blazing_smtlib::{
    NonstandardCommandError,
    lexer::SmtLexicalErrorKind,
    parser::{SmtCommandOutcome, SmtSyntaxErrorKind},
    token::{SmtVersion, SmtVersionPosture},
};

/// Expected location as `(offset, line, column)`.
type Loc = (u64, u64, u64);

fn loc(location: Location) -> Loc {
    (location.offset(), location.line(), location.column())
}

fn read(input: &[u8]) -> Result<(), ReadError<NonstandardCommandError>> {
    read_smt(&mut SyntaxChecker, input)
}

#[track_caller]
fn assert_span(err: &ReadError<NonstandardCommandError>, start: Loc, end: Loc) {
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
    // the string literal starts at offset 15, zero-based line 2, column 2, and is unclosed at EOF
    let err = read(b"(check-sat)\n\n  \"abc").expect_err("expected a lexer error, got Ok");
    assert!(matches!(
        err.cause(),
        ReadErrorCause::Lexical(SmtLexicalErrorKind::UnclosedStringLiteral)
    ));
    assert_span(&err, (15, 2, 2), (19, 2, 6));
}

#[test]
fn parser_error_span_is_resolved_to_lines() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // `(assert )` is missing a term; the offending token is the `)` on line 2
    let err = read(b"(check-sat)\n(assert )").expect_err("expected a parser error, got Ok");
    assert!(matches!(
        err.cause(),
        ReadErrorCause::Syntax(SmtSyntaxErrorKind::ExpectedTerm)
    ));
    assert_span(&err, (20, 1, 8), (21, 1, 9));
}

#[test]
fn parser_error_deep_in_the_input_is_resolved_to_lines() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // the empty application `(f )` is rejected on its closing parenthesis,
    // which is the ninth byte of the third line
    let input = b"(set-logic QF_UF)\n(declare-const x Bool)\n(assert (f ))\n";
    let err = read(input).expect_err("expected a parser error, got Ok");
    assert!(matches!(
        err.cause(),
        ReadErrorCause::Syntax(SmtSyntaxErrorKind::EmptyTermApplication)
    ));
    assert_span(&err, (52, 2, 11), (53, 2, 12));
}

#[test]
fn handler_error_span_is_resolved_to_lines() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // the handler rejects the command by name, and the reported span is that
    // of the name symbol on the second line rather than of the whole command
    let err = read(b"(check-sat)\n(frobnicate 1)").expect_err("expected a handler error");
    assert!(matches!(err.cause(), ReadErrorCause::Handler(_)));
    assert_span(&err, (13, 1, 1), (23, 1, 11));
}

#[test]
fn span_after_a_token_containing_a_line_break() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // the quoted symbol carries the line break, so the offending `x` after it
    // must be reported on the second line
    let err = read(b"(assert |a\nb| x)").expect_err("expected a parser error, got Ok");
    assert!(matches!(err.cause(), ReadErrorCause::Syntax(_)));
    assert_span(&err, (14, 1, 3), (15, 1, 4));
}

#[test]
fn parser_error_at_eof_is_empty_span() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // unclosed command: the error is on the zero-width EOF token after a newline
    let err = read(b"(check-sat\n").expect_err("expected a parser error, got Ok");
    assert!(matches!(err.cause(), ReadErrorCause::Syntax(_)));
    assert_span(&err, (11, 1, 0), (11, 1, 0));
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
    let err = read_smt(&mut SyntaxChecker, reader).expect_err("expected an I/O error, got Ok");
    assert!(matches!(err.cause(), ReadErrorCause::Io(_)));
    // 13 bytes were consumed, so the location is zero-based line 1, column 1
    assert_span(&err, (13, 1, 1), (13, 1, 1));
}

#[test]
fn file_open_error_has_zero_span() {
    let path = std::path::Path::new("/nonexistent/smt-parser-test/does-not-exist.smt2");
    let err = read_smt_file(&mut SyntaxChecker, path).expect_err("expected an I/O error, got Ok");
    assert!(matches!(err.cause(), ReadErrorCause::Io(_)));
    assert_span(&err, (0, 0, 0), (0, 0, 0));
}

// --- Buffer refills: every refill size must read the same ---

/// A reader that hands out the input in a repeating pattern of read sizes,
/// so that `fill_buf` returns slices of varying lengths regardless of the
/// buffer capacity.
struct TrickleReader<'a> {
    data: &'a [u8],
    sizes: &'a [usize],
    index: usize,
}

impl Read for TrickleReader<'_> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let size = self.sizes[self.index % self.sizes.len()];
        self.index += 1;
        let n = size.min(self.data.len()).min(buf.len());
        buf[..n].copy_from_slice(&self.data[..n]);
        self.data = &self.data[n..];
        Ok(n)
    }
}

/// The outcome of a read as comparable text: `Ok`, or the error kind and span.
fn outcome_text(result: Result<(), ReadError<NonstandardCommandError>>) -> String {
    match result {
        Ok(()) => "ok".to_string(),
        Err(err) => format!(
            "{:?} at {:?}..{:?}",
            err.cause(),
            loc(err.span().start()),
            loc(err.span().end())
        ),
    }
}

const REFILL_INPUTS: &[&[u8]] = &[
    // valid script touching every token type over several lines
    b"(set-info :source |multi\nline|)\n(set-logic QF_BV)\n(declare-fun x () (_ BitVec 8))\n\
      (assert (= x #x2A))\n(assert (= ((_ extract 3 0) x) #b1010))\n(assert (! (= 1.5 1.5) :named a))\n\
      (assert (= \"a\"\"b\" \"a\"\"b\"))\n(check-sat)\n(exit)\n",
    // lexer error deep in the input, detected on a byte
    b"(set-logic QF_UF)\n(assert (= 01 x))\n",
    // lexer error at EOF
    b"(set-logic QF_UF)\n(assert |unclosed",
    // parser error deep in the input
    b"(set-logic QF_UF)\n(declare-fun f () Bool)\n(assert )\n",
    // parser error at EOF
    b"(set-logic QF_UF)\n(assert (f x)",
    // handler error on a nonstandard command
    b"(set-logic QF_UF)\n(check-sat)\n(frobnicate 1)\n",
];

#[test]
fn every_buffer_capacity_reads_the_same() {
    for input in REFILL_INPUTS {
        let expected = outcome_text(read(input));
        for capacity in (1..=70).chain([4096]) {
            let reader = std::io::BufReader::with_capacity(capacity, std::io::Cursor::new(*input));
            let actual = outcome_text(read_smt(&mut SyntaxChecker, reader));
            assert_eq!(
                actual,
                expected,
                "capacity {capacity} on {:?}",
                String::from_utf8_lossy(input)
            );
        }
    }
}

#[test]
fn every_refill_pattern_reads_the_same() {
    let patterns: &[&[usize]] = &[&[1], &[2, 1], &[3, 1, 7], &[16, 1], &[5, 64, 1, 1, 2]];
    for input in REFILL_INPUTS {
        let expected = outcome_text(read(input));
        for sizes in patterns {
            let reader = std::io::BufReader::with_capacity(
                64,
                TrickleReader {
                    data: input,
                    sizes,
                    index: 0,
                },
            );
            let actual = outcome_text(read_smt(&mut SyntaxChecker, reader));
            assert_eq!(
                actual,
                expected,
                "read sizes {sizes:?} on {:?}",
                String::from_utf8_lossy(input)
            );
        }
    }
}

#[test]
fn a_script_ends_at_the_end_of_the_input_located_after_an_exit_command() {
    // the exit command makes the reader discard the rest of the input,
    // whatever it is, without moving on: the discarding begins right after
    // the command, and the end of the input finishes the script there
    let mut handler = SyntaxChecker;
    let mut reader = Reader::script(&mut handler, SmtVersionPosture::default(), SmtVersion::V2_7);
    reader
        .read_slice(b"(check-sat) ")
        .expect("valid up to the exit command");
    assert_eq!(reader.discarded_from(), None);
    reader
        .read_slice(b"(exit) x ) ( 1 (check-sat")
        .expect("valid up to the exit command");
    assert_eq!(reader.discarded_from().map(loc), Some((18, 0, 18)));
    reader
        .read_slice(b"\n#q \"open")
        .expect("the rest of the input is discarded");
    assert_eq!(reader.discarded_from().map(loc), Some((18, 0, 18)));
    let located = reader.read_eof().expect("the script must end");
    assert_eq!(loc(located.location()), (18, 0, 18));
    assert_eq!(reader.discarded_from(), None, "the end of the input resets");

    // without the exit command, the script finishes at the end of the input
    let mut handler = SyntaxChecker;
    let mut reader = Reader::script(&mut handler, SmtVersionPosture::default(), SmtVersion::V2_7);
    reader
        .read_slice(b"(check-sat) ")
        .expect("valid up to the end of the input");
    let located = reader.read_eof().expect("the script must end");
    assert_eq!(loc(located.location()), (12, 0, 12));
}

#[test]
fn reading_after_a_finished_input_starts_a_new_one_from_the_origin() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // whether the script had the exit command or not, the reader is back at
    // its start once the input has ended: the next pieces are a new input
    // whose locations begin at the origin, as an error span shows
    type End = fn(&mut Reader<'_, SyntaxChecker, ScriptParser>);
    let by_exit: End = |reader| {
        reader
            .read_slice(b"(check-sat)\n(exit) x")
            .expect("valid up to the exit command");
        // the rest of the input is discarded, also what would be an error
        reader
            .read_slice(b"(assert )")
            .expect("the rest of the input is discarded");
        let located = reader.read_eof().expect("the input must end");
        assert_eq!(loc(located.location()), (18, 1, 6));
    };
    let by_eof: End = |reader| {
        reader
            .read_slice(b"(check-sat)\n")
            .expect("valid up to the end of the input");
        let located = reader.read_eof().expect("the input must end");
        assert_eq!(loc(located.location()), (12, 1, 0));
    };
    for end in [by_exit, by_eof] {
        let mut handler = SyntaxChecker;
        let mut reader =
            Reader::script(&mut handler, SmtVersionPosture::default(), SmtVersion::V2_7);
        end(&mut reader);
        reader
            .read_slice(b"(check-sat)\n")
            .expect("valid up to the missing term");
        let err = reader
            .read_slice(b"(assert )")
            .expect_err("a missing term is a parser error");
        assert!(matches!(
            err.cause(),
            ReadErrorCause::Syntax(SmtSyntaxErrorKind::ExpectedTerm)
        ));
        assert_span(&err, (20, 1, 8), (21, 1, 9));
    }
}

/// A buffered reader over pieces of input that arrive one at a time.
///
/// It panics when it is asked for the same input again without any of it
/// consumed, so that a reading loop that makes no progress fails rather than
/// running forever, and, unless the stream has ended, when it is asked for
/// more input than it has, where an interactive stream would block.
struct Pieces<'a> {
    pieces: Vec<&'a [u8]>,
    /// Whether the input ends after the pieces.
    ended: bool,
    /// The piece being read and how much of it has been consumed.
    index: usize,
    consumed: usize,
    /// Whether the input was given out and nothing of it consumed since.
    given: bool,
}

impl<'a> Pieces<'a> {
    fn new(pieces: Vec<&'a [u8]>, ended: bool) -> Self {
        Pieces {
            pieces,
            ended,
            index: 0,
            consumed: 0,
            given: false,
        }
    }

    /// The input not consumed yet.
    fn rest(&self) -> Vec<u8> {
        let mut rest = Vec::new();
        for (index, piece) in self.pieces.iter().enumerate().skip(self.index) {
            let from = if index == self.index {
                self.consumed
            } else {
                0
            };
            rest.extend_from_slice(&piece[from..]);
        }
        rest
    }
}

impl Read for Pieces<'_> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let available = self.fill_buf()?;
        let len = buf.len().min(available.len());
        buf[..len].copy_from_slice(&available[..len]);
        self.consume(len);
        Ok(len)
    }
}

impl BufRead for Pieces<'_> {
    fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
        assert!(
            !self.given,
            "the same input was asked for again without any of it consumed"
        );
        match self.pieces.get(self.index) {
            Some(piece) => {
                self.given = true;
                Ok(&piece[self.consumed..])
            }
            None => {
                assert!(self.ended, "the reader must not wait for more input");
                Ok(&[])
            }
        }
    }

    fn consume(&mut self, amount: usize) {
        if amount == 0 {
            return;
        }
        self.given = false;
        self.consumed += amount;
        if self.consumed == self.pieces[self.index].len() {
            self.index += 1;
            self.consumed = 0;
        }
    }
}

#[test]
fn read_all_leaves_the_rest_after_an_exit_command_unread() {
    // whatever the pieces the input arrives in, the buffered reader is left
    // right after the exit command, with the rest of the input still to be
    // read
    let input: &[u8] = b"(check-sat)\n(exit)\n(get-model)";
    for size in 1..=input.len() {
        let mut stream = Pieces::new(input.chunks(size).collect(), true);
        let mut handler = SyntaxChecker;
        let mut reader =
            Reader::script(&mut handler, SmtVersionPosture::default(), SmtVersion::V2_7);
        reader
            .read_all(&mut stream)
            .unwrap_or_else(|err| panic!("pieces of {size}: {err:?}"));
        assert_eq!(stream.rest(), b"\n(get-model)", "pieces of {size}");
    }

    // without it, the whole input is read
    let mut stream = Pieces::new(vec![b"(check-sat)\n"], true);
    let mut handler = SyntaxChecker;
    let mut reader = Reader::script(&mut handler, SmtVersionPosture::default(), SmtVersion::V2_7);
    reader.read_all(&mut stream).expect("valid input");
    assert!(stream.rest().is_empty(), "the whole input is read");
}

#[test]
fn read_smt_leaves_the_rest_after_an_exit_command_unread() {
    // a buffered reader lent to `read_smt` is left as `read_all` leaves it:
    // right after the exit command, with the rest of the input still to be
    // read
    let input: &[u8] = b"(check-sat)\n(exit)\n(get-model)";
    for size in 1..=input.len() {
        let mut stream = Pieces::new(input.chunks(size).collect(), true);
        read_smt(&mut SyntaxChecker, &mut stream)
            .unwrap_or_else(|err| panic!("pieces of {size}: {err:?}"));
        assert_eq!(stream.rest(), b"\n(get-model)", "pieces of {size}");
    }
}

#[test]
fn read_all_returns_after_an_exit_command_without_waiting_for_more_input() {
    // an interactive stream has not ended after the exit command, but the
    // script has: the reader returns without asking for more input
    let mut stream = Pieces::new(vec![b"(check-sat)\n", b"(exit)\n"], false);
    let mut handler = SyntaxChecker;
    let mut reader = Reader::script(&mut handler, SmtVersionPosture::default(), SmtVersion::V2_7);
    reader.read_all(&mut stream).expect("valid input");
    assert_eq!(
        stream.rest(),
        b"\n",
        "the stream is left right after the exit command"
    );
}

#[test]
fn one_reader_reads_several_inputs_in_turn_each_from_the_origin() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // after a whole input, however it ended, the reader serves the next one
    // with fresh locations, as an error span in the last input shows
    let mut handler = SyntaxChecker;
    let mut reader = Reader::script(&mut handler, SmtVersionPosture::default(), SmtVersion::V2_7);
    let inputs: [&[u8]; 3] = [
        b"(set-logic QF_UF)\n(check-sat)\n(exit)\n",
        b"(check-sat)\n",
        b"(check-sat)\n(assert )",
    ];
    for input in &inputs[..2] {
        reader
            .read_all(Pieces::new(vec![input], true))
            .expect("valid input");
    }
    let err = reader
        .read_all(Pieces::new(vec![inputs[2]], true))
        .expect_err("a missing term is a parser error");
    assert_span(&err, (20, 1, 8), (21, 1, 9));

    // scripts ended by the exit command can follow each other in one stream:
    // each is read from where the one before it left the stream
    let mut handler = SyntaxChecker;
    let mut reader = Reader::script(&mut handler, SmtVersionPosture::default(), SmtVersion::V2_7);
    let mut stream = Pieces::new(
        vec![b"(check-sat)\n(exit)(check-sat)\n(exit)\n(assert )"],
        true,
    );
    reader.read_all(&mut stream).expect("valid input");
    reader.read_all(&mut stream).expect("valid input");
    let err = reader
        .read_all(&mut stream)
        .expect_err("a missing term is a parser error");
    assert_span(&err, (9, 1, 8), (10, 1, 9));
}

#[test]
fn a_reader_over_another_top_level_parser_finishes_where_that_parser_does() {
    // a term parser as the top-level parser: the reader finishes after one
    // term with that parser's result, the layout after it is allowed, and
    // the end of the input returns the location after the term
    let mut handler = SyntaxChecker;
    let mut reader = Reader::new(&mut handler, TermParser, SmtVersion::V2_7);
    reader
        .read_slice(b"(f a b) ; done\n")
        .expect("valid up to the term");
    let located = reader.read_eof().expect("the term finishes the reader");
    assert_eq!(loc(located.location()), (7, 0, 7));

    // a token after the term is a trailing token, also when read whole
    let mut handler = SyntaxChecker;
    let mut reader = Reader::new(&mut handler, TermParser, SmtVersion::V2_7);
    let err = reader
        .read_all(&b"(f a b) ) ("[..])
        .expect_err("a token after the term is an error");
    assert!(matches!(
        err.cause(),
        ReadErrorCause::Lexical(SmtLexicalErrorKind::UnexpectedTrailingToken)
    ));
    assert_span(&err, (8, 0, 8), (9, 0, 9));

    // a term cut off by the end of the input is that parser's error
    let mut handler = SyntaxChecker;
    let mut reader = Reader::new(&mut handler, TermParser, SmtVersion::V2_7);
    reader
        .read_slice(b"(f a ")
        .expect("valid up to the end of the input");
    assert!(reader.read_eof().is_err());
}

#[test]
fn a_reader_over_a_command_parser_reads_one_command_per_input() {
    // every command finishes the reader, and the end of the input returns
    // the location after it; an input with no command in it finishes the
    // reader at its end
    let mut handler = SyntaxChecker;
    let mut reader = Reader::new(&mut handler, CommandParser, SmtVersion::V2_7);
    let mut stops = Vec::new();
    for input in [
        &b"(set-logic QF_UF)\n"[..],
        b" (check-sat)",
        b"(exit)",
        b"\n",
    ] {
        reader.read_slice(input).expect("valid input");
        let located = reader.read_eof().expect("valid input");
        stops.push((*located.value(), loc(located.location())));
    }
    assert_eq!(
        stops,
        [
            (SmtCommandOutcome::Command, (17, 0, 17)),
            (SmtCommandOutcome::Command, (12, 0, 12)),
            (SmtCommandOutcome::Exit, (6, 0, 6)),
            (SmtCommandOutcome::EndOfFile, (1, 1, 0)),
        ]
    );

    // inside a command, the end of the input is a syntax error
    reader
        .read_slice(b"(check-sat")
        .expect("valid up to the end of the input");
    assert!(reader.read_eof().is_err());

    // a second command in the same input is a trailing token
    let mut handler = SyntaxChecker;
    let mut reader = Reader::new(&mut handler, CommandParser, SmtVersion::V2_7);
    let err = reader
        .read_slice(b"(check-sat)\n(exit)")
        .expect_err("a second command is an error");
    assert!(matches!(
        err.cause(),
        ReadErrorCause::Lexical(SmtLexicalErrorKind::UnexpectedTrailingToken)
    ));
    assert_span(&err, (12, 1, 0), (13, 1, 1));
}

#[test]
fn read_all_after_an_exit_command_reads_nothing_more() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // the exit command has made the reader discard inside a piece; reading
    // the rest of the input as a whole then reads nothing of it and ends the
    // script
    let mut handler = SyntaxChecker;
    let mut reader = Reader::script(&mut handler, SmtVersionPosture::default(), SmtVersion::V2_7);
    reader
        .read_slice(b"(check-sat)\n(exit) (assert")
        .expect("valid up to the exit command");
    let mut rest = Pieces::new(vec![b" ) #q\n(check-sat)"], true);
    reader.read_all(&mut rest).expect("the script must end");
    assert_eq!(rest.rest(), b" ) #q\n(check-sat)", "nothing more is read");

    // the next input is read from the origin
    let err = reader
        .read_slice(b"(assert )")
        .expect_err("a missing term is a parser error");
    assert_span(&err, (8, 0, 8), (9, 0, 9));
}

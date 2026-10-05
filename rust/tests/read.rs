//! Public-API tests of the top-level reader entry points.

use std::io::{BufRead, Read};

use std::ops::ControlFlow;

use blazing_smtlib::{
    NonstandardCommandError, SmtLocation, SmtSyntaxChecker,
    lexer::SmtLexicalErrorKind,
    parser::{
        SmtCommandOutcome, SmtCommandParser, SmtScriptEnd, SmtSyntaxErrorKind, SmtTermParser,
    },
    reader::{SmtReadError, SmtReadErrorCause, SmtReader, read_smt, read_smt_file},
    token::{SmtVersion, SmtVersionPosture},
};

/// Expected location as `(offset, line, column)`.
type Loc = (u64, u64, u64);

fn loc(location: SmtLocation) -> Loc {
    (location.offset(), location.line(), location.column())
}

fn read(input: &[u8]) -> Result<(), SmtReadError<NonstandardCommandError>> {
    read_smt(&mut SmtSyntaxChecker, input)
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
    // the string literal starts at offset 15, zero-based line 2, column 2, and is unclosed at EOF
    let err = read(b"(check-sat)\n\n  \"abc").expect_err("expected a lexer error, got Ok");
    assert!(matches!(
        err.cause(),
        SmtReadErrorCause::Lexical(SmtLexicalErrorKind::UnclosedStringLiteral)
    ));
    assert_span(&err, (15, 2, 2), (19, 2, 6));
}

#[test]
fn parser_error_span_is_resolved_to_lines() {
    // `(assert )` is missing a term; the offending token is the `)` on line 2
    let err = read(b"(check-sat)\n(assert )").expect_err("expected a parser error, got Ok");
    assert!(matches!(
        err.cause(),
        SmtReadErrorCause::Syntax(SmtSyntaxErrorKind::ExpectedTerm)
    ));
    assert_span(&err, (20, 1, 8), (21, 1, 9));
}

#[test]
fn parser_error_deep_in_the_input_is_resolved_to_lines() {
    // the empty application `(f )` is rejected on its closing parenthesis,
    // which is the ninth byte of the third line
    let input = b"(set-logic QF_UF)\n(declare-const x Bool)\n(assert (f ))\n";
    let err = read(input).expect_err("expected a parser error, got Ok");
    assert!(matches!(
        err.cause(),
        SmtReadErrorCause::Syntax(SmtSyntaxErrorKind::EmptyTermApplication)
    ));
    assert_span(&err, (52, 2, 11), (53, 2, 12));
}

#[test]
fn handler_error_span_is_resolved_to_lines() {
    // the handler rejects the command by name, and the reported span is that
    // of the name symbol on the second line rather than of the whole command
    let err = read(b"(check-sat)\n(frobnicate 1)").expect_err("expected a handler error");
    assert!(matches!(err.cause(), SmtReadErrorCause::Handler(_)));
    assert_span(&err, (13, 1, 1), (23, 1, 11));
}

#[test]
fn span_after_a_token_containing_a_line_break() {
    // the quoted symbol carries the line break, so the offending `x` after it
    // must be reported on the second line
    let err = read(b"(assert |a\nb| x)").expect_err("expected a parser error, got Ok");
    assert!(matches!(err.cause(), SmtReadErrorCause::Syntax(_)));
    assert_span(&err, (14, 1, 3), (15, 1, 4));
}

#[test]
fn parser_error_at_eof_is_empty_span() {
    // unclosed command: the error is on the zero-width EOF token after a newline
    let err = read(b"(check-sat\n").expect_err("expected a parser error, got Ok");
    assert!(matches!(err.cause(), SmtReadErrorCause::Syntax(_)));
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
    let err = read_smt(&mut SmtSyntaxChecker, reader).expect_err("expected an I/O error, got Ok");
    assert!(matches!(err.cause(), SmtReadErrorCause::Io(_)));
    // 13 bytes were consumed, so the location is zero-based line 1, column 1
    assert_span(&err, (13, 1, 1), (13, 1, 1));
}

#[test]
fn file_open_error_has_zero_span() {
    let path = std::path::Path::new("/nonexistent/smt-parser-test/does-not-exist.smt2");
    let err =
        read_smt_file(&mut SmtSyntaxChecker, path).expect_err("expected an I/O error, got Ok");
    assert!(matches!(err.cause(), SmtReadErrorCause::Io(_)));
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
fn outcome_text(result: Result<(), SmtReadError<NonstandardCommandError>>) -> String {
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
            let actual = outcome_text(read_smt(&mut SmtSyntaxChecker, reader));
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
            let actual = outcome_text(read_smt(&mut SmtSyntaxChecker, reader));
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
fn read_slice_reports_an_exit_command_and_read_eof_the_end_of_the_input() {
    // a piece that runs out before any exit command asks for more; a piece
    // with the exit command finishes the reader there, whatever follows in
    // the piece, with the location after the command
    let mut handler = SmtSyntaxChecker;
    let mut reader =
        SmtReader::script(&mut handler, SmtVersion::V2_7, SmtVersionPosture::default());
    assert!(matches!(
        reader.read_slice(b"(check-sat) "),
        Ok(ControlFlow::Continue(()))
    ));
    let located = reader
        .read_slice(b"(exit) x ) ( 1 (check-sat")
        .expect("valid up to the exit command")
        .break_value()
        .expect("the exit command finishes the reader");
    assert_eq!(*located.value(), SmtScriptEnd::Exit);
    assert_eq!(loc(located.location()), (18, 0, 18));

    // the end of the input between commands finishes the reader as well,
    // at the end of the input
    let mut handler = SmtSyntaxChecker;
    let mut reader =
        SmtReader::script(&mut handler, SmtVersion::V2_7, SmtVersionPosture::default());
    assert!(matches!(
        reader.read_slice(b"(check-sat) "),
        Ok(ControlFlow::Continue(()))
    ));
    let located = reader
        .read_eof()
        .expect("valid up to the end of the input")
        .break_value()
        .expect("the end of the input finishes the reader");
    assert_eq!(*located.value(), SmtScriptEnd::EndOfFile);
    assert_eq!(loc(located.location()), (12, 0, 12));
}

#[test]
fn reading_after_a_finished_input_starts_a_new_one_from_the_origin() {
    // whether the parser finished by the exit command or by the end of the
    // input, the reader is back at its start once the input has ended: the
    // next pieces are a new input whose locations begin at the origin, as an
    // error span shows
    type End = fn(&mut SmtReader<'_, SmtSyntaxChecker>);
    let by_exit: End = |reader| {
        assert!(matches!(
            reader.read_slice(b"(check-sat)\n(exit) x"),
            Ok(ControlFlow::Break(_))
        ));
        // the rest of the input is disregarded, also what would be an error
        assert!(matches!(
            reader.read_slice(b"(assert )"),
            Ok(ControlFlow::Continue(()))
        ));
        // until the end of the input, which hands nothing more to the parser
        assert!(matches!(reader.read_eof(), Ok(ControlFlow::Continue(()))));
    };
    let by_eof: End = |reader| {
        assert!(matches!(
            reader.read_slice(b"(check-sat)\n"),
            Ok(ControlFlow::Continue(()))
        ));
        assert!(matches!(reader.read_eof(), Ok(ControlFlow::Break(_))));
    };
    for end in [by_exit, by_eof] {
        let mut handler = SmtSyntaxChecker;
        let mut reader =
            SmtReader::script(&mut handler, SmtVersion::V2_7, SmtVersionPosture::default());
        end(&mut reader);
        assert!(matches!(
            reader.read_slice(b"(check-sat)\n"),
            Ok(ControlFlow::Continue(()))
        ));
        let err = reader
            .read_slice(b"(assert )")
            .expect_err("a missing term is a parser error");
        assert!(matches!(
            err.cause(),
            SmtReadErrorCause::Syntax(SmtSyntaxErrorKind::ExpectedTerm)
        ));
        assert_span(&err, (20, 1, 8), (21, 1, 9));
    }
}

#[test]
fn read_all_tells_an_exit_command_from_the_end_of_the_input() {
    // with the exit command, the result says so and the buffered reader is
    // left positioned after the command, whatever the buffer capacity: the
    // rest of the input is still there to be read
    let input: &[u8] = b"(check-sat)\n(exit)\n(get-model)";
    for capacity in (1..=24).chain([4096]) {
        let mut buf_reader =
            std::io::BufReader::with_capacity(capacity, std::io::Cursor::new(input));
        let mut handler = SmtSyntaxChecker;
        let mut reader =
            SmtReader::script(&mut handler, SmtVersion::V2_7, SmtVersionPosture::default());
        assert_eq!(
            reader.read_all(&mut buf_reader).expect("valid input"),
            Some(SmtScriptEnd::Exit),
            "capacity {capacity}"
        );
        let mut rest = Vec::new();
        buf_reader
            .read_to_end(&mut rest)
            .expect("reading the rest of the input");
        assert_eq!(rest, b"\n(get-model)", "capacity {capacity}");
    }

    // without it, the end of the input ends the script
    let mut handler = SmtSyntaxChecker;
    let mut reader =
        SmtReader::script(&mut handler, SmtVersion::V2_7, SmtVersionPosture::default());
    assert_eq!(
        reader.read_all(&b"(check-sat)\n"[..]).expect("valid input"),
        Some(SmtScriptEnd::EndOfFile)
    );
}

#[test]
fn one_reader_reads_several_inputs_in_turn_each_from_the_origin() {
    // after a whole input, however it ended, the reader serves the next one
    // with fresh locations, as an error span in the last input shows
    let mut handler = SmtSyntaxChecker;
    let mut reader =
        SmtReader::script(&mut handler, SmtVersion::V2_7, SmtVersionPosture::default());
    assert_eq!(
        reader
            .read_all(&b"(set-logic QF_UF)\n(check-sat)\n(exit)\n"[..])
            .expect("valid input"),
        Some(SmtScriptEnd::Exit)
    );
    assert_eq!(
        reader.read_all(&b"(check-sat)\n"[..]).expect("valid input"),
        Some(SmtScriptEnd::EndOfFile)
    );
    let err = reader
        .read_all(&b"(check-sat)\n(assert )"[..])
        .expect_err("a missing term is a parser error");
    assert_span(&err, (20, 1, 8), (21, 1, 9));
}

#[test]
fn a_reader_over_another_top_level_parser_finishes_where_that_parser_does() {
    // a term parser as the top-level parser: the reader finishes after one
    // term with that parser's result, whatever follows in the piece, and
    // reports the location after the term
    let mut handler = SmtSyntaxChecker;
    let mut reader = SmtReader::with_parser(&mut handler, SmtTermParser::new(), SmtVersion::V2_7);
    let located = reader
        .read_slice(b"(f a b) (check-sat)")
        .expect("valid up to the term")
        .break_value()
        .expect("the term finishes the reader");
    assert_eq!(loc(located.location()), (7, 0, 7));

    // reading the whole input stops there as well, without an error for the rest
    let mut handler = SmtSyntaxChecker;
    let mut reader = SmtReader::with_parser(&mut handler, SmtTermParser::new(), SmtVersion::V2_7);
    assert!(matches!(reader.read_all(&b"(f a b) ) ("[..]), Ok(Some(()))));

    // a term cut off by the end of the input is that parser's error
    let mut handler = SmtSyntaxChecker;
    let mut reader = SmtReader::with_parser(&mut handler, SmtTermParser::new(), SmtVersion::V2_7);
    assert!(matches!(
        reader.read_slice(b"(f a "),
        Ok(ControlFlow::Continue(()))
    ));
    assert!(reader.read_eof().is_err());
}

#[test]
fn a_reader_over_a_command_parser_reads_one_command_per_break() {
    // every command finishes the reader with the location after it, and the
    // reader disregards what it is fed until the input ends; ending it there
    // makes the rest of the piece a new input, fed from that location, so
    // each command's location counts from the end of the previous one
    let mut handler = SmtSyntaxChecker;
    let mut reader =
        SmtReader::with_parser(&mut handler, SmtCommandParser::new(), SmtVersion::V2_7);
    let mut rest: &[u8] = b"(set-logic QF_UF)\n(check-sat)\n(exit)\n";
    let mut stops = Vec::new();
    loop {
        match reader.read_slice(rest).expect("valid input") {
            ControlFlow::Continue(()) => break,
            ControlFlow::Break(located) => {
                stops.push((*located.value(), loc(located.location())));
                rest = &rest[located.location().offset() as usize..];
                assert!(matches!(reader.read_eof(), Ok(ControlFlow::Continue(()))));
            }
        }
    }
    assert_eq!(
        stops,
        [
            (SmtCommandOutcome::Command, (17, 0, 17)),
            (SmtCommandOutcome::Command, (12, 1, 11)),
            (SmtCommandOutcome::Exit, (7, 1, 6)),
        ]
    );
    assert_eq!(rest, b"\n");

    // the end of the input before a command finishes the reader too;
    // inside a command it is a syntax error
    let located = reader
        .read_eof()
        .expect("valid up to the end of the input")
        .break_value()
        .expect("the end of the input finishes the reader");
    assert_eq!(*located.value(), SmtCommandOutcome::EndOfFile);
    assert_eq!(loc(located.location()), (1, 1, 0));
    assert!(matches!(
        reader.read_slice(b"(check-sat"),
        Ok(ControlFlow::Continue(()))
    ));
    assert!(reader.read_eof().is_err());
}

/// A buffered reader over bytes that panics when it is asked for its buffer
/// too many times, so that a reading loop that consumes nothing shows as a
/// failure and not as a test that never ends.
struct Bounded<'a> {
    rest: &'a [u8],
    fills: usize,
}

impl Read for Bounded<'_> {
    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
        let len = buf.len().min(self.rest.len());
        buf[..len].copy_from_slice(&self.rest[..len]);
        self.rest = &self.rest[len..];
        Ok(len)
    }
}

impl BufRead for Bounded<'_> {
    fn fill_buf(&mut self) -> std::io::Result<&[u8]> {
        self.fills += 1;
        assert!(
            self.fills <= 16,
            "the buffer was asked for again and again without being consumed"
        );
        Ok(self.rest)
    }

    fn consume(&mut self, amount: usize) {
        self.rest = &self.rest[amount..];
    }
}

#[test]
fn the_rest_of_a_finished_input_can_be_read_to_its_end() {
    // the exit command finishes the reader inside a piece; the rest of the
    // input is discarded, also when it is read to its end as a whole: it is
    // consumed without being parsed, and the input ends
    let mut handler = SmtSyntaxChecker;
    let mut reader =
        SmtReader::script(&mut handler, SmtVersion::V2_7, SmtVersionPosture::default());
    assert!(matches!(
        reader.read_slice(b"(check-sat)\n(exit) (assert"),
        Ok(ControlFlow::Break(_))
    ));
    let mut rest = Bounded {
        rest: b" ) #q\n(check-sat)",
        fills: 0,
    };
    assert!(matches!(reader.read_all(&mut rest), Ok(None)));
    assert!(rest.rest.is_empty(), "the rest was consumed");

    // the next input is read from the origin
    let err = reader
        .read_slice(b"(assert )")
        .expect_err("a missing term is a parser error");
    assert_span(&err, (8, 0, 8), (9, 0, 9));
}

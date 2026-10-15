//! Tests of the batch contract between the lexer and its token consumer:
//! how tokens are grouped into `consume` calls, and what a consumer's
//! stop does to lexing.
//!
//! Tokens borrowing the current slice are batched and handed over when the
//! batch is full, at the end of the slice, and before an error is returned.
//! A token that began in an earlier slice and the end-of-file token are
//! handed over alone.
//!
//! Every hand-over has at least one token, and the consumer must consume at
//! least one before it returns, whatever it returns. The tokens a consumer
//! leaves are handed over again before any new ones, in a hand-over that
//! starts with nothing consumed, so the tokens a consumer takes are the same
//! in every stopping pattern, spans included. A version the consumer sets
//! applies from the end of the last consumed token, also to what the lexer
//! had lexed ahead. A consumer that finishes ends lexing after the tokens it
//! took: that location is returned with the result, and the lexer discards
//! what it is fed until the end of the input.
//!
//! The runs with a plan go through the lexing backend of the tests, so they
//! check the Lean port when its driver is selected. The tests that build a
//! lexer themselves use the Rust interface and test the Rust lexer only.
//!
//! Every test that sends a plan through the backend depends on where the
//! hand-overs are cut. It first asks `boundaries_not_applicable` and ends
//! there, reported as not applicable, when the Lean lexer under test cuts
//! them elsewhere by design.

mod lex_backend;

use blazing_smtlib::lexer::SmtLexicalExpected;
use std::cell::RefCell;
use std::ops::ControlFlow;
use std::panic::{AssertUnwindSafe, catch_unwind};

use blazing_smtlib::{
    SmtLocated, SmtLocation,
    lexer::{SmtLexError, SmtLexErrorCause, SmtLexer, SmtLexicalErrorKind},
    token::{
        SmtBatchCursor, SmtConsume, SmtConsumeFrom, SmtCursor, SmtLookahead, SmtToken,
        SmtTokenCategory, SmtVersion,
    },
};

use lex_backend::{Feed, Line, Loc, Options, driver};

/// The batch capacity the lexer is expected to use.
///
/// The capacity is not part of the public API; it is pinned here so that a
/// change is noticed and the expectations below are updated with it.
const BATCH_CAPACITY: usize = 256;

/// The two ends of the span of a recorded token.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RecordedSpan {
    start: Loc,
    end: Loc,
}

/// An owned copy of a handed-over token.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Recorded {
    ty: SmtTokenCategory,
    content: Vec<u8>,
    span: RecordedSpan,
}

fn record(token: SmtToken) -> Recorded {
    Recorded {
        ty: token.category(),
        content: token.content().to_vec(),
        span: RecordedSpan {
            start: loc(token.span().start()),
            end: loc(token.span().end()),
        },
    }
}

/// The slices of one input, fed to the lexer in turn.
type Chunks = &'static [&'static [u8]];

fn loc(location: SmtLocation) -> Loc {
    (location.offset(), location.line(), location.column())
}

/// What the consumer replies to one `consume` call.
#[derive(Debug, Clone, Copy)]
enum Reply {
    /// Take every token and continue.
    TakeAll,
    /// Take `consumed` tokens (at most the batch length) and continue: the
    /// lexer hands the tokens left over again.
    Leave { consumed: usize },
    /// Take `consumed` tokens (at most the batch length) and fail.
    Fail { consumed: usize },
    /// Take `consumed` tokens and finish.
    Finish { consumed: usize },
    /// Take `consumed` tokens, set the version, and continue.
    Switch {
        consumed: usize,
        version: SmtVersion,
    },
    /// Take `consumed` tokens, set the version, and finish.
    SwitchAndFinish {
        consumed: usize,
        version: SmtVersion,
    },
}

impl Reply {
    /// How many of `len` tokens the reply takes.
    fn takes(self, len: usize) -> usize {
        match self {
            Reply::TakeAll => len,
            Reply::Leave { consumed }
            | Reply::Fail { consumed }
            | Reply::Finish { consumed }
            | Reply::Switch { consumed, .. }
            | Reply::SwitchAndFinish { consumed, .. } => consumed.min(len),
        }
    }
}

/// A consumer that records every hand-over and replies according to a plan.
///
/// The plan gives the reply of each call by index; calls past the plan's end
/// take every token. The records live outside the consumer, so that they can
/// be read after the lexer, which owns the consumer, is gone.
struct Recorder<'r> {
    calls: &'r mut Vec<Vec<Recorded>>,
    versions: &'r mut Vec<SmtVersion>,
    plan: &'r [Reply],
}

impl SmtConsume for Recorder<'_> {
    /// Whether the consumer finished by the plan, rather than only because
    /// it was handed the end of the input, where every consumer breaks at
    /// the latest.
    type Result = bool;
    type Error = ();
    const IS_CONCRETE: bool = false;
}

impl<'a> SmtConsumeFrom<SmtBatchCursor<'a>> for Recorder<'_> {
    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'a>,
    ) -> Result<ControlFlow<Self::Result>, ()> {
        // the end-of-file token is handed over alone
        let at_end = cursor
            .peek()
            .is_some_and(|token| token.category() == SmtTokenCategory::EndOfFile);
        match self.reply(cursor)? {
            ControlFlow::Continue(()) if at_end => Ok(ControlFlow::Break(false)),
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(()) => Ok(ControlFlow::Break(true)),
        }
    }
}

impl Recorder<'_> {
    /// Records the hand-over, takes its tokens as the plan says, and answers
    /// as it says.
    fn reply(&mut self, cursor: &mut SmtBatchCursor<'_>) -> Result<ControlFlow<()>, ()> {
        // Record every token of the hand-over, also those the reply will not
        // take. A consumer has no way to look at tokens without consuming
        // them, so the recording goes through an attempt that takes every
        // token and then fails, which consumes nothing, and carries the
        // tokens out of the extractor in a cell.
        let seen = RefCell::new(Vec::new());
        let failed: Option<()> = cursor.attempt(|window| {
            while let Some(token) = window.next() {
                seen.borrow_mut().push(record(token));
            }
            None
        });
        assert!(failed.is_none());
        let tokens = seen.into_inner();
        let len = tokens.len();
        assert_ne!(len, 0, "every hand-over has at least one token");
        let index = self.calls.len();
        let reply = self.plan.get(index).copied().unwrap_or(Reply::TakeAll);
        let taken = reply.takes(len);
        for _ in 0..taken {
            cursor.next();
        }
        self.calls.push(tokens);
        self.versions.push(cursor.version());
        match reply {
            Reply::TakeAll | Reply::Leave { .. } => Ok(ControlFlow::Continue(())),
            Reply::Fail { .. } => Err(()),
            Reply::Finish { .. } => Ok(ControlFlow::Break(())),
            Reply::Switch { version, .. } => {
                cursor
                    .set_version(version)
                    .expect("lexer should switch version");
                Ok(ControlFlow::Continue(()))
            }
            Reply::SwitchAndFinish { version, .. } => {
                cursor
                    .set_version(version)
                    .expect("lexer should switch version");
                Ok(ControlFlow::Break(()))
            }
        }
    }
}

/// Why a run ended in an error.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RunError {
    Lexical(SmtLexicalErrorKind),
    Consumer,
}

/// The start and end of an error span, each as `(offset, line, column)`.
type ErrorSpan = ((u64, u64, u64), (u64, u64, u64));

/// Everything observable about one lexer run.
#[derive(Debug, PartialEq, Eq)]
struct Run {
    /// The tokens of every hand-over, in order.
    calls: Vec<Vec<Recorded>>,
    /// The version of the cursor at the start of every hand-over.
    versions: Vec<SmtVersion>,
    /// The error that ended the run, if any.
    error: Option<RunError>,
    /// The span of the error, if it was a lexical one.
    error_span: Option<ErrorSpan>,
    /// The location returned with the result if the consumer finished.
    finished_at: Option<(u64, u64, u64)>,
}

impl Run {
    /// The lengths of the hand-overs.
    fn sizes(&self) -> Vec<usize> {
        self.calls.iter().map(Vec::len).collect()
    }

    /// The tokens of every hand-over, concatenated.
    fn all(&self) -> Vec<Recorded> {
        self.calls.concat()
    }

    /// The tokens the consumer took under the plan: for each hand-over, the
    /// prefix the reply consumed.
    fn taken(&self, plan: &[Reply]) -> Vec<Recorded> {
        self.calls
            .iter()
            .enumerate()
            .flat_map(|(index, tokens)| {
                let reply = plan.get(index).copied().unwrap_or(Reply::TakeAll);
                tokens[..reply.takes(tokens.len())].iter().cloned()
            })
            .collect()
    }
}

/// Whether a call returned the break that the consumer makes at the end of
/// the input, as every consumer must, rather than a finish by the plan.
fn breaks_at_end(result: &Result<SmtLocated<bool>, SmtLexError<()>>) -> bool {
    matches!(result, Ok(located) if !*located.value())
}

/// The location of a finish by the plan, which the end of the input returns.
#[track_caller]
fn finished_at(result: Result<SmtLocated<bool>, SmtLexError<()>>) -> (u64, u64, u64) {
    match result {
        Ok(located) if *located.value() => loc(located.location()),
        other => panic!("expected a finish by the plan, got {other:?}"),
    }
}

/// The lexer is at the origin, as it must be after the end of the input.
#[track_caller]
fn assert_at_origin<C: SmtConsume>(lexer: &SmtLexer<C>) {
    assert_eq!(
        loc(lexer.current_location()),
        (0, 0, 0),
        "the lexer must be reset to the origin"
    );
}

/// What made the call fail, and the span of a lexical error. The lexer of
/// these runs stops at its first error, so no error may say that the input
/// continues.
type Failed = (RunError, Option<ErrorSpan>);

fn into_cause(err: SmtLexError<()>) -> Failed {
    assert_eq!(
        err.continues_from(),
        None,
        "a lexer that stops at its first error does not continue the input"
    );
    let span = (loc(err.span().start()), loc(err.span().end()));
    match err.into_cause() {
        SmtLexErrorCause::Lexical(kind) => (RunError::Lexical(kind), Some(span)),
        SmtLexErrorCause::Consumer(()) => (RunError::Consumer, None),
    }
}

/// Lexes the chunks, then end of file, from the given version, with the
/// consumer replying by the plan.
///
/// After every successfully lexed chunk, the lexer's location is checked
/// against the location computed independently from the bytes, which a
/// rewind must restore correctly. After the end of the input, the lexer must
/// be back at the origin.
#[track_caller]
fn run_direct_from(version: SmtVersion, chunks: &[&[u8]], plan: &[Reply]) -> Run {
    let mut calls = Vec::new();
    let mut versions = Vec::new();
    let mut error = None;
    let mut error_span = None;
    let mut finished_at = None;
    {
        let mut lexer = SmtLexer::new(
            Recorder {
                calls: &mut calls,
                versions: &mut versions,
                plan,
            },
            version,
        );
        let mut expected = SmtLocation::initial();
        for chunk in chunks {
            if let Err(err) = lexer.lex_slice(chunk) {
                let (cause, span) = into_cause(err);
                error = Some(cause);
                error_span = span;
                break;
            }
            // whatever the consumer did, the lexer is after everything it was fed
            expected = chunk
                .iter()
                .fold(expected, |location, &c| location.after_byte(c));
            assert_eq!(
                loc(lexer.current_location()),
                loc(expected),
                "location after the chunk {:?} under the plan {plan:?}",
                String::from_utf8_lossy(chunk)
            );
        }
        if error.is_none() {
            match lexer.lex_eof() {
                Ok(located) => {
                    // the break that every consumer makes at the end of the
                    // input is not a finish by the plan
                    if *located.value() {
                        finished_at = Some(loc(located.location()));
                    }
                    assert_at_origin(&lexer);
                }
                Err(err) => {
                    let (cause, span) = into_cause(err);
                    error = Some(cause);
                    error_span = span;
                }
            }
        }
    }
    Run {
        calls,
        versions,
        error,
        error_span,
        finished_at,
    }
}

/// Lexes the chunks, then end of file, from the given version, with the
/// consumer replying by the plan, through the lexing backend of the tests:
/// the Lean driver if it is selected, the Rust lexer otherwise.
///
/// The Rust lexer is also run directly with a consumer of this file, which
/// checks the cursor as it goes, and the two runs must be the same.
#[track_caller]
fn run_from(version: SmtVersion, chunks: &[&[u8]], plan: &[Reply]) -> Run {
    let replies = plan
        .iter()
        .map(|reply| match *reply {
            Reply::TakeAll => driver::Reply::TakeAll,
            Reply::Leave { consumed } => driver::Reply::Leave(consumed),
            Reply::Fail { consumed } => driver::Reply::Fail(consumed),
            Reply::Finish { consumed } => driver::Reply::Finish(consumed),
            Reply::Switch { consumed, version } => driver::Reply::Switch(consumed, version),
            Reply::SwitchAndFinish { consumed, version } => {
                driver::Reply::SwitchAndFinish(consumed, version)
            }
        })
        .collect();
    let options = Options {
        behaviour: driver::Behaviour::Plan(replies),
        ..Options::default()
    };
    let mut feeds: Vec<Feed<'_>> = chunks.iter().map(|chunk| Feed::Slice(chunk)).collect();
    feeds.push(Feed::Eof);

    let mut run = Run {
        calls: Vec::new(),
        versions: Vec::new(),
        error: None,
        error_span: None,
        finished_at: None,
    };
    let mut locations = Vec::new();
    // the tokens of the current hand-over that are still to come
    let mut awaited = 0;
    for line in lex_backend::run(version, &options, &feeds) {
        match line {
            Line::Handover { version, count } => {
                assert_eq!(awaited, 0, "a hand-over with fewer tokens than it said");
                assert_ne!(count, 0, "every hand-over has at least one token");
                run.versions.push(version);
                run.calls.push(Vec::with_capacity(count));
                awaited = count;
            }
            Line::Token(token) => {
                assert_ne!(awaited, 0, "a token outside of a hand-over");
                awaited -= 1;
                let call = run.calls.last_mut().expect("a hand-over was started");
                call.push(Recorded {
                    ty: token.ty,
                    content: token.content,
                    span: RecordedSpan {
                        start: token.start,
                        end: token.end,
                    },
                });
            }
            Line::Finish(location) => {
                assert!(
                    run.finished_at.is_none(),
                    "a finished consumer is handed nothing more"
                );
                run.finished_at = Some(location);
            }
            Line::LexicalError { error, continues } => {
                assert_eq!(continues, None, "the lexer stops at its first error");
                run.error = Some(RunError::Lexical(error.kind));
                run.error_span = Some((error.start, error.end));
            }
            Line::ConsumerError { continues, .. } => {
                assert_eq!(continues, None, "the lexer stops at its first error");
                run.error = Some(RunError::Consumer);
            }
            Line::At(location) => locations.push(location),
            Line::Version(_) => {}
            Line::Abandon(_) | Line::Recover(_) => {
                panic!("a lexer that stops at its first error does not recover")
            }
        }
    }
    assert_eq!(awaited, 0, "a hand-over with fewer tokens than it said");

    // whatever the consumer did, after every chunk the lexer is after
    // everything it was fed, and the end of the input resets it
    let mut expected = SmtLocation::initial();
    for (index, location) in locations.iter().enumerate() {
        match chunks.get(index) {
            Some(chunk) => {
                expected = chunk
                    .iter()
                    .fold(expected, |location, &c| location.after_byte(c));
                assert_eq!(
                    *location,
                    loc(expected),
                    "location after the chunk {:?} under the plan {plan:?}",
                    String::from_utf8_lossy(chunk)
                );
            }
            None => assert_eq!(
                *location,
                (0, 0, 0),
                "the lexer must be reset to the origin"
            ),
        }
    }
    if run.error.is_none() {
        assert_eq!(locations.len(), feeds.len(), "every feed is applied");
    }

    if lex_backend::lean_driver().is_none() {
        assert_eq!(
            run_direct_from(version, chunks, plan),
            run,
            "the direct run and the run through the backend"
        );
    }
    run
}

/// Lexes the chunks, then end of file, from version 2.7.
#[track_caller]
fn run(chunks: &[&[u8]], plan: &[Reply]) -> Run {
    run_from(SmtVersion::V2_7, chunks, plan)
}

/// The tokens of the input lexed as one slice, taking everything.
fn reference(input: &[u8]) -> Vec<Recorded> {
    run(&[input], &[]).all()
}

/// A slice of `count` one-byte symbols.
fn symbols(count: usize) -> Vec<u8> {
    b"a ".repeat(count)
}

/// The end-of-file token as the last hand-over, alone.
#[track_caller]
fn assert_ends_with_eof_alone(run: &Run) {
    let last = run
        .calls
        .last()
        .expect("at least the end of file is handed over");
    assert_eq!(
        last.len(),
        1,
        "the end-of-file token must be handed over alone"
    );
    assert_eq!(last[0].ty, SmtTokenCategory::EndOfFile);
}

/// The message of the panic the closure must raise.
#[track_caller]
fn panic_message(run: impl FnOnce()) -> String {
    let payload = catch_unwind(AssertUnwindSafe(run)).expect_err("the run must panic");
    payload
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| payload.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_else(|| "<non-string panic payload>".to_string())
}

// --- Grouping ---

#[test]
fn tokens_are_batched_up_to_the_capacity_and_the_rest_follows() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    for count in [0, 1, 255, 256, 257, 300, 512, 513] {
        let input = symbols(count);
        let run = run(&[&input], &[]);
        let mut expected: Vec<usize> = vec![BATCH_CAPACITY; count / BATCH_CAPACITY];
        if count % BATCH_CAPACITY != 0 {
            expected.push(count % BATCH_CAPACITY);
        }
        expected.push(1);
        assert_eq!(run.sizes(), expected, "hand-over sizes for {count} symbols");
        assert_ends_with_eof_alone(&run);
        let all = run.all();
        assert_eq!(all.len(), count + 1);
        for (index, token) in all[..count].iter().enumerate() {
            assert_eq!(token.ty, SmtTokenCategory::UnquotedSymbol, "token {index}");
            assert_eq!(token.content, b"a", "token {index}");
            let start = 2 * index as u64;
            assert_eq!(token.span.start, (start, 0, start), "token {index}");
        }
        assert!(run.error.is_none());
    }
}

#[test]
fn the_end_of_a_slice_hands_over_the_batched_tokens() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    let cases: &[(Chunks, &[usize])] = &[
        (&[b"a b ", b" c d "], &[2, 2, 1]),
        (&[b"a b ", b"", b" c "], &[2, 1, 1]),
        (&[b"(a)", b"(b)"], &[3, 3, 1]),
        (&[b"a ", b" ", b"b "], &[1, 1, 1]),
    ];
    for (chunks, sizes) in cases {
        let run = run(chunks, &[]);
        assert_eq!(&run.sizes(), sizes, "chunks {chunks:?}");
        assert_ends_with_eof_alone(&run);
        assert_eq!(run.all(), reference(&chunks.concat()), "chunks {chunks:?}");
    }
}

#[test]
fn a_token_cut_by_a_slice_boundary_is_handed_over_alone() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // the cut token is finished from the lexer's own buffer, so it cannot
    // sit in a batch beside tokens borrowing the slice
    let cases: &[(Chunks, &[usize], &[u8])] = &[
        (&[b"a b", b" c"], &[1, 1, 1, 1], b"b"),
        (&[b"a", b"b c"], &[1, 1, 1], b"ab"),
        (&[b"x a", b"b c"], &[1, 1, 1, 1], b"ab"),
        (&[b"x \"s", b"t\" y"], &[1, 1, 1, 1], b"st"),
        (&[b"x |s\n", b"t| y"], &[1, 1, 1, 1], b"s\nt"),
        (&[b"x 1", b"2 y"], &[1, 1, 1, 1], b"12"),
        (&[b"x #x1", b"F y"], &[1, 1, 1, 1], b"1F"),
        (&[b"x :k", b"w y"], &[1, 1, 1, 1], b"kw"),
        (&[b"a"], &[1, 1], b"a"),
        (&[b"x a"], &[1, 1, 1], b"a"),
    ];
    for (chunks, sizes, cut) in cases {
        let run = run(chunks, &[]);
        assert_eq!(&run.sizes(), sizes, "chunks {chunks:?}");
        assert_ends_with_eof_alone(&run);
        let all = run.all();
        assert_eq!(all, reference(&chunks.concat()), "chunks {chunks:?}");
        let alone = run
            .calls
            .iter()
            .find(|tokens| tokens.len() == 1 && tokens[0].content == *cut)
            .unwrap_or_else(|| panic!("the cut token {cut:?} is handed over alone: {run:?}"));
        assert_eq!(alone[0].content, *cut);
    }
}

// --- Tokens left by the consumer ---

/// An input with every kind of line and location bookkeeping a rewind must
/// restore: line feeds between and inside tokens, a comment, and tokens of
/// several types.
const REWIND_INPUT: &[u8] = b"(a)\n(b c)\n|q\nr| \"s\" 12 ; c\n#x1F 1.5 :k)";

#[test]
fn tokens_left_are_handed_over_again() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    let reference = reference(REWIND_INPUT);
    let plain = run(&[REWIND_INPUT], &[]);
    assert_eq!(
        reference.len(),
        15,
        "the input has the expected token count"
    );
    // the quoted symbol with a line feed inside is finished from the stored
    // content, so it is handed over alone between the two batches
    assert_eq!(plain.sizes(), [7, 1, 6, 1]);

    for chunk_length in [1usize, 2, 3, 5, 7, REWIND_INPUT.len()] {
        let chunks: Vec<&[u8]> = REWIND_INPUT.chunks(chunk_length).collect();
        let calls = run(&chunks, &[]).calls;
        // every hand-over but the end of file, left after every prefix of at
        // least one token
        for (index, tokens) in calls[..calls.len() - 1].iter().enumerate() {
            for consumed in 1..=tokens.len() {
                let mut plan = vec![Reply::TakeAll; index];
                plan.push(Reply::Leave { consumed });
                let stopped = run(&chunks, &plan);
                let describe = format!(
                    "chunks of {chunk_length}, {consumed} of {} tokens of hand-over {index} taken",
                    tokens.len()
                );
                assert!(stopped.error.is_none(), "{describe}: {:?}", stopped.error);
                assert_eq!(
                    stopped.taken(&plan),
                    reference,
                    "{describe}: the taken tokens must be the reference tokens"
                );
                assert_ends_with_eof_alone(&stopped);
                if consumed < tokens.len() {
                    // the first token left arrives again, unchanged
                    assert_eq!(
                        stopped.calls[index + 1][0],
                        tokens[consumed],
                        "{describe}: the first token left is handed over again"
                    );
                }
            }
        }
    }
}

#[test]
fn leaving_nothing_continues_after_the_batch() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // every token of the hand-over is taken: nothing is handed over again, and
    // the next slice continues with the right locations
    let chunks: &[&[u8]] = &[b"a b ", b"c\nd "];
    let plan = [Reply::Leave { consumed: 2 }];
    let run = run(chunks, &plan);
    assert!(run.error.is_none());
    assert_eq!(run.sizes(), [2, 2, 1]);
    assert_eq!(run.taken(&plan), reference(&chunks.concat()));
    let d = &run.calls[1][1];
    assert_eq!(d.content, b"d");
    assert_eq!(d.span.start, (6, 1, 0));
}

#[test]
fn tokens_left_of_a_full_batch_come_before_the_rest_of_the_slice() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    let input = symbols(300);
    let plan = [Reply::Leave { consumed: 100 }];
    let run = run(&[&input], &plan);
    assert!(run.error.is_none());
    // the first batch was full; the 156 symbols left of it are handed over
    // again before the symbols that had not fitted into it. How the tokens
    // after the stop are grouped is not part of the contract.
    assert_eq!(run.sizes()[0], BATCH_CAPACITY);
    assert_eq!(run.calls[1][0], run.calls[0][100]);
    assert_eq!(run.taken(&plan), reference(&input));
    assert_ends_with_eof_alone(&run);
}

#[test]
fn leaving_tokens_at_every_hand_over_still_takes_the_reference() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // leaving tokens on every hand-over, not only the first: the consumer
    // still takes exactly the reference
    let plan = [
        Reply::Leave { consumed: 3 },
        Reply::Leave { consumed: 1 },
        Reply::Leave { consumed: 5 },
        Reply::Leave { consumed: 2 },
    ];
    let run = run(&[REWIND_INPUT], &plan);
    assert!(run.error.is_none());
    assert_eq!(run.taken(&plan), reference(REWIND_INPUT));
    assert_eq!(run.sizes(), [7, 4, 3, 1, 6, 1]);
}

#[test]
fn taking_one_token_per_hand_over_still_takes_the_reference() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // the slowest lawful consumer: every hand-over starts at the next token
    let reference = reference(REWIND_INPUT);
    let plan = vec![Reply::Leave { consumed: 1 }; reference.len()];
    for chunk_length in [1usize, 4, REWIND_INPUT.len()] {
        let chunks: Vec<&[u8]> = REWIND_INPUT.chunks(chunk_length).collect();
        let run = run(&chunks, &plan);
        assert!(run.error.is_none(), "chunks of {chunk_length}");
        assert_eq!(run.calls.len(), reference.len(), "chunks of {chunk_length}");
        assert_eq!(run.taken(&plan), reference, "chunks of {chunk_length}");
    }
}

// --- A stop without a consumed token ---

#[test]
fn a_stop_without_a_consumed_token_panics() {
    let v2_0 = SmtVersion::V2_0;
    let replies = [
        Reply::Leave { consumed: 0 },
        Reply::Fail { consumed: 0 },
        Reply::Finish { consumed: 0 },
        Reply::Switch {
            consumed: 0,
            version: v2_0,
        },
        Reply::SwitchAndFinish {
            consumed: 0,
            version: v2_0,
        },
    ];
    for reply in replies {
        let cases: [(Chunks, Vec<Reply>, &str); 5] = [
            (&[b"a b c "], vec![reply], "a batch of the slice"),
            (
                &[b"a b c "],
                vec![Reply::Leave { consumed: 1 }, reply],
                "the tokens left of a batch",
            ),
            (
                &[b"a b ", b"c d "],
                vec![Reply::TakeAll, reply],
                "a batch of a later slice",
            ),
            (&[b"a", b"b c"], vec![reply], "a token cut by the slice end"),
            (
                &[b"a "],
                vec![Reply::TakeAll, reply],
                "the end-of-file token",
            ),
        ];
        for (chunks, plan, what) in cases {
            let message = panic_message(|| {
                let _ = run_direct_from(SmtVersion::V2_7, chunks, &plan);
            });
            assert!(
                message.contains("at least one token"),
                "{reply:?} on {what}: panic {message:?} must say that the consumer \
                 has to consume at least one token"
            );
        }
    }
}

// --- Finishing ---

#[test]
fn tokens_left_by_a_finish_are_trailing_tokens() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // the consumer finishes after three tokens of the first hand-over: the
    // fourth is handed over to nobody, and is an error spanning that token
    let plan = [Reply::Finish { consumed: 3 }];
    let run = run(&[REWIND_INPUT], &plan);
    assert_eq!(
        run.error,
        Some(RunError::Lexical(
            SmtLexicalErrorKind::UnexpectedTrailingToken
        ))
    );
    let fourth = run.calls[0][3].span;
    assert_eq!(run.error_span, Some((fourth.start, fourth.end)));
    assert_eq!(run.sizes(), [7]);
    assert_eq!(run.taken(&plan), reference(REWIND_INPUT)[..3]);
    assert_eq!(run.finished_at, None);
}

#[test]
fn a_finish_holds_its_result_over_the_layout_after_it() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // the second chunk finishes the consumer at its only token: the layout
    // after it, also in a later chunk, is no token, and the end of the input
    // returns the result without handing over the end of file
    let chunks: &[&[u8]] = &[b"a b ", b"c ", b" ; d\n "];
    let plan = [Reply::TakeAll, Reply::Finish { consumed: 1 }];
    let run = run(chunks, &plan);
    assert!(run.error.is_none(), "{:?}", run.error);
    assert_eq!(run.sizes(), [2, 1]);
    assert_eq!(run.taken(&plan), reference(b"a b c ")[..3]);
    assert_eq!(run.finished_at, Some((5, 0, 5)));
}

#[test]
fn a_token_in_a_later_chunk_after_a_finish_is_a_trailing_token() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // the token after the finish is an error, whether a later slice ends it
    // or the end of the input does
    let plan = [Reply::TakeAll, Reply::Finish { consumed: 1 }];
    for last in [&b" d "[..], b" d"] {
        let run = run(&[b"a b ", b"c ", last], &plan);
        assert_eq!(
            run.error,
            Some(RunError::Lexical(
                SmtLexicalErrorKind::UnexpectedTrailingToken
            )),
            "{:?}",
            String::from_utf8_lossy(last)
        );
        assert_eq!(run.error_span, Some(((7, 0, 7), (8, 0, 8))));
        assert_eq!(run.sizes(), [2, 1]);
        assert_eq!(run.finished_at, None);
    }
}

#[test]
fn a_lexical_error_after_a_finish_is_reported_as_itself() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // the bytes after a finish are still lexed: a malformed token among them
    // is the lexical error it is, as no token reaches a hand-over
    let plan = [Reply::Finish { consumed: 1 }];
    let run = run(&[b"a ", b"#q "], &plan);
    assert_eq!(
        run.error,
        Some(RunError::Lexical(SmtLexicalErrorKind::Expected(
            SmtLexicalExpected::Base
        )))
    );
    assert_eq!(run.sizes(), [1]);
    assert_eq!(run.finished_at, None);
}

#[test]
fn layout_after_a_finish_is_a_trailing_token_for_a_concrete_consumer() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // a consumer that takes whitespace and comments is handed them as tokens,
    // so after its finish they are trailing tokens like any other
    let options = Options {
        whitespace: true,
        behaviour: driver::Behaviour::Plan(vec![driver::Reply::Finish(1)]),
        ..Options::default()
    };
    for (input, trailing) in [
        (&b"a b"[..], ((1, 0, 1), (2, 0, 2))),
        (b"a;c\n", ((1, 0, 1), (4, 1, 0))),
    ] {
        let lines = lex_backend::run(SmtVersion::V2_7, &options, &[Feed::Slice(input), Feed::Eof]);
        let error = lines.iter().find_map(|line| match line {
            Line::LexicalError { error, .. } => Some((error.kind, (error.start, error.end))),
            _ => None,
        });
        assert_eq!(
            error,
            Some((SmtLexicalErrorKind::UnexpectedTrailingToken, trailing)),
            "{:?}",
            String::from_utf8_lossy(input)
        );
        assert!(
            !lines.iter().any(|line| matches!(line, Line::Finish(_))),
            "a run with trailing tokens has no result"
        );
    }
}

#[test]
fn a_finish_with_a_version_set_reports_trailing_tokens_under_that_version() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // the consumer takes the symbol, sets 2.6 and finishes: the rest is lexed
    // again under 2.6, where the doubled quote is inside one string literal,
    // and that whole literal is the trailing token, not the error 2.0 would
    // have met
    let plan = [Reply::SwitchAndFinish {
        consumed: 1,
        version: SmtVersion::V2_6,
    }];
    let run = run_from(SmtVersion::V2_0, &[DOUBLED_QUOTE], &plan);
    assert_eq!(
        run.error,
        Some(RunError::Lexical(
            SmtLexicalErrorKind::UnexpectedTrailingToken
        ))
    );
    assert_eq!(run.error_span, Some(((2, 0, 2), (8, 0, 8))));
    assert_eq!(run.sizes(), [1]);
}

#[test]
fn a_finish_stop_at_the_end_of_file_token_is_returned_by_lex_eof() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // the tokens are handed over at the end of the slice, so the second
    // hand-over is the end-of-file token alone
    let plan = [Reply::TakeAll, Reply::Finish { consumed: 1 }];
    let run = run(&[b"a b "], &plan);
    assert!(run.error.is_none());
    assert_ends_with_eof_alone(&run);
    assert_eq!(run.finished_at, Some((4, 0, 4)));
}

#[test]
fn the_input_after_a_finished_one_starts_at_the_origin() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // once the end of the input has ended the finished input, the bytes fed
    // are a new input, whose tokens are located from the origin
    let mut calls = Vec::new();
    let mut versions = Vec::new();
    let plan = [Reply::Finish { consumed: 1 }];
    {
        let mut lexer = SmtLexer::new(
            Recorder {
                calls: &mut calls,
                versions: &mut versions,
                plan: &plan,
            },
            SmtVersion::V2_7,
        );
        lexer.lex_slice(b"a  ").expect("the slice must lex");
        assert_eq!(loc(lexer.current_location()), (3, 0, 3));
        assert_eq!(finished_at(lexer.lex_eof()), (1, 0, 1));
        assert_at_origin(&lexer);
        lexer.lex_slice(b"c\nd ").expect("the slice must lex");
        assert_eq!(loc(lexer.current_location()), (4, 1, 2));
        assert!(breaks_at_end(&lexer.lex_eof()));
        assert_at_origin(&lexer);
    }
    assert_eq!(
        calls.iter().map(Vec::len).collect::<Vec<_>>(),
        [1, 2, 1],
        "the second hand-over is the new input, the third its end of file"
    );
    let mut expected = reference(b"c\nd ");
    expected.truncate(2);
    assert_eq!(calls[1], expected);
    assert_eq!(calls[2][0].ty, SmtTokenCategory::EndOfFile);
    assert_eq!(calls[2][0].span.start, (4, 1, 2));
}

#[test]
fn a_finish_at_the_end_of_file_token_is_followed_by_a_new_input() {
    // finishing on the end-of-file token resets the lexer like any finish:
    // a further end of file is a new, empty input at the origin
    let mut calls = Vec::new();
    let mut versions = Vec::new();
    let plan = [Reply::TakeAll, Reply::Finish { consumed: 1 }];
    {
        let mut lexer = SmtLexer::new(
            Recorder {
                calls: &mut calls,
                versions: &mut versions,
                plan: &plan,
            },
            SmtVersion::V2_7,
        );
        lexer.lex_slice(b"a b ").expect("the slice must lex");
        assert_eq!(finished_at(lexer.lex_eof()), (4, 0, 4));
        assert_at_origin(&lexer);
        assert!(breaks_at_end(&lexer.lex_eof()));
    }
    assert_eq!(calls.iter().map(Vec::len).collect::<Vec<_>>(), [2, 1, 1]);
    assert_eq!(calls[2][0].ty, SmtTokenCategory::EndOfFile);
    assert_eq!(calls[2][0].span.start, (0, 0, 0));
}

// --- Setting the version ---

/// A string literal that is one token from version 2.5 on, and under
/// version 2.0 a string directly followed by a quote, which is an error.
const DOUBLED_QUOTE: &[u8] = b"a \"x\"\"y\" b";

/// A string literal that is one token under version 2.0, and from version
/// 2.5 on a string directly followed by a letter, which is an error.
const BACKSLASH_QUOTE: &[u8] = b"a \"x\\\"y\" b";

#[test]
fn a_version_applies_from_the_end_of_the_last_consumed_token() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // the consumer takes the first symbol and sets the other version: what
    // follows is lexed under it, in every chunking, though the lexer had
    // already lexed ahead under the old one
    let cases = [
        (SmtVersion::V2_0, SmtVersion::V2_6, DOUBLED_QUOTE),
        (SmtVersion::V2_7, SmtVersion::V2_0, BACKSLASH_QUOTE),
    ];
    for (initial, declared, input) in cases {
        let expected = run_from(declared, &[input], &[]);
        assert!(expected.error.is_none(), "test bug: {:?}", expected.error);
        let plan = [Reply::Switch {
            consumed: 1,
            version: declared,
        }];
        for chunk_length in 1..=input.len() {
            let chunks: Vec<&[u8]> = input.chunks(chunk_length).collect();
            let switched = run_from(initial, &chunks, &plan);
            let describe = format!("{initial:?} to {declared:?}, chunks of {chunk_length}");
            assert!(switched.error.is_none(), "{describe}: {:?}", switched.error);
            assert_eq!(switched.taken(&plan), expected.all(), "{describe}");
            assert_eq!(switched.versions[0], initial, "{describe}");
            assert!(
                switched.versions[1..].iter().all(|&v| v == declared),
                "{describe}: every later hand-over is under the set version, got {:?}",
                switched.versions
            );
        }
    }
}

#[test]
fn an_error_met_ahead_under_the_old_version_is_dropped() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // under 2.0 the quote directly after the string is an error, which the
    // lexer meets while lexing ahead; only the symbol before it is handed over
    let plain = run_from(SmtVersion::V2_0, &[DOUBLED_QUOTE], &[]);
    assert_eq!(plain.sizes(), [1]);
    assert!(
        matches!(
            &plain.error,
            Some(RunError::Lexical(SmtLexicalErrorKind::MissingDelimiter))
        ),
        "{:?}",
        plain.error
    );

    // the consumer takes that symbol, so no token is left, and sets 2.6:
    // the error belongs to the old version and must not be reported
    let plan = [Reply::Switch {
        consumed: 1,
        version: SmtVersion::V2_6,
    }];
    let switched = run_from(SmtVersion::V2_0, &[DOUBLED_QUOTE], &plan);
    assert!(switched.error.is_none(), "{:?}", switched.error);
    assert_eq!(switched.calls[0].len(), 1);
    assert_eq!(switched.calls[1][0].ty, SmtTokenCategory::String);
    assert_eq!(switched.calls[1][0].content, b"x\"y");
}

#[test]
fn an_error_under_both_versions_is_still_reported() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // the backslash is an error in every version: setting a version before
    // it does not make it go away
    let input: &[u8] = b"a \\ b";
    for declared in [SmtVersion::V2_0, SmtVersion::V2_7] {
        let plan = [Reply::Switch {
            consumed: 1,
            version: declared,
        }];
        let switched = run_from(SmtVersion::V2_6, &[input], &plan);
        assert!(
            matches!(
                &switched.error,
                Some(RunError::Lexical(SmtLexicalErrorKind::UnexpectedCharacter))
            ),
            "to {declared:?}: {:?}",
            switched.error
        );
    }
}

#[test]
fn a_version_set_with_tokens_left_hands_them_over_again_under_it() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // under 2.0 the hand-over holds two symbols, and the error lies ahead;
    // the consumer takes the first symbol and sets 2.6: the second symbol
    // comes again, and what follows it is one string and a symbol
    let input: &[u8] = b"a b \"x\"\"y\" c";
    let plain = run_from(SmtVersion::V2_0, &[input], &[]);
    assert_eq!(plain.sizes(), [2]);
    assert!(plain.error.is_some());

    let plan = [Reply::Switch {
        consumed: 1,
        version: SmtVersion::V2_6,
    }];
    let switched = run_from(SmtVersion::V2_0, &[input], &plan);
    assert!(switched.error.is_none(), "{:?}", switched.error);
    assert_eq!(
        switched.calls[1][0], plain.calls[0][1],
        "the symbol left is handed over again"
    );
    let taken = switched.taken(&plan);
    assert_eq!(taken, run_from(SmtVersion::V2_6, &[input], &[]).all());
    assert_eq!(taken[2].ty, SmtTokenCategory::String);
    assert_eq!(taken[2].content, b"x\"y");
}

#[test]
fn a_version_lasts_until_the_end_of_the_input() {
    // set on the first hand-over, the version holds for the later slices and
    // the end-of-file token; the next input starts under the initial version
    let mut calls = Vec::new();
    let mut versions = Vec::new();
    let plan = [Reply::Switch {
        consumed: 1,
        version: SmtVersion::V2_5,
    }];
    {
        let mut lexer = SmtLexer::new(
            Recorder {
                calls: &mut calls,
                versions: &mut versions,
                plan: &plan,
            },
            SmtVersion::V2_7,
        );
        for chunk in [&b"a "[..], b"b ", b"c "] {
            lexer.lex_slice(chunk).expect("the slice must lex");
        }
        assert!(breaks_at_end(&lexer.lex_eof()));
        lexer.lex_slice(b"d ").expect("the slice must lex");
        assert!(breaks_at_end(&lexer.lex_eof()));
    }
    assert_eq!(
        versions,
        [
            SmtVersion::V2_7,
            SmtVersion::V2_5,
            SmtVersion::V2_5,
            SmtVersion::V2_5,
            SmtVersion::V2_7,
            SmtVersion::V2_7,
        ]
    );
}

#[test]
fn a_version_may_be_set_at_the_end_of_the_input() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // a token finished by the end of the input, and the end-of-file token
    // itself, are hand-overs like any other: setting a version on them, also
    // one with other lexical rules, is allowed and lasts until the input ends
    let cases: [(&[Reply], &[SmtVersion]); 2] = [
        (
            &[Reply::Switch {
                consumed: 1,
                version: SmtVersion::V2_0,
            }],
            &[SmtVersion::V2_7, SmtVersion::V2_0],
        ),
        (
            &[
                Reply::TakeAll,
                Reply::Switch {
                    consumed: 1,
                    version: SmtVersion::V2_0,
                },
            ],
            &[SmtVersion::V2_7, SmtVersion::V2_7],
        ),
    ];
    for (plan, versions) in cases {
        // the symbol is cut by the end of the input: it is handed over alone
        // by the end-of-file call, before the end-of-file token
        let run = run(&[b"a"], plan);
        assert!(run.error.is_none(), "{plan:?}: {:?}", run.error);
        assert_eq!(run.sizes(), [1, 1], "{plan:?}");
        assert_ends_with_eof_alone(&run);
        assert_eq!(run.versions, versions, "{plan:?}");
    }
}

#[test]
fn a_version_set_while_finishing_has_no_effect() {
    // the finish ends the input, and the version ends with it: the next
    // input starts under the initial version
    let mut calls = Vec::new();
    let mut versions = Vec::new();
    let plan = [Reply::SwitchAndFinish {
        consumed: 1,
        version: SmtVersion::V2_0,
    }];
    {
        let mut lexer = SmtLexer::new(
            Recorder {
                calls: &mut calls,
                versions: &mut versions,
                plan: &plan,
            },
            SmtVersion::V2_7,
        );
        lexer.lex_slice(b"a  ").expect("the slice must lex");
        assert_eq!(loc(lexer.current_location()), (3, 0, 3));
        // the end of the input ends the finished input, the next one follows
        assert_eq!(finished_at(lexer.lex_eof()), (1, 0, 1));
        lexer.lex_slice(b"c ").expect("the slice must lex");
    }
    assert_eq!(versions, [SmtVersion::V2_7, SmtVersion::V2_7]);
}

// --- Errors ---

#[test]
fn tokens_before_a_lexer_error_are_handed_over_first() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // the backslash is a lexer error; the two tokens before it are batched
    // and reach the consumer before the error is returned
    let input: &[u8] = b"a b \\ c";
    let plain = run(&[input], &[]);
    assert_eq!(plain.sizes(), [2]);
    assert!(
        matches!(
            &plain.error,
            Some(RunError::Lexical(SmtLexicalErrorKind::UnexpectedCharacter))
        ),
        "{:?}",
        plain.error
    );

    // a token left on that hand-over comes before the error: the lexer goes
    // back, lexes the second symbol again, and meets the error again
    let plan = [Reply::Leave { consumed: 1 }];
    let stopped = run(&[input], &plan);
    assert_eq!(stopped.sizes(), [2, 1]);
    assert_eq!(stopped.calls[1][0].content, b"b");
    assert!(
        matches!(&stopped.error, Some(RunError::Lexical(_))),
        "{:?}",
        stopped.error
    );
}

#[test]
fn a_consumer_error_ends_the_run_with_the_consumer_error() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    let plan = [Reply::Fail { consumed: 1 }];
    let run = run(&[b"a b c "], &plan);
    assert_eq!(run.sizes(), [3]);
    assert_eq!(run.error, Some(RunError::Consumer));
}

#[test]
fn a_finish_in_a_whole_input_ends_that_input() {
    if lex_backend::boundaries_not_applicable() {
        return;
    }
    // an input lexed whole ends with its slice, and the next call lexes a
    // new input
    let mut calls = Vec::new();
    let mut versions = Vec::new();
    let plan = [Reply::Finish { consumed: 1 }];
    {
        let mut lexer = SmtLexer::new(
            Recorder {
                calls: &mut calls,
                versions: &mut versions,
                plan: &plan,
            },
            SmtVersion::V2_7,
        );
        assert_eq!(finished_at(lexer.lex_all(b"a  ")), (1, 0, 1));
        assert_at_origin(&lexer);
        assert!(breaks_at_end(&lexer.lex_all(b"c\nd ")));
        assert_at_origin(&lexer);
    }
    assert_eq!(
        calls.iter().map(Vec::len).collect::<Vec<_>>(),
        [1, 2, 1],
        "the second hand-over is the new input, the third its end of file"
    );
    let mut expected = reference(b"c\nd ");
    expected.truncate(2);
    assert_eq!(calls[1], expected);
}

#[test]
fn the_lexer_tells_the_version_in_force() {
    // the version the consumer has set is in force until the input ends,
    // whatever the consumer does afterwards, and the end of the input brings
    // back the version the lexer was constructed with
    let switch = Reply::Switch {
        consumed: 1,
        version: SmtVersion::V2_0,
    };
    let after_switch: [(&[Reply], &str); 4] = [
        (&[switch], "the consumer goes on"),
        (
            &[switch, Reply::Finish { consumed: 1 }],
            "the consumer finishes",
        ),
        (&[switch, Reply::Fail { consumed: 1 }], "the consumer fails"),
        (
            &[Reply::SwitchAndFinish {
                consumed: 2,
                version: SmtVersion::V2_0,
            }],
            "the consumer finishes with the switch",
        ),
    ];
    for (plan, what) in after_switch {
        let mut calls = Vec::new();
        let mut versions = Vec::new();
        let mut lexer = SmtLexer::new(
            Recorder {
                calls: &mut calls,
                versions: &mut versions,
                plan,
            },
            SmtVersion::V2_7,
        );
        assert_eq!(lexer.version(), SmtVersion::V2_7, "before the input");
        // every consumer that finishes takes the last token, so that no
        // trailing token ends the input with an error
        let result = lexer.lex_slice(b"a b ");
        assert_eq!(lexer.version(), SmtVersion::V2_0, "{what}");
        if result.is_err() {
            // the lexer has stopped at its first error, the input cannot end
            continue;
        }
        // also over the layout after a finish
        lexer.lex_slice(b" ;d\n").expect("the slice must lex");
        assert_eq!(lexer.version(), SmtVersion::V2_0, "{what}");
        // a finished input ends with its held result, the other one with the
        // break at the end-of-file token
        assert!(lexer.lex_eof().is_ok(), "{what}");
        assert_eq!(lexer.version(), SmtVersion::V2_7, "{what}: after the input");
    }
}

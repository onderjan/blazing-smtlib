//! Tests of the batch contract between the lexer and its token consumer:
//! how tokens are grouped into `consume` calls, and what a handler's
//! stop does to lexing.
//!
//! Tokens borrowing the current slice are batched and handed over when the
//! batch is full, at the end of the slice, and before an error is returned.
//! A token that began in an earlier slice and the end-of-file token are
//! handed over alone. A handler that takes only some of a batch's tokens
//! and requests re-lexing makes the lexer lex again after the last taken
//! token, so the tokens a handler takes are the same in every stopping
//! pattern, spans included. A handler that finishes ends lexing after the
//! tokens it took: that location is returned with the result, and the lexer
//! is reset to its initial state for the next input.

use std::ops::ControlFlow;
use std::panic::{AssertUnwindSafe, catch_unwind};

use blazing_smtlib::{
    SmtLocation, SmtSpan,
    read::lexer::{Lexer, SmtLexError, SmtLexicalErrorKind},
    token::{SmtBatchCursor, SmtConsume, SmtToken, SmtTokenCategory, SmtVersion},
};

/// The batch capacity the lexer is expected to use.
///
/// The capacity is not part of the public API; it is pinned here so that a
/// change is noticed and the expectations below are updated with it.
const BATCH_CAPACITY: usize = 256;

/// An owned copy of a handed-over token.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Recorded {
    ty: SmtTokenCategory,
    content: Vec<u8>,
    span: SmtSpan,
}

fn record(token: SmtToken) -> Recorded {
    Recorded {
        ty: token.category(),
        content: token.content().to_vec(),
        span: token.span(),
    }
}

/// The slices of one input, fed to the lexer in turn.
type Chunks = &'static [&'static [u8]];

fn loc(location: SmtLocation) -> (u64, u64, u64) {
    (location.offset(), location.line(), location.column())
}

/// What the handler replies to one `consume` call.
#[derive(Debug, Clone, Copy)]
enum Reply {
    /// Take every token.
    TakeAll,
    /// Take `consumed` tokens (at most the batch length) and request re-lexing.
    Relex { consumed: usize },
    /// Take `consumed` tokens (at most the batch length) and fail.
    Fail { consumed: usize },
    /// Take `consumed` tokens and return as if done, which the lexer rejects
    /// when tokens are left.
    Leave { consumed: usize },
    /// Take `consumed` tokens and finish.
    Finish { consumed: usize },
    /// Take `consumed` tokens, request re-lexing, and finish, which is a
    /// contradiction the lexer rejects.
    FinishAfterRelex { consumed: usize },
}

impl Reply {
    /// How many of `len` tokens the reply takes.
    fn takes(self, len: usize) -> usize {
        match self {
            Reply::TakeAll => len,
            Reply::Relex { consumed }
            | Reply::Fail { consumed }
            | Reply::Leave { consumed }
            | Reply::Finish { consumed }
            | Reply::FinishAfterRelex { consumed } => consumed.min(len),
        }
    }
}

/// A handler that records every hand-over and replies according to a plan.
///
/// The plan gives the reply of each call by index; calls past the plan's end
/// take every token. The records live outside the handler, so that they can
/// be read after the lexer, which owns the handler, is gone.
struct Recorder<'r> {
    calls: &'r mut Vec<Vec<Recorded>>,
    plan: &'r [Reply],
}

impl SmtConsume for Recorder<'_> {
    type Result = ();
    type Error = ();

    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, ()> {
        // record every token of the hand-over by walking a copy of the cursor
        let mut walk = *cursor;
        let mut tokens = Vec::new();
        while let Some(token) = walk.next() {
            tokens.push(record(token));
        }
        let len = tokens.len();
        let index = self.calls.len();
        self.calls.push(tokens);
        let reply = self.plan.get(index).copied().unwrap_or(Reply::TakeAll);
        cursor.advance(reply.takes(len));
        match reply {
            Reply::TakeAll | Reply::Leave { .. } => Ok(ControlFlow::Continue(())),
            Reply::Relex { .. } => {
                cursor.relex();
                Ok(ControlFlow::Continue(()))
            }
            Reply::Fail { .. } => Err(()),
            Reply::Finish { .. } => Ok(ControlFlow::Break(())),
            Reply::FinishAfterRelex { .. } => {
                cursor.relex();
                Ok(ControlFlow::Break(()))
            }
        }
    }
}

/// Everything observable about one lexer run.
#[derive(Debug)]
struct Run {
    /// The tokens of every hand-over, in order.
    calls: Vec<Vec<Recorded>>,
    /// The error that ended the run, if any.
    error: Option<SmtLexError<()>>,
    /// The location returned with the result if the handler finished.
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

    /// The tokens the handler took under the plan: for each hand-over, the
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

/// The lexer is at the origin, as it must be after a finish or an end of file.
#[track_caller]
fn assert_at_origin<H: SmtConsume>(lexer: &Lexer<H>) {
    assert_eq!(
        loc(lexer.current_location()),
        (0, 0, 0),
        "the lexer must be reset to the origin"
    );
}

/// Lexes the chunks, then end of file, with the handler replying by the plan.
///
/// After every successfully lexed chunk, the lexer's location is checked
/// against the location computed independently from the bytes, which a
/// rewind must restore correctly. After a finish, the lexer must be back
/// at the origin.
#[track_caller]
fn run(chunks: &[&[u8]], plan: &[Reply]) -> Run {
    let mut calls = Vec::new();
    let mut error = None;
    let mut finished_at = None;
    {
        let mut lexer = Lexer::new(
            Recorder {
                calls: &mut calls,
                plan,
            },
            SmtVersion::V2_7,
        );
        let mut expected = SmtLocation::initial();
        for chunk in chunks {
            match lexer.lex_slice(chunk) {
                Ok(ControlFlow::Continue(())) => {}
                Ok(ControlFlow::Break(located)) => {
                    finished_at = Some(loc(located.location()));
                    assert_at_origin(&lexer);
                    break;
                }
                Err(err) => {
                    error = Some(err);
                    break;
                }
            }
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
        if error.is_none() && finished_at.is_none() {
            match lexer.lex_eof() {
                Ok(ControlFlow::Continue(())) => assert_at_origin(&lexer),
                Ok(ControlFlow::Break(located)) => {
                    finished_at = Some(loc(located.location()));
                    assert_at_origin(&lexer);
                }
                Err(err) => error = Some(err),
            }
        }
    }
    Run {
        calls,
        error,
        finished_at,
    }
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

// --- Grouping ---

#[test]
fn tokens_are_batched_up_to_the_capacity_and_the_rest_follows() {
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
            assert_eq!(loc(token.span.start()), (start, 0, start), "token {index}");
        }
        assert!(run.error.is_none());
    }
}

#[test]
fn the_end_of_a_slice_hands_over_the_batched_tokens() {
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

// --- Re-lexing after a stop ---

/// An input with every kind of line and location bookkeeping a rewind must
/// restore: line feeds between and inside tokens, a comment, and tokens of
/// several types.
const RELEX_INPUT: &[u8] = b"(a)\n(b c)\n|q\nr| \"s\" 12 ; c\n#x1F 1.5 :k)";

#[test]
fn a_relex_stop_takes_a_prefix_and_lexes_the_rest_again() {
    let reference = reference(RELEX_INPUT);
    let plain = run(&[RELEX_INPUT], &[]);
    assert_eq!(
        reference.len(),
        15,
        "the input has the expected token count"
    );
    // the quoted symbol with a line feed inside is finished from the stored
    // content, so it is handed over alone between the two batches
    assert_eq!(plain.sizes(), [7, 1, 6, 1]);

    for chunk_length in [1usize, 2, 3, 5, 7, RELEX_INPUT.len()] {
        let chunks: Vec<&[u8]> = RELEX_INPUT.chunks(chunk_length).collect();
        let calls = run(&chunks, &[]).calls;
        // every hand-over but the end of file, stopped after every prefix of
        // at least one token; a stop before the first token of a hand-over
        // is legal only where that token began in the current slice, so it
        // is tested separately on whole slices
        for (index, tokens) in calls[..calls.len() - 1].iter().enumerate() {
            for consumed in 1..=tokens.len() {
                let mut plan = vec![Reply::TakeAll; index];
                plan.push(Reply::Relex { consumed });
                let stopped = run(&chunks, &plan);
                let describe = format!(
                    "chunks of {chunk_length}, stop after {consumed} of {} tokens of hand-over {index}",
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
                    // the first token after the stop arrives again, unchanged
                    assert_eq!(
                        stopped.calls[index + 1][0],
                        tokens[consumed],
                        "{describe}: the token after the stop is lexed again"
                    );
                }
            }
        }
    }
}

#[test]
fn a_relex_stop_before_the_first_token_lexes_the_batch_again() {
    let plan = [Reply::Relex { consumed: 0 }];
    let run = run(&[RELEX_INPUT], &plan);
    assert!(run.error.is_none());
    assert_eq!(run.sizes(), [7, 7, 1, 6, 1]);
    assert_eq!(run.calls[1], run.calls[0]);
    assert_eq!(run.taken(&plan), reference(RELEX_INPUT));
}

#[test]
fn a_relex_stop_after_a_whole_batch_continues_after_it() {
    // consumed equal to the batch length: nothing is lexed again, and the
    // next slice continues with the right locations
    let chunks: &[&[u8]] = &[b"a b ", b"c\nd "];
    let plan = [Reply::Relex { consumed: 2 }];
    let run = run(chunks, &plan);
    assert!(run.error.is_none());
    assert_eq!(run.sizes(), [2, 2, 1]);
    assert_eq!(run.taken(&plan), reference(&chunks.concat()));
    let d = &run.calls[1][1];
    assert_eq!(d.content, b"d");
    assert_eq!(loc(d.span.start()), (6, 1, 0));
}

#[test]
fn a_relex_stop_in_a_full_batch_refills_from_the_stop() {
    let input = symbols(300);
    let plan = [Reply::Relex { consumed: 100 }];
    let run = run(&[&input], &plan);
    assert!(run.error.is_none());
    // the first batch was full; after the stop the remaining 200 symbols
    // are lexed again into one batch, then the end of file follows alone
    assert_eq!(run.sizes(), [BATCH_CAPACITY, 200, 1]);
    assert_eq!(run.taken(&plan), reference(&input));
}

#[test]
fn a_relex_stop_at_every_hand_over_in_turn_still_takes_the_reference() {
    // stopping on every hand-over, not only the first: the plan replies with
    // a stop to each call, and the handler still takes exactly the reference
    let plan = [
        Reply::Relex { consumed: 3 },
        Reply::Relex { consumed: 1 },
        Reply::Relex { consumed: 5 },
        Reply::Relex { consumed: 2 },
    ];
    let run = run(&[RELEX_INPUT], &plan);
    assert!(run.error.is_none());
    assert_eq!(run.taken(&plan), reference(RELEX_INPUT));
    assert_eq!(run.sizes(), [7, 4, 3, 1, 6, 1]);
}

#[test]
fn impossible_stops_panic() {
    let cases: &[(Chunks, &[Reply], &str)] = &[
        // a relex stop at end of file, before or after the end-of-file token
        (
            &[b"a b"],
            &[Reply::TakeAll, Reply::Relex { consumed: 0 }],
            "cannot request relex at end of file",
        ),
        (
            &[b"a b"],
            &[Reply::TakeAll, Reply::Relex { consumed: 1 }],
            "cannot request relex at end of file",
        ),
        // a stop before a token that began in an earlier slice, whether the
        // handler asks for re-lexing or finishes: the location it would
        // report lies before the slice being lexed
        (
            &[b"a", b"b c"],
            &[Reply::Relex { consumed: 0 }],
            "must not stop before the starting token",
        ),
        (
            &[b"a", b"b c"],
            &[Reply::Finish { consumed: 0 }],
            "must not stop before the starting token",
        ),
    ];
    for (chunks, plan, expected) in cases {
        let outcome = catch_unwind(AssertUnwindSafe(|| run(chunks, plan)));
        let payload = outcome.expect_err("the run must panic");
        let message = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or("<non-string panic payload>");
        assert!(
            message.contains(expected),
            "chunks {chunks:?} under {plan:?}: panic {message:?} must mention {expected:?}"
        );
    }
}

// --- Finishing ---

#[test]
fn a_finish_stop_takes_a_prefix_and_ends_lexing() {
    // the handler finishes after three tokens of the first hand-over: nothing
    // more is handed over, not even the end of file, and the lexer is left
    // after the third token
    let plan = [Reply::Finish { consumed: 3 }];
    let run = run(&[RELEX_INPUT], &plan);
    assert!(run.error.is_none());
    assert_eq!(run.sizes(), [7]);
    assert_eq!(run.taken(&plan), reference(RELEX_INPUT)[..3]);
    assert_eq!(run.finished_at, Some(loc(run.calls[0][2].span.end())));
}

#[test]
fn a_finish_stop_before_the_first_token_ends_at_the_batch_start() {
    let plan = [Reply::Finish { consumed: 0 }];
    let run = run(&[RELEX_INPUT], &plan);
    assert!(run.error.is_none());
    assert_eq!(run.sizes(), [7]);
    assert!(run.taken(&plan).is_empty());
    assert_eq!(run.finished_at, Some((0, 0, 0)));
}

#[test]
fn a_finish_stop_across_chunks_leaves_the_rest_unread() {
    // the second chunk finishes the handler after its first token: the
    // third chunk is never lexed
    let chunks: &[&[u8]] = &[b"a b ", b"c d ", b"e f "];
    let plan = [Reply::TakeAll, Reply::Finish { consumed: 1 }];
    let run = run(chunks, &plan);
    assert!(run.error.is_none());
    assert_eq!(run.sizes(), [2, 2]);
    assert_eq!(run.taken(&plan), reference(b"a b c ")[..3]);
    assert_eq!(run.finished_at, Some((5, 0, 5)));
}

#[test]
fn a_finish_stop_at_the_end_of_file_token_is_returned_by_lex_eof() {
    // the tokens are handed over at the end of the slice, so the second
    // hand-over is the end-of-file token alone
    let plan = [Reply::TakeAll, Reply::Finish { consumed: 1 }];
    let run = run(&[b"a b "], &plan);
    assert!(run.error.is_none());
    assert_ends_with_eof_alone(&run);
    assert_eq!(run.finished_at, Some((4, 0, 4)));
}

#[test]
fn lexing_after_a_finish_starts_a_new_input_at_the_origin() {
    // the handler finishes after the first token of the first hand-over; the
    // bytes fed afterwards are a new input: the rest of the first slice is
    // not seen again, and the new tokens are located from the origin
    let mut calls = Vec::new();
    let plan = [Reply::Finish { consumed: 1 }];
    {
        let mut lexer = Lexer::new(
            Recorder {
                calls: &mut calls,
                plan: &plan,
            },
            SmtVersion::V2_7,
        );
        let located = match lexer.lex_slice(b"a b ") {
            Ok(ControlFlow::Break(located)) => located,
            other => panic!("expected a finish, got {other:?}"),
        };
        assert_eq!(loc(located.location()), (1, 0, 1));
        assert_at_origin(&lexer);
        assert!(matches!(
            lexer.lex_slice(b"c\nd "),
            Ok(ControlFlow::Continue(()))
        ));
        assert_eq!(loc(lexer.current_location()), (4, 1, 2));
        assert!(matches!(lexer.lex_eof(), Ok(ControlFlow::Continue(()))));
        assert_at_origin(&lexer);
    }
    assert_eq!(
        calls.iter().map(Vec::len).collect::<Vec<_>>(),
        [2, 2, 1],
        "the second hand-over is the new input, the third its end of file"
    );
    let mut expected = reference(b"c\nd ");
    expected.truncate(2);
    assert_eq!(calls[1], expected);
    assert_eq!(calls[2][0].ty, SmtTokenCategory::EndOfFile);
    assert_eq!(loc(calls[2][0].span.start()), (4, 1, 2));
}

#[test]
fn a_finish_at_the_end_of_file_token_is_followed_by_a_new_input() {
    // finishing on the end-of-file token resets the lexer like any finish:
    // a further end of file is a new, empty input at the origin
    let mut calls = Vec::new();
    let plan = [Reply::TakeAll, Reply::Finish { consumed: 1 }];
    {
        let mut lexer = Lexer::new(
            Recorder {
                calls: &mut calls,
                plan: &plan,
            },
            SmtVersion::V2_7,
        );
        assert!(matches!(
            lexer.lex_slice(b"a b "),
            Ok(ControlFlow::Continue(()))
        ));
        let located = match lexer.lex_eof() {
            Ok(ControlFlow::Break(located)) => located,
            other => panic!("expected a finish, got {other:?}"),
        };
        assert_eq!(loc(located.location()), (4, 0, 4));
        assert_at_origin(&lexer);
        assert!(matches!(lexer.lex_eof(), Ok(ControlFlow::Continue(()))));
    }
    assert_eq!(calls.iter().map(Vec::len).collect::<Vec<_>>(), [2, 1, 1]);
    assert_eq!(calls[2][0].ty, SmtTokenCategory::EndOfFile);
    assert_eq!(loc(calls[2][0].span.start()), (0, 0, 0));
}

#[test]
#[should_panic(expected = "cannot both finish and request relex")]
fn finishing_and_requesting_relex_together_panics() {
    let plan = [Reply::FinishAfterRelex { consumed: 1 }];
    let _ = run(&[b"a b "], &plan);
}

// --- Errors ---

#[test]
fn tokens_before_a_lexer_error_are_handed_over_first() {
    // the backslash is a lexer error; the two tokens before it are batched
    // and reach the handler before the error is returned
    let input: &[u8] = b"a b \\ c";
    let plain = run(&[input], &[]);
    assert_eq!(plain.sizes(), [2]);
    assert!(
        matches!(&plain.error, Some(SmtLexError::Lexical(err)) if *err.kind() == SmtLexicalErrorKind::UnexpectedCharacter),
        "{:?}",
        plain.error
    );

    // a stop on that hand-over wins over the error: the lexer rewinds, lexes
    // the second symbol again, and meets the error again
    let plan = [Reply::Relex { consumed: 1 }];
    let stopped = run(&[input], &plan);
    assert_eq!(stopped.sizes(), [2, 1]);
    assert_eq!(stopped.calls[1][0].content, b"b");
    assert!(
        matches!(&stopped.error, Some(SmtLexError::Lexical(_))),
        "{:?}",
        stopped.error
    );
}

#[test]
fn a_handler_that_returns_ok_with_tokens_left_panics() {
    let cases: &[(Chunks, &[Reply])] = &[
        (&[b"a b c "], &[Reply::Leave { consumed: 1 }]),
        (&[b"a b c "], &[Reply::Leave { consumed: 0 }]),
        // a lone stored token and the end-of-file token count too
        (&[b"a", b"b "], &[Reply::Leave { consumed: 0 }]),
        (&[b"a "], &[Reply::TakeAll, Reply::Leave { consumed: 0 }]),
    ];
    for (chunks, plan) in cases {
        let outcome = catch_unwind(AssertUnwindSafe(|| run(chunks, plan)));
        let payload = outcome.expect_err("the run must panic");
        let message = payload
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| payload.downcast_ref::<&str>().copied())
            .unwrap_or("<non-string panic payload>");
        assert!(
            message.contains("must consume all tokens before continuing"),
            "chunks {chunks:?} under {plan:?}: panic {message:?}"
        );
    }
}

#[test]
fn a_handler_that_consumes_everything_and_returns_ok_continues() {
    // the plain plan is exactly that on every hand-over, so the reference run
    // is the witness; a plan that leaves nothing is the same as taking all
    let full = run(
        &[b"a b c "],
        &[Reply::Leave { consumed: 3 }, Reply::Leave { consumed: 1 }],
    );
    assert!(full.error.is_none());
    assert_eq!(full.all(), reference(b"a b c "));
}

#[test]
fn a_handler_error_ends_the_run_with_the_handler_error() {
    let plan = [Reply::Fail { consumed: 1 }];
    let run = run(&[b"a b c "], &plan);
    assert_eq!(run.sizes(), [3]);
    assert_eq!(run.error, Some(SmtLexError::Consumer(())));
}

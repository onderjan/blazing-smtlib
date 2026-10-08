//! Tests of the token cursor and of the entry point of the category
//! parsers, `parse`, on the cursors the lexer hands over.
//!
//! A cursor over a batch can only come from the lexer, so every test lexes a
//! small input and runs its checks inside the consumer, on each hand-over.
//! The consumer sees the cursor only as a producer, so the checks go through
//! the producer trait, as every consumer's do.

use std::cell::RefCell;
use std::convert::Infallible;
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtSyntaxChecker,
    lexer::SmtLexer,
    parser::{SmtParse, SmtParseState, SmtSortParser, SmtTermParser},
    token::{SmtConsume, SmtLookahead, SmtProduce, SmtToken, SmtTokenCategory, SmtVersion},
};

/// A check run on a hand-over, generic over the producer as a consumer is.
trait Check {
    fn check<'a, P: SmtProduce<'a>>(&mut self, cursor: &mut P);
}

/// A check from a block over the cursor, for checks that keep no state
/// between hand-overs.
macro_rules! check {
    (|$cursor:ident| $body:block) => {{
        struct Body;
        impl Check for Body {
            fn check<'a, P: SmtProduce<'a>>(&mut self, $cursor: &mut P) $body
        }
        Body
    }};
}

/// Which hand-overs a probe runs its check on.
enum Which {
    /// Every hand-over.
    Every,
    /// The single hand-over of the input before the end of file.
    TokenBatch,
    /// The first hand-over only.
    First,
}

/// A consumer that runs a check on the hand-overs it is told to, then
/// consumes what the check left of each hand-over.
struct Probe<C> {
    check: C,
    which: Which,
    seen: usize,
}

impl<C: Check> SmtConsume for Probe<C> {
    type Result = ();
    type Error = Infallible;
    const IS_CONCRETE: bool = false;

    fn consume<'a, P: SmtProduce<'a>>(
        &mut self,
        cursor: &mut P,
    ) -> Result<ControlFlow<Self::Result>, Infallible> {
        let run = match self.which {
            Which::Every => true,
            Which::TokenBatch => {
                let at_end = cursor.peek().map(|token| token.category())
                    == Some(SmtTokenCategory::EndOfFile);
                !at_end
            }
            Which::First => self.seen == 0,
        };
        if run {
            self.check.check(cursor);
        }
        self.seen += 1;
        cursor.consume_all();
        Ok(ControlFlow::Continue(()))
    }
}

/// Lexes the chunks and end of file, running the check on the chosen
/// hand-overs, and returns the probe.
fn probe<C: Check>(chunks: &[&[u8]], which: Which, check: C) -> Probe<C> {
    let mut probe = Probe {
        check,
        which,
        seen: 0,
    };
    let mut lexer = SmtLexer::new(&mut probe, SmtVersion::V2_7);
    for chunk in chunks {
        let _ = lexer.lex_slice(chunk).expect("valid input must lex");
    }
    let _ = lexer.lex_eof().expect("valid input must lex");
    drop(lexer);
    probe
}

/// The single hand-over of the input as one slice, before the end of file.
fn on_token_batch(input: &[u8], check: impl Check) {
    let probe = probe(&[input], Which::TokenBatch, check);
    assert_eq!(
        probe.seen, 2,
        "the input must arrive as one batch before the end of file"
    );
}

/// The first hand-over of the input as one slice. What follows it is consumed
/// without a check: a check that sets a version with other lexical rules makes
/// the lexer hand the rest of the input over again.
fn on_first_batch(input: &[u8], check: impl Check) {
    let probe = probe(&[input], Which::First, check);
    assert!(
        probe.seen >= 2,
        "the input and the end of file must be handed over"
    );
}

/// The tokens ahead in the cursor, without consuming any.
///
/// A consumer has no way to look at tokens without consuming them, so this
/// goes through an attempt that takes every token and then fails, and
/// carries the tokens out of the extractor in a cell.
fn ahead<'a, P: SmtProduce<'a>>(cursor: &mut P) -> Vec<SmtToken<'a>> {
    let seen = RefCell::new(Vec::new());
    let failed: Option<()> = cursor.attempt(|window| {
        while let Some(token) = window.next() {
            seen.borrow_mut().push(token);
        }
        None
    });
    assert!(failed.is_none());
    seen.into_inner()
}

// --- The cursor ---

#[test]
fn cursor_walks_the_batch_in_order() {
    on_token_batch(
        b"(a b) c ",
        check!(|cursor| {
            let tokens = ahead(cursor);
            assert_eq!(tokens.len(), 5);

            // at the start: nothing consumed, everything ahead
            assert!(!cursor.is_empty());
            assert_eq!(cursor.peek(), Some(tokens[0]));

            // one token taken
            let first = cursor.next().expect("a token");
            assert_eq!(first, tokens[0]);
            assert_eq!(first.category(), SmtTokenCategory::ParenOpen);
            assert_eq!(cursor.peek(), Some(tokens[1]));

            // looking at the next token does not take it
            assert_eq!(cursor.peek(), Some(tokens[1]));
            assert_eq!(ahead(cursor), tokens[1..]);

            // to the end and past it
            assert_eq!(cursor.next(), Some(tokens[1]));
            assert_eq!(cursor.next(), Some(tokens[2]));
            assert_eq!(
                cursor.next().map(|token| token.category()),
                Some(SmtTokenCategory::ParenClose)
            );
            assert_eq!(cursor.next().map(|token| token.content()), Some(&b"c"[..]));
            assert!(cursor.is_empty());
            assert_eq!(cursor.peek(), None);
            assert_eq!(cursor.next(), None);
            assert!(ahead(cursor).is_empty());
        }),
    );
}

#[test]
fn cursor_over_the_end_of_file_batch_yields_it_alone() {
    /// Checks the second hand-over, which must be the end of file alone.
    struct Second {
        batches: usize,
    }
    impl Check for Second {
        fn check<'a, P: SmtProduce<'a>>(&mut self, cursor: &mut P) {
            self.batches += 1;
            if self.batches == 2 {
                assert_eq!(ahead(cursor).len(), 1);
                assert_eq!(
                    cursor.next().map(|token| token.category()),
                    Some(SmtTokenCategory::EndOfFile)
                );
                assert!(cursor.is_empty());
            }
        }
    }
    let probe = probe(&[b"a "], Which::Every, Second { batches: 0 });
    assert_eq!(probe.check.batches, 2);
}

#[test]
fn consuming_all_empties_the_cursor_at_its_end() {
    on_token_batch(
        b"a b c ",
        check!(|cursor| {
            cursor.next();
            cursor.consume_all();
            assert!(cursor.is_empty());
            assert_eq!(cursor.peek(), None);
            assert_eq!(cursor.next(), None);
            assert!(ahead(cursor).is_empty());
            // consuming all of an empty cursor changes nothing
            cursor.consume_all();
            assert!(cursor.is_empty());
        }),
    );

    // after a version with other lexical rules is set, there is nothing
    // left to consume
    on_first_batch(
        b"a b c ",
        check!(|cursor| {
            cursor.next().expect("a token");
            cursor.set_version(SmtVersion::V2_0);
            cursor.consume_all();
            assert!(cursor.is_empty());
            assert_eq!(cursor.next(), None);
        }),
    );
}

// --- Attempts ---

#[test]
fn an_attempt_that_succeeds_consumes_exactly_what_it_took() {
    on_token_batch(
        b"a b c d ",
        check!(|cursor| {
            let tokens = ahead(cursor);
            // the value of the extractor is returned
            let taken = cursor.attempt(|window| {
                let first = window.next()?;
                let second = window.next()?;
                Some((first, second))
            });
            assert_eq!(taken, Some((tokens[0], tokens[1])));
            assert_eq!(cursor.peek(), Some(tokens[2]));

            // the next attempt starts at the next token
            assert_eq!(cursor.attempt(|window| window.next()), Some(tokens[2]));
            assert_eq!(cursor.peek(), Some(tokens[3]));

            // an extractor that succeeds without taking a token consumes nothing
            assert_eq!(cursor.attempt(|_| Some(7)), Some(7));
            assert_eq!(cursor.peek(), Some(tokens[3]));
            assert_eq!(ahead(cursor), tokens[3..]);
        }),
    );
}

#[test]
fn an_attempt_that_fails_consumes_nothing() {
    on_token_batch(
        b"a b c d ",
        check!(|cursor| {
            let tokens = ahead(cursor);
            // without taking a token, and after taking some or all of them
            for take in [0, 1, 3, 4] {
                let failed: Option<()> = cursor.attempt(|window| {
                    for _ in 0..take {
                        window.next()?;
                    }
                    None
                });
                assert_eq!(failed, None);
                assert_eq!(cursor.peek(), Some(tokens[0]), "after taking {take}");
                assert_eq!(ahead(cursor), tokens, "after taking {take}");
            }

            // the same after some tokens are consumed
            cursor.next();
            let failed: Option<()> = cursor.attempt(|window| {
                window.next()?;
                None
            });
            assert_eq!(failed, None);
            assert_eq!(cursor.peek(), Some(tokens[1]));
            assert_eq!(ahead(cursor), tokens[1..]);
        }),
    );
}

#[test]
fn a_window_ends_where_the_cursor_does() {
    on_token_batch(
        b"a b c ",
        check!(|cursor| {
            let tokens = ahead(cursor);
            cursor.next();
            cursor.next();

            // one token is left: an extractor that needs two runs out and fails,
            // and nothing is consumed
            let two = cursor.attempt(|window| {
                let first = window.next()?;
                let second = window.next()?;
                Some((first, second))
            });
            assert_eq!(two, None);
            assert_eq!(cursor.peek(), Some(tokens[2]));

            // past its end the window keeps yielding nothing
            let counted = cursor.attempt(|window| {
                let mut count = 0;
                while window.next().is_some() {
                    count += 1;
                }
                assert!(window.next().is_none());
                Some(count)
            });
            assert_eq!(counted, Some(1));
            assert!(cursor.is_empty());

            // the window of an empty cursor is empty
            assert_eq!(cursor.attempt(|window| window.next()), None);
            assert_eq!(
                cursor.attempt(|window| Some(window.next().is_none())),
                Some(true)
            );
        }),
    );
}

#[test]
fn an_extractor_can_choose_among_shapes_that_share_a_start() {
    // the shapes "( symbol" and "( ( symbol" share the opening parenthesis:
    // one attempt reads it once and goes on by what follows
    #[derive(Debug, PartialEq)]
    enum Shape {
        Open(Vec<u8>),
        OpenOpen(Vec<u8>),
    }
    fn shape<'a, P: SmtProduce<'a>>(cursor: &mut P) -> Option<Shape> {
        cursor.attempt(|window| {
            if window.next()?.category() != SmtTokenCategory::ParenOpen {
                return None;
            }
            let second = window.next()?;
            match second.category() {
                SmtTokenCategory::UnquotedSymbol => Some(Shape::Open(second.content().to_vec())),
                SmtTokenCategory::ParenOpen => {
                    let third = window.next()?;
                    (third.category() == SmtTokenCategory::UnquotedSymbol)
                        .then(|| Shape::OpenOpen(third.content().to_vec()))
                }
                _ => None,
            }
        })
    }

    on_token_batch(
        b"(a ((b (1 (",
        check!(|cursor| {
            let tokens = ahead(cursor);
            assert_eq!(shape(cursor), Some(Shape::Open(b"a".to_vec())));
            assert_eq!(cursor.peek(), Some(tokens[2]));
            assert_eq!(shape(cursor), Some(Shape::OpenOpen(b"b".to_vec())));
            assert_eq!(cursor.peek(), Some(tokens[5]));
            // neither shape: nothing is consumed, not even the parenthesis
            assert_eq!(shape(cursor), None);
            assert_eq!(cursor.peek(), Some(tokens[5]));
            cursor.next();
            cursor.next();
            // a shape cut by the end of the batch: nothing is consumed either
            assert_eq!(shape(cursor), None);
            assert_eq!(cursor.peek(), Some(tokens[7]));
        }),
    );
}

// --- Setting the version ---

#[test]
fn a_version_with_the_same_lexical_rules_keeps_the_tokens_ahead() {
    on_token_batch(
        b"(a b) ",
        check!(|cursor| {
            let tokens = ahead(cursor);
            cursor.next();
            cursor.next();
            cursor.set_version(SmtVersion::V2_5);
            assert_eq!(cursor.version(), SmtVersion::V2_5);
            assert!(!cursor.is_empty());
            assert_eq!(ahead(cursor), tokens[2..]);
            assert_eq!(cursor.next(), Some(tokens[2]));
        }),
    );
}

#[test]
fn a_version_with_other_lexical_rules_fixes_the_cursor_at_the_consumed_position() {
    on_first_batch(
        b"(a b) ",
        check!(|cursor| {
            cursor.next();
            let second = cursor.next().expect("a token");
            cursor.set_version(SmtVersion::V2_0);
            assert_eq!(cursor.version(), SmtVersion::V2_0);
            // the tokens ahead were lexed under the old rules: nothing more comes
            // out of the cursor or of a window
            assert!(cursor.is_empty());
            assert!(cursor.peek().is_none());
            assert!(cursor.next().is_none());
            assert!(ahead(cursor).is_empty());
            assert_eq!(cursor.attempt(|window| window.next()), None);
            assert_eq!(second.content(), b"a");
        }),
    );
}

// --- The batch entry point of category parsers ---

/// A consumer that drives a category parser through `parse` until it
/// finishes, recording per hand-over how many tokens it consumed and whether
/// it finished.
struct Drive<P> {
    parser: P,
    parse_state: SmtParseState<SmtSyntaxChecker>,
    finished: bool,
    calls: Vec<(usize, bool)>,
}

impl<P: SmtParse<SmtSyntaxChecker>> SmtConsume for Drive<P> {
    type Result = ();
    type Error = Infallible;
    const IS_CONCRETE: bool = false;

    fn consume<'a, C: SmtProduce<'a>>(
        &mut self,
        cursor: &mut C,
    ) -> Result<ControlFlow<Self::Result>, Infallible> {
        if !self.finished {
            let before = ahead(cursor).len();
            let flow = self
                .parser
                .parse(&mut SmtSyntaxChecker, &mut self.parse_state, cursor)
                .expect("the category must parse");
            self.finished = matches!(flow, ControlFlow::Break(_));
            self.calls
                .push((before - ahead(cursor).len(), self.finished));
        }
        cursor.consume_all();
        Ok(ControlFlow::Continue(()))
    }
}

/// Drives the parser through `parse` on the hand-overs of the chunks,
/// returning per hand-over how many tokens it consumed and whether it finished.
fn drive<P: SmtParse<SmtSyntaxChecker> + Default>(chunks: &[&[u8]]) -> Vec<(usize, bool)> {
    let mut drive = Drive {
        parser: P::default(),
        parse_state: SmtParseState::new(),
        finished: false,
        calls: Vec::new(),
    };
    let mut lexer = SmtLexer::new(&mut drive, SmtVersion::V2_7);
    for chunk in chunks {
        let _ = lexer.lex_slice(chunk).expect("valid input must lex");
    }
    let _ = lexer.lex_eof().expect("valid input must lex");
    drop(lexer);
    drive.calls
}

#[test]
fn parse_stops_after_the_category_and_leaves_the_rest() {
    // the same property for a term and a sort: five tokens make the category,
    // the sixth is left in the cursor
    assert_eq!(drive::<SmtTermParser<_>>(&[b"(f a b) x "]), [(5, true)]);
    assert_eq!(drive::<SmtSortParser<_>>(&[b"(Array a b) x "]), [(5, true)]);
}

#[test]
fn parse_continues_across_batches() {
    // the category spans two hand-overs: the first is consumed whole without a
    // result, the second finishes it after two tokens
    assert_eq!(
        drive::<SmtTermParser<_>>(&[b"(f a ", b"b) x "]),
        [(3, false), (2, true)]
    );
    assert_eq!(
        drive::<SmtSortParser<_>>(&[b"(Array a ", b"b) x "]),
        [(3, false), (2, true)]
    );
}

#[test]
fn parse_finishes_at_the_last_token_of_a_batch() {
    // the closing parenthesis is the hand-over's last token: finished, nothing left
    assert_eq!(
        drive::<SmtTermParser<_>>(&[b"(f a b)", b" x "]),
        [(5, true)]
    );
}

#[test]
fn parse_reports_the_parser_error() {
    on_token_batch(
        b") x ",
        check!(|cursor| {
            let result = SmtTermParser::<SmtSyntaxChecker>::default().parse(
                &mut SmtSyntaxChecker,
                &mut SmtParseState::new(),
                cursor,
            );
            assert!(result.is_err(), "a closing parenthesis cannot start a term");
        }),
    );
}

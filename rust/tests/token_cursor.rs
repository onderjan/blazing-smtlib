//! Tests of the token cursor and of the entry point of the category
//! parsers, `parse`, on the cursors the lexer hands over.
//!
//! A cursor over a batch can only come from the lexer, so every test lexes a
//! small input and runs its checks inside the handler, on each hand-over.

use std::convert::Infallible;
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtSyntaxChecker,
    read::{
        lexer::SmtLexer,
        parser::{SmtParse, SmtParseState, SmtSortParser, SmtTermParser},
    },
    token::{SmtBatchCursor, SmtConsume, SmtTokenCategory, SmtVersion},
};

/// A handler that runs a check on a copy of every cursor it receives, then
/// consumes the hand-over.
struct Probe<F>(F);

impl<F: FnMut(SmtBatchCursor<'_>)> SmtConsume for Probe<F> {
    type Result = ();
    type Error = Infallible;

    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Infallible> {
        (self.0)(*cursor);
        cursor.consume_all();
        Ok(ControlFlow::Continue(()))
    }
}

/// Lexes the chunks and end of file, running the check on every hand-over.
fn on_batches(chunks: &[&[u8]], check: impl FnMut(SmtBatchCursor<'_>)) {
    let mut lexer = SmtLexer::new(Probe(check), SmtVersion::V2_7);
    for chunk in chunks {
        let _ = lexer.lex_slice(chunk).expect("valid input must lex");
    }
    let _ = lexer.lex_eof().expect("valid input must lex");
}

/// The single hand-over of the input as one slice, before the end of file.
fn on_token_batch(input: &[u8], mut check: impl FnMut(SmtBatchCursor<'_>)) {
    let mut seen = 0;
    on_batches(&[input], |cursor| {
        if cursor.peek().map(|token| token.category()) == Some(SmtTokenCategory::EndOfFile) {
            return;
        }
        seen += 1;
        check(cursor);
    });
    assert_eq!(
        seen, 1,
        "the input must arrive as one batch before the end of file"
    );
}

/// How many tokens a fresh cursor holds, counted by walking a copy.
fn len(cursor: SmtBatchCursor<'_>) -> usize {
    let mut walk = cursor;
    let mut count = 0;
    while walk.next().is_some() {
        count += 1;
    }
    count
}

// --- The cursor ---

#[test]
fn cursor_walks_the_batch_in_order() {
    on_token_batch(b"(a b) c ", |start| {
        assert_eq!(len(start), 5);
        let mut cursor = start;

        // at the start: nothing consumed, everything ahead
        assert_eq!(cursor.consumed(), 0);
        assert!(!cursor.is_empty());
        assert_eq!(cursor.peek(), start.get(0));
        assert_eq!(cursor.get(0), start.get(0));
        assert_eq!(cursor.get(4), start.get(4));
        assert_eq!(cursor.get(5), None);
        assert_eq!(cursor.last_consumed(), None);

        // one token taken
        let first = cursor.next().expect("a token");
        assert_eq!(first.category(), SmtTokenCategory::ParenOpen);
        assert_eq!(cursor.consumed(), 1);
        assert_eq!(cursor.last_consumed(), Some(first));
        assert_eq!(cursor.peek(), start.get(1));

        // two more at once: the lookback and lookahead move with them
        cursor.advance(2);
        assert_eq!(cursor.consumed(), 3);
        assert_eq!(cursor.last_consumed(), start.get(2));
        assert_eq!(cursor.get(0), start.get(3));
        assert_eq!(cursor.get(1), start.get(4));
        assert_eq!(cursor.get(2), None);

        // to the end and past it
        assert_eq!(
            cursor.next().map(|token| token.category()),
            Some(SmtTokenCategory::ParenClose)
        );
        assert_eq!(cursor.next().map(|token| token.content()), Some(&b"c"[..]));
        assert!(cursor.is_empty());
        assert_eq!(cursor.consumed(), 5);
        assert_eq!(cursor.peek(), None);
        assert_eq!(cursor.next(), None);
        assert_eq!(cursor.consumed(), 5, "taking past the end consumes nothing");
        assert_eq!(cursor.last_consumed(), start.get(4));
    });
}

#[test]
fn cursor_over_the_end_of_file_batch_yields_it_alone() {
    let mut batches = 0;
    on_batches(&[b"a "], |start| {
        batches += 1;
        if batches == 2 {
            assert_eq!(len(start), 1);
            let mut cursor = start;
            assert_eq!(
                cursor.next().map(|token| token.category()),
                Some(SmtTokenCategory::EndOfFile)
            );
            assert!(cursor.is_empty());
        }
    });
    assert_eq!(batches, 2);
}

#[test]
fn cursor_is_a_copy_of_its_position() {
    // a copied cursor keeps its own position, which lets a parser look ahead
    // by walking a copy and consume from the original
    on_token_batch(b"(a b) c ", |start| {
        let mut cursor = start;
        let mut ahead = cursor;
        ahead.advance(3);
        assert_eq!(cursor.consumed(), 0);
        assert_eq!(ahead.consumed(), 3);
        cursor.next();
        assert_eq!(ahead.consumed(), 3);
    });
}

#[test]
fn single_token_cursor_holds_that_token_alone() {
    on_token_batch(b"(a b) c ", |start| {
        let mut walk = start;
        while let Some(token) = walk.next() {
            let mut cursor = SmtBatchCursor::single(SmtVersion::V2_7, token);
            assert!(!cursor.is_empty());
            assert_eq!(cursor.peek(), Some(token));
            assert_eq!(cursor.get(1), None);
            assert_eq!(cursor.next(), Some(token));
            assert!(cursor.is_empty());
            assert_eq!(cursor.last_consumed(), Some(token));
        }
    });
}

#[test]
fn advancing_past_the_end_stops_at_the_end_like_next() {
    on_token_batch(b"a b ", |start| {
        let mut cursor = start;
        cursor.advance(3);
        assert!(cursor.is_empty());
        assert_eq!(cursor.consumed(), 2);
        assert_eq!(cursor.last_consumed(), start.get(1));
        cursor.consume_all();
        assert_eq!(cursor.consumed(), 2);
    });
}

#[test]
fn advancing_consumes_that_many_tokens_in_order() {
    on_token_batch(b"a b c d ", |start| {
        let mut cursor = start;
        cursor.advance(0);
        assert_eq!(cursor.consumed(), 0);
        assert_eq!(cursor.last_consumed(), None);
        cursor.advance(2);
        assert_eq!(cursor.consumed(), 2);
        assert_eq!(cursor.peek(), start.get(2));
        assert_eq!(cursor.last_consumed(), start.get(1));
        // advancing continues where the cursor is, like repeated next calls
        cursor.advance(1);
        assert_eq!(cursor.next(), start.get(3));
        assert!(cursor.is_empty());
    });
}

#[test]
fn consuming_all_empties_the_cursor_at_its_end() {
    on_token_batch(b"a b c ", |start| {
        let mut cursor = start;
        cursor.next();
        cursor.consume_all();
        assert!(cursor.is_empty());
        assert_eq!(cursor.consumed(), 3);
        assert_eq!(cursor.peek(), None);
        assert_eq!(cursor.next(), None);
        assert_eq!(cursor.last_consumed(), start.get(2));
        // consuming all of an empty cursor changes nothing
        cursor.consume_all();
        assert_eq!(cursor.consumed(), 3);

        // after a relex request there is nothing left to consume
        let mut cursor = start;
        cursor.advance(1);
        cursor.relex();
        cursor.consume_all();
        assert_eq!(cursor.consumed(), 1);
        assert_eq!(cursor.last_consumed(), start.get(0));
    });
}

// --- The batch entry point of category parsers ---

/// Drives the parser through `parse` on the hand-overs of the chunks,
/// returning per hand-over how many tokens it consumed and whether it finished.
fn drive<P: SmtParse<SmtSyntaxChecker> + Default>(chunks: &[&[u8]]) -> Vec<(usize, bool)> {
    let mut parser = P::default();
    let mut resources = SmtParseState::new();
    let mut finished = false;
    let mut calls = Vec::new();
    on_batches(chunks, |mut cursor| {
        if finished {
            return;
        }
        let flow = parser
            .parse(&mut SmtSyntaxChecker, &mut resources, &mut cursor)
            .expect("the category must parse");
        finished = matches!(flow, ControlFlow::Break(_));
        calls.push((cursor.consumed(), finished));
    });
    calls
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
    on_token_batch(b") x ", |mut cursor| {
        let result = SmtTermParser::<SmtSyntaxChecker>::default().parse(
            &mut SmtSyntaxChecker,
            &mut SmtParseState::new(),
            &mut cursor,
        );
        assert!(result.is_err(), "a closing parenthesis cannot start a term");
    });
}

#[test]
fn a_relex_request_fixes_the_cursor_at_the_consumed_position() {
    on_token_batch(b"(a b) ", |mut cursor| {
        cursor.advance(2);
        assert!(!cursor.relex_requested());
        cursor.relex();
        // nothing more comes out of the cursor, and the position stays
        assert!(cursor.relex_requested());
        assert!(cursor.is_empty());
        assert!(cursor.peek().is_none());
        assert!(cursor.get(0).is_none());
        assert!(cursor.next().is_none());
        cursor.advance(1);
        assert_eq!(cursor.consumed(), 2);
        assert_eq!(
            cursor.last_consumed().map(|token| token.content().to_vec()),
            Some(b"a".to_vec())
        );
    });
}

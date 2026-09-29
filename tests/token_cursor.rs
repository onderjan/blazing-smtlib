//! Tests of the token cursor and of the batch entry point of the category
//! parsers, `progress_all`, on the batches the lexer hands over.
//!
//! A batch can only come from the lexer, so every test lexes a small input
//! and runs its checks inside the handler, on each batch as it arrives.

use std::convert::Infallible;
use std::ops::ControlFlow;

use smt_parser_rs::{
    CheckStandardSyntax,
    read::{
        lexer::Lexer,
        parser::{CategoryParser, ParserResources, SortParser, TermParser},
    },
    token::{Token, TokenBatch, TokenBatchStop, TokenCursor, TokenHandler, TokenStop, TokenType},
};

/// A handler that runs a check on every batch it receives.
struct Probe<F>(F);

impl<F: FnMut(TokenBatch<'_>)> TokenHandler for Probe<F> {
    type Error = Infallible;

    fn handle_token(&mut self, _token: Token) -> Result<(), TokenStop<Infallible>> {
        panic!("test bug: the probe expects every hand-over through handle_tokens")
    }

    fn handle_tokens(&mut self, batch: TokenBatch<'_>) -> Result<(), TokenBatchStop<Infallible>> {
        (self.0)(batch);
        Ok(())
    }
}

/// Lexes the chunks and end of file, running the check on every batch.
fn on_batches(chunks: &[&[u8]], check: impl FnMut(TokenBatch<'_>)) {
    let mut lexer = Lexer::new(Probe(check));
    for chunk in chunks {
        lexer.lex_slice(chunk).expect("valid input must lex");
    }
    lexer.lex_eof().expect("valid input must lex");
}

/// The batches of the input as one slice: the tokens, then the end of file alone.
fn on_token_batch(input: &[u8], mut check: impl FnMut(TokenBatch<'_>)) {
    let mut seen = 0;
    on_batches(&[input], |batch| {
        if batch.get(0).map(|token| token.ty()) == Some(TokenType::EndOfFile) {
            return;
        }
        seen += 1;
        check(batch);
    });
    assert_eq!(
        seen, 1,
        "the input must arrive as one batch before the end of file"
    );
}

// --- The cursor ---

#[test]
fn cursor_walks_the_batch_in_order() {
    on_token_batch(b"(a b) c ", |batch| {
        assert_eq!(batch.len(), 5);
        let mut cursor = TokenCursor::new(batch);

        // at the start: nothing consumed, everything ahead
        assert_eq!(cursor.consumed(), 0);
        assert_eq!(batch.len() - cursor.consumed(), 5);
        assert!(!cursor.is_empty());
        assert_eq!(cursor.peek(), batch.get(0));
        assert_eq!(cursor.get(0), batch.get(0));
        assert_eq!(cursor.get(4), batch.get(4));
        assert_eq!(cursor.get(5), None);
        assert_eq!(cursor.last_consumed(), None);

        // one token taken
        let first = cursor.take().expect("a token");
        assert_eq!(first.ty(), TokenType::ParenOpen);
        assert_eq!(cursor.consumed(), 1);
        assert_eq!(batch.len() - cursor.consumed(), 4);
        assert_eq!(cursor.last_consumed(), Some(first));
        assert_eq!(cursor.peek(), batch.get(1));

        // two more at once: the lookback and lookahead move with them
        cursor.advance(2);
        assert_eq!(cursor.consumed(), 3);
        assert_eq!(batch.len() - cursor.consumed(), 2);
        assert_eq!(cursor.last_consumed(), batch.get(2));
        assert_eq!(cursor.get(0), batch.get(3));
        assert_eq!(cursor.get(1), batch.get(4));
        assert_eq!(cursor.get(2), None);

        // to the end and past it
        assert_eq!(
            cursor.take().map(|token| token.ty()),
            Some(TokenType::ParenClose)
        );
        assert_eq!(cursor.take().map(|token| token.content()), Some(&b"c"[..]));
        assert!(cursor.is_empty());
        assert_eq!(batch.len() - cursor.consumed(), 0);
        assert_eq!(cursor.consumed(), 5);
        assert_eq!(cursor.peek(), None);
        assert_eq!(cursor.take(), None);
        assert_eq!(cursor.consumed(), 5, "taking past the end consumes nothing");
        assert_eq!(cursor.last_consumed(), batch.get(4));
    });
}

#[test]
fn cursor_over_the_end_of_file_batch_yields_it_alone() {
    let mut batches = 0;
    on_batches(&[b"a "], |batch| {
        batches += 1;
        if batches == 2 {
            let mut cursor = TokenCursor::new(batch);
            assert_eq!(batch.len(), 1);
            assert_eq!(
                cursor.take().map(|token| token.ty()),
                Some(TokenType::EndOfFile)
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
    on_token_batch(b"(a b) c ", |batch| {
        let mut cursor = TokenCursor::new(batch);
        let mut ahead = cursor;
        ahead.advance(3);
        assert_eq!(cursor.consumed(), 0);
        assert_eq!(ahead.consumed(), 3);
        cursor.take();
        assert_eq!(ahead.consumed(), 3);
    });
}

#[test]
fn single_token_cursor_holds_that_token_alone() {
    on_token_batch(b"(a b) c ", |batch| {
        for index in 0..batch.len() {
            let token = batch.get(index).expect("a token of the batch");
            let mut cursor = TokenCursor::single(token);
            assert!(!cursor.is_empty());
            assert_eq!(cursor.peek(), Some(token));
            assert_eq!(cursor.get(1), None);
            assert_eq!(cursor.take(), Some(token));
            assert!(cursor.is_empty());
            assert_eq!(cursor.last_consumed(), Some(token));
        }
    });
}

#[test]
fn advancing_past_the_end_stops_at_the_end_like_take() {
    on_token_batch(b"a b ", |batch| {
        let mut cursor = TokenCursor::new(batch);
        cursor.advance(3);
        assert!(cursor.is_empty());
        assert_eq!(cursor.consumed(), 2);
        assert_eq!(cursor.last_consumed(), batch.get(1));
        cursor.advance(usize::MAX);
        assert_eq!(cursor.consumed(), 2);
    });
}

// --- The batch entry point of category parsers ---

/// Drives the parser through `progress_all` on the batches of the chunks,
/// returning per batch how many tokens it consumed and whether it finished.
fn drive<P: CategoryParser<CheckStandardSyntax> + Default>(chunks: &[&[u8]]) -> Vec<(usize, bool)> {
    let mut parser = P::default();
    let mut resources = ParserResources::new();
    let mut finished = false;
    let mut calls = Vec::new();
    on_batches(chunks, |batch| {
        if finished {
            return;
        }
        let mut cursor = TokenCursor::new(batch);
        let flow = parser
            .progress_all(&mut CheckStandardSyntax, &mut resources, &mut cursor)
            .expect("the category must parse");
        finished = matches!(flow, ControlFlow::Break(_));
        calls.push((cursor.consumed(), finished));
    });
    calls
}

#[test]
fn default_progress_all_stops_after_the_category_and_leaves_the_rest() {
    // the same property for a term and a sort: five tokens make the category,
    // the sixth is left in the cursor
    assert_eq!(drive::<TermParser<_>>(&[b"(f a b) x "]), [(5, true)]);
    assert_eq!(drive::<SortParser<_>>(&[b"(Array a b) x "]), [(5, true)]);
}

#[test]
fn default_progress_all_continues_across_batches() {
    // the category spans two batches: the first is consumed whole without a
    // result, the second finishes it after two tokens
    assert_eq!(
        drive::<TermParser<_>>(&[b"(f a ", b"b) x "]),
        [(3, false), (2, true)]
    );
    assert_eq!(
        drive::<SortParser<_>>(&[b"(Array a ", b"b) x "]),
        [(3, false), (2, true)]
    );
}

#[test]
fn default_progress_all_finishes_at_the_last_token_of_a_batch() {
    // the closing parenthesis is the batch's last token: finished, nothing left
    assert_eq!(drive::<TermParser<_>>(&[b"(f a b)", b" x "]), [(5, true)]);
}

#[test]
fn default_progress_all_reports_the_parser_error() {
    on_token_batch(b") x ", |batch| {
        let mut cursor = TokenCursor::new(batch);
        let result = TermParser::<CheckStandardSyntax>::default().progress_all(
            &mut CheckStandardSyntax,
            &mut ParserResources::new(),
            &mut cursor,
        );
        assert!(result.is_err(), "a closing parenthesis cannot start a term");
    });
}

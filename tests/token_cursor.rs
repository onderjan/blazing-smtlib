//! Tests of the token cursor and of the entry point of the category
//! parsers, `parse`, on the cursors the lexer hands over.
//!
//! A cursor over a batch can only come from the lexer, so every test lexes a
//! small input and runs its checks inside the handler, on each hand-over.

use std::convert::Infallible;
use std::ops::ControlFlow;

use smt_parser_rs::{
    CheckStandardSyntax,
    read::{
        lexer::Lexer,
        parser::{Parser, ParserResources, SortParser, TermParser},
    },
    token::{TokenCursor, TokenHandler, TokenType},
};

/// A handler that runs a check on a copy of every cursor it receives, then
/// consumes the hand-over.
struct Probe<F>(F);

impl<F: FnMut(TokenCursor<'_>)> TokenHandler for Probe<F> {
    type Error = Infallible;

    fn handle_tokens(&mut self, cursor: &mut TokenCursor<'_>) -> Result<(), Infallible> {
        (self.0)(*cursor);
        cursor.advance(usize::MAX);
        Ok(())
    }
}

/// Lexes the chunks and end of file, running the check on every hand-over.
fn on_batches(chunks: &[&[u8]], check: impl FnMut(TokenCursor<'_>)) {
    let mut lexer = Lexer::new(Probe(check));
    for chunk in chunks {
        lexer.lex_slice(chunk).expect("valid input must lex");
    }
    lexer.lex_eof().expect("valid input must lex");
}

/// The single hand-over of the input as one slice, before the end of file.
fn on_token_batch(input: &[u8], mut check: impl FnMut(TokenCursor<'_>)) {
    let mut seen = 0;
    on_batches(&[input], |cursor| {
        if cursor.peek().map(|token| token.ty()) == Some(TokenType::EndOfFile) {
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
fn len(cursor: TokenCursor<'_>) -> usize {
    let mut walk = cursor;
    let mut count = 0;
    while walk.take().is_some() {
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
        let first = cursor.take().expect("a token");
        assert_eq!(first.ty(), TokenType::ParenOpen);
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
            cursor.take().map(|token| token.ty()),
            Some(TokenType::ParenClose)
        );
        assert_eq!(cursor.take().map(|token| token.content()), Some(&b"c"[..]));
        assert!(cursor.is_empty());
        assert_eq!(cursor.consumed(), 5);
        assert_eq!(cursor.peek(), None);
        assert_eq!(cursor.take(), None);
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
    on_token_batch(b"(a b) c ", |start| {
        let mut cursor = start;
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
    on_token_batch(b"(a b) c ", |start| {
        let mut walk = start;
        while let Some(token) = walk.take() {
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
    on_token_batch(b"a b ", |start| {
        let mut cursor = start;
        cursor.advance(3);
        assert!(cursor.is_empty());
        assert_eq!(cursor.consumed(), 2);
        assert_eq!(cursor.last_consumed(), start.get(1));
        cursor.advance(usize::MAX);
        assert_eq!(cursor.consumed(), 2);
    });
}

// --- The batch entry point of category parsers ---

/// Drives the parser through `parse` on the hand-overs of the chunks,
/// returning per hand-over how many tokens it consumed and whether it finished.
fn drive<P: Parser<CheckStandardSyntax> + Default>(chunks: &[&[u8]]) -> Vec<(usize, bool)> {
    let mut parser = P::default();
    let mut resources = ParserResources::new();
    let mut finished = false;
    let mut calls = Vec::new();
    on_batches(chunks, |mut cursor| {
        if finished {
            return;
        }
        let flow = parser
            .parse(&mut CheckStandardSyntax, &mut resources, &mut cursor)
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
    assert_eq!(drive::<TermParser<_>>(&[b"(f a b) x "]), [(5, true)]);
    assert_eq!(drive::<SortParser<_>>(&[b"(Array a b) x "]), [(5, true)]);
}

#[test]
fn parse_continues_across_batches() {
    // the category spans two hand-overs: the first is consumed whole without a
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
fn parse_finishes_at_the_last_token_of_a_batch() {
    // the closing parenthesis is the hand-over's last token: finished, nothing left
    assert_eq!(drive::<TermParser<_>>(&[b"(f a b)", b" x "]), [(5, true)]);
}

#[test]
fn parse_reports_the_parser_error() {
    on_token_batch(b") x ", |mut cursor| {
        let result = TermParser::<CheckStandardSyntax>::default().parse(
            &mut CheckStandardSyntax,
            &mut ParserResources::new(),
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
        assert!(cursor.take().is_none());
        cursor.advance(1);
        assert_eq!(cursor.consumed(), 2);
        assert_eq!(
            cursor.last_consumed().map(|token| token.content().to_vec()),
            Some(b"a".to_vec())
        );
    });
}

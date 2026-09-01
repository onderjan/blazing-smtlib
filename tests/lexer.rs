//! Public-API tests of the lexer: error kinds and spans, token spans and
//! payloads, location tracking, handler errors, and misuse panics.

use std::convert::Infallible;

use smt_parser_rs::{
    SmtLocation, SmtSpan,
    read::lexer::{LexError, Lexer, LexerError, LexerErrorKind, TokenHandler},
    token::{Reserved, Token, TokenKind, TokenType},
};

/// An owned copy of a produced token, collected by [`CollectTokens`].
///
/// Borrowed tokens cannot outlive the lexer's buffer, so tests collect these instead.
#[derive(Debug)]
struct OwnedToken {
    ty: TokenType,
    content: Vec<u8>,
    span: SmtSpan,
}

/// A token handler that collects owned copies of all tokens for later inspection.
struct CollectTokens(Vec<OwnedToken>);

impl TokenHandler for CollectTokens {
    type Error = Infallible;

    fn handle_token(&mut self, token: Token) -> Result<(), Self::Error> {
        let content = match token.kind() {
            TokenKind::Symbol(s) => s.as_slice(),
            TokenKind::Keyword(k) => k.as_slice(),
            TokenKind::Numeral(n) => n.as_slice(),
            TokenKind::Decimal(d) => d.as_slice(),
            TokenKind::Hexadecimal(h) => h.as_slice(),
            TokenKind::Binary(b) => b.as_slice(),
            TokenKind::String(s) => s.as_slice(),
            _ => b"".as_slice(),
        };
        self.0.push(OwnedToken {
            ty: token.kind().ty(),
            content: content.to_vec(),
            span: token.span(),
        });
        Ok(())
    }
}

/// Extracts the lexer error from a lex error whose handler cannot fail.
fn into_lexer_error(err: LexError<Infallible>) -> LexerError {
    match err {
        LexError::Lexer(err) => err,
        LexError::Handler(never) => match never {},
    }
}

/// Lexes the whole input including EOF and returns all produced tokens.
fn lex_all(input: &[u8]) -> Result<Vec<OwnedToken>, LexerError> {
    let mut collected = CollectTokens(Vec::new());
    let mut lexer = Lexer::new(&mut collected);
    lexer.lex_all(input).map_err(into_lexer_error)?;
    drop(lexer);
    Ok(collected.0)
}

/// Expected location as `(offset, line, column)`.
type Loc = (u64, u64, u64);

fn loc(location: SmtLocation) -> Loc {
    (location.offset(), location.line(), location.column())
}

/// Lexes the input, requires an error of the given kind, and checks its span.
#[track_caller]
fn assert_error(input: &[u8], kind: LexerErrorKind, start: Loc, end: Loc) {
    let err = lex_all(input).expect_err("expected a lexer error, got tokens");
    assert_eq!(*err.kind(), kind);
    let span = err.span();
    assert_eq!(
        (loc(span.start()), loc(span.end())),
        (start, end),
        "span mismatch (start, end) as (offset, line, column)"
    );
}

#[test]
fn valid_input_has_no_error() {
    assert!(lex_all(b"").is_ok());
    assert!(lex_all(b"(set-logic QF_UF)\n(check-sat)\n").is_ok());
    assert!(lex_all(b"; comment only").is_ok());
    assert!(lex_all(b"7 7.0 #x1F #b10 \"s\" :kw |q s| sym").is_ok());
}

// --- Errors detected on a byte: span covers the token so far and the offending byte ---

#[test]
fn unexpected_character_is_single_byte() {
    // backslash is not allowed outside of string literals
    assert_error(
        b"\\",
        LexerErrorKind::UnexpectedCharacter,
        (0, 1, 1),
        (1, 1, 2),
    );
    // after other tokens, still just the one byte
    assert_error(
        b"(check-sat) \\",
        LexerErrorKind::UnexpectedCharacter,
        (12, 1, 13),
        (13, 1, 14),
    );
}

#[test]
fn fraction_digit_expected_on_byte() {
    // "7." followed by a space: the space is the byte where the error is detected
    assert_error(
        b"7. ",
        LexerErrorKind::FractionDigitExpected,
        (0, 1, 1),
        (3, 1, 4),
    );
}

#[test]
fn base_selection_expected() {
    assert_error(
        b"#q",
        LexerErrorKind::BaseSelectionExpected,
        (0, 1, 1),
        (2, 1, 3),
    );
}

#[test]
fn hexadecimal_digit_expected() {
    assert_error(
        b"#x ",
        LexerErrorKind::HexadecimalDigitExpected,
        (0, 1, 1),
        (3, 1, 4),
    );
}

#[test]
fn binary_digit_expected() {
    assert_error(
        b"#b)",
        LexerErrorKind::BinaryDigitExpected,
        (0, 1, 1),
        (3, 1, 4),
    );
}

#[test]
fn numeral_leading_zero() {
    assert_error(
        b"01",
        LexerErrorKind::NumeralLeadingZero,
        (0, 1, 1),
        (2, 1, 3),
    );
}

#[test]
fn keyword_name_expected() {
    assert_error(
        b": ",
        LexerErrorKind::ForbiddenKeywordName,
        (0, 1, 1),
        (2, 1, 3),
    );
}

#[test]
fn keyword_leading_digit() {
    assert_error(
        b":0",
        LexerErrorKind::ForbiddenKeywordName,
        (0, 1, 1),
        (2, 1, 3),
    );
    // the leading digit is rejected even when more characters would follow
    assert_error(
        b":0abc",
        LexerErrorKind::ForbiddenKeywordName,
        (0, 1, 1),
        (2, 1, 3),
    );
}

#[test]
fn keyword_reserved() {
    assert_error(
        b":let ",
        LexerErrorKind::KeywordReserved,
        (0, 1, 1),
        (5, 1, 6),
    );
}

#[test]
fn backslash_in_quoted_symbol() {
    assert_error(
        b"|a\\b|",
        LexerErrorKind::BackslashInQuotedSymbol,
        (0, 1, 1),
        (3, 1, 4),
    );
}

#[test]
fn forbidden_char_in_string() {
    assert_error(
        b"\"a\x01b\"",
        LexerErrorKind::ForbiddenCharInString,
        (0, 1, 1),
        (3, 1, 4),
    );
}

#[test]
fn forbidden_char_in_quoted_symbol() {
    assert_error(
        b"|a\x7fb|",
        LexerErrorKind::ForbiddenCharInQuotedSymbol,
        (0, 1, 1),
        (3, 1, 4),
    );
}

// --- Errors detected at EOF: span must end exactly at the input length, not past it ---

#[test]
fn fraction_digit_expected_at_eof() {
    assert_error(
        b"7.",
        LexerErrorKind::FractionDigitExpected,
        (0, 1, 1),
        (2, 1, 3),
    );
}

#[test]
fn hexadecimal_digit_expected_at_eof() {
    assert_error(
        b"#x",
        LexerErrorKind::HexadecimalDigitExpected,
        (0, 1, 1),
        (2, 1, 3),
    );
}

#[test]
fn base_selection_expected_at_eof() {
    assert_error(
        b"#",
        LexerErrorKind::BaseSelectionExpected,
        (0, 1, 1),
        (1, 1, 2),
    );
}

#[test]
fn keyword_name_expected_at_eof() {
    assert_error(
        b":",
        LexerErrorKind::ForbiddenKeywordName,
        (0, 1, 1),
        (1, 1, 2),
    );
}

#[test]
fn unclosed_string_literal_at_eof() {
    assert_error(
        b"\"abc",
        LexerErrorKind::UnclosedStringLiteral,
        (0, 1, 1),
        (4, 1, 5),
    );
}

#[test]
fn unclosed_quoted_symbol_at_eof() {
    assert_error(
        b"|abc",
        LexerErrorKind::UnclosedQuotedSymbol,
        (0, 1, 1),
        (4, 1, 5),
    );
}

// --- Line and column tracking ---

#[test]
fn error_on_later_line() {
    // the string literal starts on line 3, column 3 (offset 15) and is unclosed at EOF
    assert_error(
        b"(check-sat)\n\n  \"abc",
        LexerErrorKind::UnclosedStringLiteral,
        (15, 3, 3),
        (19, 3, 7),
    );
}

#[test]
fn error_spanning_lines() {
    // an unclosed quoted symbol may contain newlines; the end is on a later line
    assert_error(
        b"|ab\ncd",
        LexerErrorKind::UnclosedQuotedSymbol,
        (0, 1, 1),
        (6, 2, 3),
    );
}

#[test]
fn crlf_counts_as_one_line() {
    // CR must not start a new line, so "01" is on line 2, column 1
    assert_error(
        b"(check-sat)\r\n01",
        LexerErrorKind::NumeralLeadingZero,
        (13, 2, 1),
        (15, 2, 3),
    );
}

#[test]
fn error_after_comment_line() {
    assert_error(
        b"; a comment\n\\",
        LexerErrorKind::UnexpectedCharacter,
        (12, 2, 1),
        (13, 2, 2),
    );
}

// --- Token spans and current location ---

#[test]
fn current_location_follows_consumed_bytes() {
    let mut collected = CollectTokens(Vec::new());
    let mut lexer = Lexer::new(&mut collected);
    assert_eq!(loc(lexer.current_location()), (0, 1, 1));
    for &c in b"ab\nc" {
        lexer
            .lex_next(c)
            .map_err(into_lexer_error)
            .expect("valid input");
    }
    assert_eq!(loc(lexer.current_location()), (4, 2, 2));
}

/// Expected token as `(type, start, end)`, with the locations as `(offset, line, column)`.
type TokenLoc = (TokenType, Loc, Loc);

/// Lexes the whole input and describes every token by its type and its span.
fn token_spans(input: &[u8]) -> Vec<TokenLoc> {
    lex_all(input)
        .expect("test input must lex")
        .iter()
        .map(|token| (token.ty, loc(token.span.start()), loc(token.span.end())))
        .collect()
}

#[test]
fn spans_on_a_single_line() {
    // columns are one-based and counted in bytes
    assert_eq!(
        token_spans(b"(a 12)"),
        vec![
            (TokenType::ParenOpen, (0, 1, 1), (1, 1, 2)),
            (TokenType::Symbol, (1, 1, 2), (2, 1, 3)),
            (TokenType::Numeral, (3, 1, 4), (5, 1, 6)),
            (TokenType::ParenClose, (5, 1, 6), (6, 1, 7)),
            (TokenType::EndOfFile, (6, 1, 7), (6, 1, 7)),
        ]
    );
}

#[test]
fn spans_restart_the_column_on_every_line() {
    assert_eq!(
        token_spans(b"(a)\n(b)"),
        vec![
            (TokenType::ParenOpen, (0, 1, 1), (1, 1, 2)),
            (TokenType::Symbol, (1, 1, 2), (2, 1, 3)),
            (TokenType::ParenClose, (2, 1, 3), (3, 1, 4)),
            (TokenType::ParenOpen, (4, 2, 1), (5, 2, 2)),
            (TokenType::Symbol, (5, 2, 2), (6, 2, 3)),
            (TokenType::ParenClose, (6, 2, 3), (7, 2, 4)),
            (TokenType::EndOfFile, (7, 2, 4), (7, 2, 4)),
        ]
    );
}

#[test]
fn span_end_is_one_past_the_last_byte_of_the_token() {
    // `ab` is terminated by the line break, but its end stays on the first line,
    // one column past the `b`, rather than moving to the start of the second line
    assert_eq!(
        token_spans(b"ab\ncd"),
        vec![
            (TokenType::Symbol, (0, 1, 1), (2, 1, 3)),
            (TokenType::Symbol, (3, 2, 1), (5, 2, 3)),
            (TokenType::EndOfFile, (5, 2, 3), (5, 2, 3)),
        ]
    );
}

#[test]
fn quoted_symbol_may_span_a_line_break() {
    // the token starts on the first line and ends on the second one,
    // and the line break inside it still counts for the tokens that follow
    assert_eq!(
        token_spans(b"|a\nb| c"),
        vec![
            (TokenType::Symbol, (0, 1, 1), (5, 2, 3)),
            (TokenType::Symbol, (6, 2, 4), (7, 2, 5)),
            (TokenType::EndOfFile, (7, 2, 5), (7, 2, 5)),
        ]
    );
}

#[test]
fn string_literal_may_span_a_line_break() {
    assert_eq!(
        token_spans(b"\"a\nb\""),
        vec![
            (TokenType::String, (0, 1, 1), (5, 2, 3)),
            (TokenType::EndOfFile, (5, 2, 3), (5, 2, 3)),
        ]
    );
}

#[test]
fn end_of_file_token_location() {
    // an empty input consists of the end-of-file token alone, at the stream start
    assert_eq!(
        token_spans(b""),
        vec![(TokenType::EndOfFile, (0, 1, 1), (0, 1, 1))]
    );
    // without a trailing line break, the end-of-file token is just past the last token
    assert_eq!(
        token_spans(b"(a)"),
        vec![
            (TokenType::ParenOpen, (0, 1, 1), (1, 1, 2)),
            (TokenType::Symbol, (1, 1, 2), (2, 1, 3)),
            (TokenType::ParenClose, (2, 1, 3), (3, 1, 4)),
            (TokenType::EndOfFile, (3, 1, 4), (3, 1, 4)),
        ]
    );
    // with one, its offset is exactly the start of the next line,
    // so it is reported at the first column of that line rather than past the end
    // of the previous one
    assert_eq!(
        token_spans(b"(a)\n"),
        vec![
            (TokenType::ParenOpen, (0, 1, 1), (1, 1, 2)),
            (TokenType::Symbol, (1, 1, 2), (2, 1, 3)),
            (TokenType::ParenClose, (2, 1, 3), (3, 1, 4)),
            (TokenType::EndOfFile, (4, 2, 1), (4, 2, 1)),
        ]
    );
}

#[test]
fn crlf_is_a_single_line_break_in_token_spans() {
    // CR terminates the symbol but must not start a line of its own
    assert_eq!(
        token_spans(b"a\r\nb"),
        vec![
            (TokenType::Symbol, (0, 1, 1), (1, 1, 2)),
            (TokenType::Symbol, (3, 2, 1), (4, 2, 2)),
            (TokenType::EndOfFile, (4, 2, 2), (4, 2, 2)),
        ]
    );
}

#[test]
fn comments_produce_no_tokens_but_still_count_lines() {
    assert_eq!(
        token_spans(b"; c\nx"),
        vec![
            (TokenType::Symbol, (4, 2, 1), (5, 2, 2)),
            (TokenType::EndOfFile, (5, 2, 2), (5, 2, 2)),
        ]
    );
}

#[test]
fn keyword_may_contain_digits_after_the_first_character() {
    // only the leading digit is forbidden; later ones are ordinary keyword characters
    assert_eq!(
        token_spans(b":a0 :x1y2"),
        vec![
            (TokenType::Keyword, (0, 1, 1), (3, 1, 4)),
            (TokenType::Keyword, (4, 1, 5), (9, 1, 10)),
            (TokenType::EndOfFile, (9, 1, 10), (9, 1, 10)),
        ]
    );
}

#[test]
fn spans_of_every_token_type() {
    // the hash of a hexadecimal or binary literal belongs to its token,
    // and a reserved word spans the same bytes an ordinary symbol would
    assert_eq!(
        token_spans(b":kw #xAB #b01 1.5 \"s\" let"),
        vec![
            (TokenType::Keyword, (0, 1, 1), (3, 1, 4)),
            (TokenType::Hexadecimal, (4, 1, 5), (8, 1, 9)),
            (TokenType::Binary, (9, 1, 10), (13, 1, 14)),
            (TokenType::Decimal, (14, 1, 15), (17, 1, 18)),
            (TokenType::String, (18, 1, 19), (21, 1, 22)),
            (TokenType::Reserved(Reserved::Let), (22, 1, 23), (25, 1, 26)),
            (TokenType::EndOfFile, (25, 1, 26), (25, 1, 26)),
        ]
    );
}

#[test]
fn decimal_token_payload_is_the_verbatim_source() {
    // the payload keeps the source bytes including the dot,
    // fractional leading zeros, and trailing zeros
    let tokens = lex_all(b"7.5 1.05 3.500 0.0").expect("valid input");
    let decimals: Vec<Vec<u8>> = tokens
        .iter()
        .filter(|token| token.ty == TokenType::Decimal)
        .map(|token| token.content.clone())
        .collect();
    assert_eq!(
        decimals,
        vec![
            b"7.5".as_slice(),
            b"1.05".as_slice(),
            b"3.500".as_slice(),
            b"0.0".as_slice(),
        ]
    );
}

/// Lexes the whole input and describes every token by its type and payload,
/// with an empty payload for the token types that have none.
fn token_payloads(input: &[u8]) -> Vec<(TokenType, Vec<u8>)> {
    lex_all(input)
        .expect("test input must lex")
        .iter()
        .map(|token| (token.ty, token.content.clone()))
        .collect()
}

#[test]
fn token_payloads_are_not_contaminated_by_previous_tokens() {
    // every payload-carrying kind in a row; each token is shorter than
    // the one before it, so any missed buffer clear shows up as leftover
    // bytes, and the reserved word fills the buffer without emitting it
    assert_eq!(
        token_payloads(b"abcd let e :k1 \"s\" |q| 12 3.4 #xA #b0"),
        vec![
            (TokenType::Symbol, b"abcd".to_vec()),
            (TokenType::Reserved(Reserved::Let), vec![]),
            (TokenType::Symbol, b"e".to_vec()),
            (TokenType::Keyword, b"k1".to_vec()),
            (TokenType::String, b"s".to_vec()),
            (TokenType::Symbol, b"q".to_vec()),
            (TokenType::Numeral, b"12".to_vec()),
            (TokenType::Decimal, b"3.4".to_vec()),
            (TokenType::Hexadecimal, b"A".to_vec()),
            (TokenType::Binary, b"0".to_vec()),
            (TokenType::EndOfFile, vec![]),
        ]
    );
}

#[test]
fn empty_payloads_follow_nonempty_ones() {
    // the empty quoted symbol and string literal must not inherit
    // the content of the tokens lexed before them
    assert_eq!(
        token_payloads(b"|abc| || \"xy\" \"\" :a"),
        vec![
            (TokenType::Symbol, b"abc".to_vec()),
            (TokenType::Symbol, vec![]),
            (TokenType::String, b"xy".to_vec()),
            (TokenType::String, vec![]),
            (TokenType::Keyword, b"a".to_vec()),
            (TokenType::EndOfFile, vec![]),
        ]
    );
}

#[test]
fn string_double_quote_escape_is_a_single_quote_in_the_payload() {
    assert_eq!(
        token_payloads(b"\"a\"\"b\" \"\"\"\""),
        vec![
            (TokenType::String, b"a\"b".to_vec()),
            (TokenType::String, b"\"".to_vec()),
            (TokenType::EndOfFile, vec![]),
        ]
    );
}

// --- Handler errors ---

/// A token handler that rejects every token, returning its span.
struct RejectTokens;

impl TokenHandler for RejectTokens {
    type Error = SmtSpan;

    fn handle_token(&mut self, token: Token) -> Result<(), Self::Error> {
        Err(token.span())
    }
}

#[test]
fn handler_error_is_returned_with_the_handled_token() {
    let mut lexer = Lexer::new(RejectTokens);
    // the parenthesis token is produced and handed to the handler immediately
    let Err(LexError::Handler(span)) = lexer.lex_next(b'(') else {
        panic!("expected a handler error");
    };
    assert_eq!((loc(span.start()), loc(span.end())), ((0, 1, 1), (1, 1, 2)));
}

// --- Lexer misuse panics ---

#[test]
#[should_panic(expected = "cannot lex after a lexer error")]
fn lexing_after_an_error_panics() {
    let mut collected = CollectTokens(Vec::new());
    let mut lexer = Lexer::new(&mut collected);
    lexer
        .lex_next(b'7')
        .map_err(into_lexer_error)
        .expect("valid input");
    // the backslash raises an error just after the numeral token was produced
    assert!(lexer.lex_next(b'\\').is_err(), "expected a lexer error");
    let _ = lexer.lex_next(b' ');
}

#[test]
#[should_panic(expected = "cannot lex after a lexer error")]
fn lexing_after_a_handler_error_panics() {
    // a handler error also makes the lexer unusable
    let mut lexer = Lexer::new(RejectTokens);
    assert!(lexer.lex_next(b'(').is_err(), "expected a handler error");
    let _ = lexer.lex_next(b'a');
}

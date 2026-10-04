//! Public-API tests of the lexer: error kinds and spans, token spans and
//! payloads, location tracking, handler errors, and misuse panics.

mod lex_backend;

use std::convert::Infallible;
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtSpan,
    lexer::{SmtLexError, SmtLexer, SmtLexicalError, SmtLexicalErrorKind},
    token::{
        SmtBatchCursor, SmtConsume, SmtGeneralReserved, SmtReserved, SmtTokenCategory, SmtVersion,
    },
};

use lex_backend::{Feed, LexedError, LexedToken, Loc, loc};

/// A token consumer that takes every token and keeps nothing, for the tests
/// that drive the Rust lexer directly.
struct TakeTokens;

impl SmtConsume for TakeTokens {
    type Result = ();
    type Error = Infallible;

    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        cursor.consume_all();
        Ok(ControlFlow::Continue(()))
    }
}

/// Extracts the lexer error from a lex error whose handler cannot fail.
fn into_lexer_error(err: SmtLexError<Infallible>) -> SmtLexicalError {
    match err {
        SmtLexError::Lexical(err) => err,
        SmtLexError::Consumer(never) => match never {},
    }
}

/// Lexes the whole input including EOF with the lexer under test and returns
/// all produced tokens.
fn lex_all(input: &[u8]) -> Result<Vec<LexedToken>, LexedError> {
    let lexed = lex_backend::lex_whole(SmtVersion::V2_7, input);
    match lexed.error {
        Some(err) => Err(err),
        None => Ok(lexed.tokens),
    }
}

/// Lexes the input, requires an error of the given kind, and checks its span.
#[track_caller]
fn assert_error(input: &[u8], kind: SmtLexicalErrorKind, start: Loc, end: Loc) {
    let err = lex_all(input).expect_err("expected a lexer error, got tokens");
    assert_eq!(err.kind, kind);
    assert_eq!(
        (err.start, err.end),
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
        SmtLexicalErrorKind::UnexpectedCharacter,
        (0, 0, 0),
        (1, 0, 1),
    );
    // after other tokens, still just the one byte
    assert_error(
        b"(check-sat) \\",
        SmtLexicalErrorKind::UnexpectedCharacter,
        (12, 0, 12),
        (13, 0, 13),
    );
}

#[test]
fn fraction_digit_expected_on_byte() {
    // "7." followed by a space: the space is the byte where the error is detected
    assert_error(
        b"7. ",
        SmtLexicalErrorKind::FractionDigitExpected,
        (0, 0, 0),
        (3, 0, 3),
    );
}

#[test]
fn base_selection_expected() {
    assert_error(
        b"#q",
        SmtLexicalErrorKind::BaseSelectionExpected,
        (0, 0, 0),
        (2, 0, 2),
    );
}

#[test]
fn hexadecimal_digit_expected() {
    assert_error(
        b"#x ",
        SmtLexicalErrorKind::HexadecimalDigitExpected,
        (0, 0, 0),
        (3, 0, 3),
    );
}

#[test]
fn binary_digit_expected() {
    assert_error(
        b"#b)",
        SmtLexicalErrorKind::BinaryDigitExpected,
        (0, 0, 0),
        (3, 0, 3),
    );
}

#[test]
fn numeral_leading_zero() {
    assert_error(
        b"01",
        SmtLexicalErrorKind::NumeralLeadingZero,
        (0, 0, 0),
        (2, 0, 2),
    );
}

#[test]
fn keyword_name_expected() {
    assert_error(
        b": ",
        SmtLexicalErrorKind::ForbiddenKeywordName,
        (0, 0, 0),
        (2, 0, 2),
    );
}

#[test]
fn keyword_leading_digit() {
    assert_error(
        b":0",
        SmtLexicalErrorKind::ForbiddenKeywordName,
        (0, 0, 0),
        (2, 0, 2),
    );
    // the leading digit is rejected even when more characters would follow
    assert_error(
        b":0abc",
        SmtLexicalErrorKind::ForbiddenKeywordName,
        (0, 0, 0),
        (2, 0, 2),
    );
}

#[test]
fn keyword_spelled_like_a_reserved_word_is_a_keyword() {
    // reserved words are only recognized in symbols, so this is no error
    let tokens = lex_all(b":let ").expect("a keyword spelled like a reserved word must lex");
    assert_eq!(tokens[0].ty, SmtTokenCategory::Keyword);
    assert_eq!(tokens[0].content, b"let");
    assert_eq!(tokens[0].reserved(), None);
}

#[test]
fn backslash_in_quoted_symbol() {
    assert_error(
        b"|a\\b|",
        SmtLexicalErrorKind::BackslashInQuotedSymbol,
        (0, 0, 0),
        (3, 0, 3),
    );
}

#[test]
fn forbidden_char_in_string() {
    assert_error(
        b"\"a\x01b\"",
        SmtLexicalErrorKind::ForbiddenCharInString,
        (0, 0, 0),
        (3, 0, 3),
    );
}

#[test]
fn forbidden_char_in_quoted_symbol() {
    assert_error(
        b"|a\x7fb|",
        SmtLexicalErrorKind::ForbiddenCharInQuotedSymbol,
        (0, 0, 0),
        (3, 0, 3),
    );
}

// --- Errors detected at EOF: span must end exactly at the input length, not past it ---

#[test]
fn fraction_digit_expected_at_eof() {
    assert_error(
        b"7.",
        SmtLexicalErrorKind::FractionDigitExpected,
        (0, 0, 0),
        (2, 0, 2),
    );
}

#[test]
fn hexadecimal_digit_expected_at_eof() {
    assert_error(
        b"#x",
        SmtLexicalErrorKind::HexadecimalDigitExpected,
        (0, 0, 0),
        (2, 0, 2),
    );
}

#[test]
fn base_selection_expected_at_eof() {
    assert_error(
        b"#",
        SmtLexicalErrorKind::BaseSelectionExpected,
        (0, 0, 0),
        (1, 0, 1),
    );
}

#[test]
fn keyword_name_expected_at_eof() {
    assert_error(
        b":",
        SmtLexicalErrorKind::ForbiddenKeywordName,
        (0, 0, 0),
        (1, 0, 1),
    );
}

#[test]
fn unclosed_string_literal_at_eof() {
    assert_error(
        b"\"abc",
        SmtLexicalErrorKind::UnclosedStringLiteral,
        (0, 0, 0),
        (4, 0, 4),
    );
}

#[test]
fn unclosed_quoted_symbol_at_eof() {
    assert_error(
        b"|abc",
        SmtLexicalErrorKind::UnclosedQuotedSymbol,
        (0, 0, 0),
        (4, 0, 4),
    );
}

// --- Line and column tracking ---

#[test]
fn error_on_later_line() {
    // the string literal starts at offset 15, zero-based line 2, column 2, and is unclosed at EOF
    assert_error(
        b"(check-sat)\n\n  \"abc",
        SmtLexicalErrorKind::UnclosedStringLiteral,
        (15, 2, 2),
        (19, 2, 6),
    );
}

#[test]
fn error_spanning_lines() {
    // an unclosed quoted symbol may contain newlines; the end is on a later line
    assert_error(
        b"|ab\ncd",
        SmtLexicalErrorKind::UnclosedQuotedSymbol,
        (0, 0, 0),
        (6, 1, 2),
    );
}

#[test]
fn crlf_counts_as_one_line() {
    // CR must not start a new line, so "01" is on zero-based line 1, column 0
    assert_error(
        b"(check-sat)\r\n01",
        SmtLexicalErrorKind::NumeralLeadingZero,
        (13, 1, 0),
        (15, 1, 2),
    );
}

#[test]
fn error_after_comment_line() {
    assert_error(
        b"; a comment\n\\",
        SmtLexicalErrorKind::UnexpectedCharacter,
        (12, 1, 0),
        (13, 1, 1),
    );
}

// --- Token spans and current location ---

#[test]
fn current_location_follows_consumed_bytes() {
    let mut lexer = SmtLexer::new(TakeTokens, SmtVersion::V2_7);
    assert_eq!(loc(lexer.current_location()), (0, 0, 0));
    for &c in b"ab\nc" {
        let _ = lexer
            .lex_slice(&[c])
            .map_err(into_lexer_error)
            .expect("valid input");
    }
    assert_eq!(loc(lexer.current_location()), (4, 1, 1));
}

/// Expected token as `(type, start, end)`, with the locations as `(offset, line, column)`.
type TokenLoc = (SmtTokenCategory, Loc, Loc);

/// Lexes the whole input and describes every token by its type and its span.
fn token_spans(input: &[u8]) -> Vec<TokenLoc> {
    lex_all(input)
        .expect("test input must lex")
        .iter()
        .map(|token| (token.ty, token.start, token.end))
        .collect()
}

#[test]
fn spans_on_a_single_line() {
    // lines and columns are zero-based, columns counted in bytes
    assert_eq!(
        token_spans(b"(a 12)"),
        vec![
            (SmtTokenCategory::ParenOpen, (0, 0, 0), (1, 0, 1)),
            (SmtTokenCategory::UnquotedSymbol, (1, 0, 1), (2, 0, 2)),
            (SmtTokenCategory::Numeral, (3, 0, 3), (5, 0, 5)),
            (SmtTokenCategory::ParenClose, (5, 0, 5), (6, 0, 6)),
            (SmtTokenCategory::EndOfFile, (6, 0, 6), (6, 0, 6)),
        ]
    );
}

#[test]
fn spans_restart_the_column_on_every_line() {
    assert_eq!(
        token_spans(b"(a)\n(b)"),
        vec![
            (SmtTokenCategory::ParenOpen, (0, 0, 0), (1, 0, 1)),
            (SmtTokenCategory::UnquotedSymbol, (1, 0, 1), (2, 0, 2)),
            (SmtTokenCategory::ParenClose, (2, 0, 2), (3, 0, 3)),
            (SmtTokenCategory::ParenOpen, (4, 1, 0), (5, 1, 1)),
            (SmtTokenCategory::UnquotedSymbol, (5, 1, 1), (6, 1, 2)),
            (SmtTokenCategory::ParenClose, (6, 1, 2), (7, 1, 3)),
            (SmtTokenCategory::EndOfFile, (7, 1, 3), (7, 1, 3)),
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
            (SmtTokenCategory::UnquotedSymbol, (0, 0, 0), (2, 0, 2)),
            (SmtTokenCategory::UnquotedSymbol, (3, 1, 0), (5, 1, 2)),
            (SmtTokenCategory::EndOfFile, (5, 1, 2), (5, 1, 2)),
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
            (SmtTokenCategory::QuotedSymbol, (0, 0, 0), (5, 1, 2)),
            (SmtTokenCategory::UnquotedSymbol, (6, 1, 3), (7, 1, 4)),
            (SmtTokenCategory::EndOfFile, (7, 1, 4), (7, 1, 4)),
        ]
    );
}

#[test]
fn string_literal_may_span_a_line_break() {
    assert_eq!(
        token_spans(b"\"a\nb\""),
        vec![
            (SmtTokenCategory::String, (0, 0, 0), (5, 1, 2)),
            (SmtTokenCategory::EndOfFile, (5, 1, 2), (5, 1, 2)),
        ]
    );
}

#[test]
fn end_of_file_token_location() {
    // an empty input consists of the end-of-file token alone, at the stream start
    assert_eq!(
        token_spans(b""),
        vec![(SmtTokenCategory::EndOfFile, (0, 0, 0), (0, 0, 0))]
    );
    // without a trailing line break, the end-of-file token is just past the last token
    assert_eq!(
        token_spans(b"(a)"),
        vec![
            (SmtTokenCategory::ParenOpen, (0, 0, 0), (1, 0, 1)),
            (SmtTokenCategory::UnquotedSymbol, (1, 0, 1), (2, 0, 2)),
            (SmtTokenCategory::ParenClose, (2, 0, 2), (3, 0, 3)),
            (SmtTokenCategory::EndOfFile, (3, 0, 3), (3, 0, 3)),
        ]
    );
    // with one, its offset is exactly the start of the next line,
    // so it is reported at the first column of that line rather than past the end
    // of the previous one
    assert_eq!(
        token_spans(b"(a)\n"),
        vec![
            (SmtTokenCategory::ParenOpen, (0, 0, 0), (1, 0, 1)),
            (SmtTokenCategory::UnquotedSymbol, (1, 0, 1), (2, 0, 2)),
            (SmtTokenCategory::ParenClose, (2, 0, 2), (3, 0, 3)),
            (SmtTokenCategory::EndOfFile, (4, 1, 0), (4, 1, 0)),
        ]
    );
}

#[test]
fn crlf_is_a_single_line_break_in_token_spans() {
    // CR terminates the symbol but must not start a line of its own
    assert_eq!(
        token_spans(b"a\r\nb"),
        vec![
            (SmtTokenCategory::UnquotedSymbol, (0, 0, 0), (1, 0, 1)),
            (SmtTokenCategory::UnquotedSymbol, (3, 1, 0), (4, 1, 1)),
            (SmtTokenCategory::EndOfFile, (4, 1, 1), (4, 1, 1)),
        ]
    );
}

#[test]
fn comments_produce_no_tokens_but_still_count_lines() {
    assert_eq!(
        token_spans(b"; c\nx"),
        vec![
            (SmtTokenCategory::UnquotedSymbol, (4, 1, 0), (5, 1, 1)),
            (SmtTokenCategory::EndOfFile, (5, 1, 1), (5, 1, 1)),
        ]
    );
}

#[test]
fn keyword_may_contain_digits_after_the_first_character() {
    // only the leading digit is forbidden; later ones are ordinary keyword characters
    assert_eq!(
        token_spans(b":a0 :x1y2"),
        vec![
            (SmtTokenCategory::Keyword, (0, 0, 0), (3, 0, 3)),
            (SmtTokenCategory::Keyword, (4, 0, 4), (9, 0, 9)),
            (SmtTokenCategory::EndOfFile, (9, 0, 9), (9, 0, 9)),
        ]
    );
}

#[test]
fn spans_of_every_token_type() {
    // the hash of a hexadecimal or binary literal belongs to its token,
    // a reserved word spans the same bytes an ordinary symbol would,
    // and the pipes of a quoted symbol belong to its token
    assert_eq!(
        token_spans(b":kw #xAB #b01 1.5 \"s\" let |q|"),
        vec![
            (SmtTokenCategory::Keyword, (0, 0, 0), (3, 0, 3)),
            (SmtTokenCategory::Hexadecimal, (4, 0, 4), (8, 0, 8)),
            (SmtTokenCategory::Binary, (9, 0, 9), (13, 0, 13)),
            (SmtTokenCategory::Decimal, (14, 0, 14), (17, 0, 17)),
            (SmtTokenCategory::String, (18, 0, 18), (21, 0, 21)),
            (SmtTokenCategory::UnquotedSymbol, (22, 0, 22), (25, 0, 25)),
            (SmtTokenCategory::QuotedSymbol, (26, 0, 26), (29, 0, 29)),
            (SmtTokenCategory::EndOfFile, (29, 0, 29), (29, 0, 29)),
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
        .filter(|token| token.ty == SmtTokenCategory::Decimal)
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
fn token_payloads(input: &[u8]) -> Vec<(SmtTokenCategory, Vec<u8>)> {
    lex_all(input)
        .expect("test input must lex")
        .iter()
        .map(|token| (token.ty, token.content.clone()))
        .collect()
}

#[test]
fn token_payloads_are_not_contaminated_by_previous_tokens() {
    // every payload-carrying kind in a row; each token is shorter than
    // the one before it, so any missed buffer clear shows up as leftover bytes
    assert_eq!(
        token_payloads(b"abcd let e :k1 \"s\" |q| 12 3.4 #xA #b0"),
        vec![
            (SmtTokenCategory::UnquotedSymbol, b"abcd".to_vec()),
            (SmtTokenCategory::UnquotedSymbol, b"let".to_vec()),
            (SmtTokenCategory::UnquotedSymbol, b"e".to_vec()),
            (SmtTokenCategory::Keyword, b"k1".to_vec()),
            (SmtTokenCategory::String, b"s".to_vec()),
            (SmtTokenCategory::QuotedSymbol, b"q".to_vec()),
            (SmtTokenCategory::Numeral, b"12".to_vec()),
            (SmtTokenCategory::Decimal, b"3.4".to_vec()),
            (SmtTokenCategory::Hexadecimal, b"A".to_vec()),
            (SmtTokenCategory::Binary, b"0".to_vec()),
            (SmtTokenCategory::EndOfFile, vec![]),
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
            (SmtTokenCategory::QuotedSymbol, b"abc".to_vec()),
            (SmtTokenCategory::QuotedSymbol, vec![]),
            (SmtTokenCategory::String, b"xy".to_vec()),
            (SmtTokenCategory::String, vec![]),
            (SmtTokenCategory::Keyword, b"a".to_vec()),
            (SmtTokenCategory::EndOfFile, vec![]),
        ]
    );
}

#[test]
fn string_double_quote_escape_is_a_single_quote_in_the_payload() {
    assert_eq!(
        token_payloads(b"\"a\"\"b\" \"\"\"\""),
        vec![
            (SmtTokenCategory::String, b"a\"b".to_vec()),
            (SmtTokenCategory::String, b"\"".to_vec()),
            (SmtTokenCategory::EndOfFile, vec![]),
        ]
    );
}

// --- Handler errors ---

/// A token consumer that rejects every token, returning its span.
struct RejectTokens;

impl SmtConsume for RejectTokens {
    type Result = ();
    type Error = SmtSpan;

    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        match cursor.next() {
            Some(token) => Err(token.span()),
            None => Ok(ControlFlow::Continue(())),
        }
    }
}

#[test]
fn handler_error_is_returned_with_the_handled_token() {
    let mut lexer = SmtLexer::new(RejectTokens, SmtVersion::V2_7);
    // the parenthesis token is produced and handed to the handler immediately
    let Err(SmtLexError::Consumer(span)) = lexer.lex_slice(b"(") else {
        panic!("expected a handler error");
    };
    assert_eq!((loc(span.start()), loc(span.end())), ((0, 0, 0), (1, 0, 1)));
}

// --- Lexer misuse panics ---

#[test]
#[should_panic(expected = "cannot lex after a lexer error")]
fn lexing_after_an_error_panics() {
    let mut lexer = SmtLexer::new(TakeTokens, SmtVersion::V2_7);
    let _ = lexer
        .lex_slice(b"7")
        .map_err(into_lexer_error)
        .expect("valid input");
    // the backslash raises an error just after the numeral token was produced
    assert!(lexer.lex_slice(b"\\").is_err(), "expected a lexer error");
    let _ = lexer.lex_slice(b" ");
}

#[test]
#[should_panic(expected = "cannot lex after a lexer error")]
fn lexing_after_a_handler_error_panics() {
    // a handler error also makes the lexer unusable
    let mut lexer = SmtLexer::new(RejectTokens, SmtVersion::V2_7);
    assert!(lexer.lex_slice(b"(").is_err(), "expected a handler error");
    let _ = lexer.lex_slice(b"a");
}

// --- Reserved words against similar symbols ---
//
// The lexer produces every symbol alike; the reserved words are recognized
// when the token is classified, from its content.

/// Every token of the input as its type and the reserved word it is
/// classified as, in order.
fn token_classes(input: &[u8]) -> Vec<(SmtTokenCategory, Option<SmtReserved>)> {
    lex_all(input)
        .expect("test input must lex")
        .iter()
        .map(|token| (token.ty, token.reserved()))
        .collect()
}

#[test]
fn reserved_words_are_recognized_exactly() {
    // reserved word lookup may be gated on the first byte or the length;
    // symbols that share a prefix, differ in case, or extend a reserved word
    // must stay symbols, and the exact spellings must not
    let lookalikes: &[&[u8]] = &[
        b"le",
        b"let1",
        b"letx",
        b"Let",
        b"LET",
        b"_a",
        b"__",
        b"!x",
        b"!!",
        b"a",
        b"ass",
        b"as_",
        b"As",
        b"forall_",
        b"foral",
        b"exist",
        b"existsx",
        b"matcher",
        b"mat",
        b"pa",
        b"par1",
        b"lambdas",
        b"lambd",
        b"HEXADECIMALS",
        b"HEXADECIMA",
        b"hexadecimal",
        b"BINARYx",
        b"DECIMAL1",
        b"NUMERALS",
        b"STRINGS",
        b"string",
    ];
    for symbol in lookalikes {
        assert_eq!(
            token_classes(symbol),
            vec![
                (SmtTokenCategory::UnquotedSymbol, None),
                (SmtTokenCategory::EndOfFile, None)
            ],
            "{:?} must be a plain symbol",
            String::from_utf8_lossy(symbol)
        );
    }
    let reserved: &[(&[u8], SmtReserved)] = &[
        (b"BINARY", SmtReserved::General(SmtGeneralReserved::Binary)),
        (
            b"DECIMAL",
            SmtReserved::General(SmtGeneralReserved::Decimal),
        ),
        (
            b"HEXADECIMAL",
            SmtReserved::General(SmtGeneralReserved::Hexadecimal),
        ),
        (
            b"NUMERAL",
            SmtReserved::General(SmtGeneralReserved::Numeral),
        ),
        (b"STRING", SmtReserved::General(SmtGeneralReserved::String)),
        (b"_", SmtReserved::General(SmtGeneralReserved::Underscore)),
        (
            b"!",
            SmtReserved::General(SmtGeneralReserved::ExclamationMark),
        ),
        (b"as", SmtReserved::General(SmtGeneralReserved::As)),
        (b"lambda", SmtReserved::General(SmtGeneralReserved::Lambda)),
        (b"let", SmtReserved::General(SmtGeneralReserved::Let)),
        (b"exists", SmtReserved::General(SmtGeneralReserved::Exists)),
        (b"forall", SmtReserved::General(SmtGeneralReserved::Forall)),
        (b"match", SmtReserved::General(SmtGeneralReserved::Match)),
        (b"par", SmtReserved::General(SmtGeneralReserved::Par)),
    ];
    for (word, expected) in reserved {
        assert_eq!(
            token_classes(word),
            vec![
                (SmtTokenCategory::UnquotedSymbol, Some(*expected)),
                (SmtTokenCategory::EndOfFile, None)
            ],
            "{:?} must be reserved",
            String::from_utf8_lossy(word)
        );
    }
}

#[test]
fn quoted_reserved_words_are_symbols() {
    // quoting makes any spelling an ordinary symbol, with the bare spelling as payload
    assert_eq!(
        token_payloads(b"|let| |_| |forall| |!|"),
        vec![
            (SmtTokenCategory::QuotedSymbol, b"let".to_vec()),
            (SmtTokenCategory::QuotedSymbol, b"_".to_vec()),
            (SmtTokenCategory::QuotedSymbol, b"forall".to_vec()),
            (SmtTokenCategory::QuotedSymbol, b"!".to_vec()),
            (SmtTokenCategory::EndOfFile, vec![]),
        ]
    );
    assert_eq!(
        token_classes(b"|let| |_| |forall| |!|"),
        vec![
            (SmtTokenCategory::QuotedSymbol, None),
            (SmtTokenCategory::QuotedSymbol, None),
            (SmtTokenCategory::QuotedSymbol, None),
            (SmtTokenCategory::QuotedSymbol, None),
            (SmtTokenCategory::EndOfFile, None),
        ]
    );
}

#[test]
fn reserved_word_followed_by_a_symbol_byte_is_a_longer_symbol() {
    // the symbol ends at the first byte that cannot continue it, so the
    // reserved check sees the complete symbol, not a prefix
    assert_eq!(
        token_payloads(b"let(letx)"),
        vec![
            (SmtTokenCategory::UnquotedSymbol, b"let".to_vec()),
            (SmtTokenCategory::ParenOpen, b"(".to_vec()),
            (SmtTokenCategory::UnquotedSymbol, b"letx".to_vec()),
            (SmtTokenCategory::ParenClose, b")".to_vec()),
            (SmtTokenCategory::EndOfFile, vec![]),
        ]
    );
    assert_eq!(
        token_classes(b"let(letx)"),
        vec![
            (
                SmtTokenCategory::UnquotedSymbol,
                Some(SmtReserved::General(SmtGeneralReserved::Let))
            ),
            (SmtTokenCategory::ParenOpen, None),
            (SmtTokenCategory::UnquotedSymbol, None),
            (SmtTokenCategory::ParenClose, None),
            (SmtTokenCategory::EndOfFile, None),
        ]
    );
}

// --- Carriage return alone ---

#[test]
fn cr_alone_ends_a_comment_but_not_a_line() {
    // a comment ends at CR as well as LF, but only LF starts a new line,
    // so the symbol after a CR-terminated comment stays on line zero
    assert_eq!(
        token_spans(b"; c\rx"),
        vec![
            (SmtTokenCategory::UnquotedSymbol, (4, 0, 4), (5, 0, 5)),
            (SmtTokenCategory::EndOfFile, (5, 0, 5), (5, 0, 5)),
        ]
    );
}

// --- Failed state after errors raised at EOF ---

/// A token consumer that rejects only the end-of-file token.
struct RejectEof;

impl SmtConsume for RejectEof {
    type Result = ();
    type Error = ();

    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        while let Some(token) = cursor.next() {
            if token.category() == SmtTokenCategory::EndOfFile {
                return Err(());
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

#[test]
#[should_panic(expected = "cannot lex after a lexer error")]
fn lexing_after_a_handler_error_on_the_eof_token_panics() {
    // the EOF token is the last thing lex_eof does; a handler error there
    // must still leave the lexer failed like every other error
    let mut lexer = SmtLexer::new(RejectEof, SmtVersion::V2_7);
    let _ = lexer.lex_slice(b"a").expect("valid input");
    assert!(lexer.lex_eof().is_err(), "expected a handler error");
    let _ = lexer.lex_slice(b"b");
}

#[test]
#[should_panic(expected = "cannot lex after a lexer error")]
fn lexing_after_a_lexer_error_at_eof_panics() {
    let mut lexer = SmtLexer::new(TakeTokens, SmtVersion::V2_7);
    let _ = lexer
        .lex_slice(b"\"unclosed")
        .map_err(into_lexer_error)
        .expect("valid so far");
    assert!(
        lexer.lex_eof().is_err(),
        "expected an unclosed string error"
    );
    let _ = lexer.lex_slice(b"\"");
}

// --- Lexing after a successful end of file ---
//
// The end of file ends an input: the lexer finishes the pending token, hands
// over the end-of-file token, and resets to its initial state, location
// included. Whatever is lexed afterwards is a new input from the origin.

/// Every token as `(type, payload, start, end)`.
type TokenRecord = (SmtTokenCategory, Vec<u8>, Loc, Loc);

fn records(tokens: &[LexedToken]) -> Vec<TokenRecord> {
    tokens
        .iter()
        .map(|token| (token.ty, token.content.clone(), token.start, token.end))
        .collect()
}

#[test]
fn the_end_of_file_resets_the_lexer_so_a_second_one_is_at_the_origin() {
    // whether a token is pending at the first EOF or not, the lexer is back
    // at the origin after it, and a second EOF is a new, empty input
    for (input, eof_at) in [(&b"a"[..], (1, 0, 1)), (&b"a "[..], (2, 0, 2))] {
        let lexed = lex_backend::lex(
            SmtVersion::V2_7,
            &[Feed::Slice(input), Feed::Eof, Feed::Eof],
        );
        assert_eq!(lexed.error, None, "valid input and two ends of file");
        // the location after the first and after the second end of file
        assert_eq!(lexed.locations[1..], [(0, 0, 0), (0, 0, 0)]);
        assert_eq!(
            records(&lexed.tokens),
            vec![
                (
                    SmtTokenCategory::UnquotedSymbol,
                    b"a".to_vec(),
                    (0, 0, 0),
                    (1, 0, 1)
                ),
                (SmtTokenCategory::EndOfFile, vec![], eof_at, eof_at),
                (SmtTokenCategory::EndOfFile, vec![], (0, 0, 0), (0, 0, 0)),
            ],
            "input {:?}",
            String::from_utf8_lossy(input)
        );
    }
}

#[test]
fn input_after_the_end_of_file_is_a_new_input_from_the_origin() {
    // the line count starts over as well
    let lexed = lex_backend::lex(
        SmtVersion::V2_7,
        &[
            Feed::Slice(b"a\n"),
            Feed::Eof,
            Feed::Slice(b"|b\nc| "),
            Feed::Eof,
        ],
    );
    assert_eq!(lexed.error, None, "two valid inputs");
    assert_eq!(
        records(&lexed.tokens),
        vec![
            (
                SmtTokenCategory::UnquotedSymbol,
                b"a".to_vec(),
                (0, 0, 0),
                (1, 0, 1)
            ),
            (SmtTokenCategory::EndOfFile, vec![], (2, 1, 0), (2, 1, 0)),
            (
                SmtTokenCategory::QuotedSymbol,
                b"b\nc".to_vec(),
                (0, 0, 0),
                (5, 1, 2)
            ),
            (SmtTokenCategory::EndOfFile, vec![], (6, 1, 3), (6, 1, 3)),
        ]
    );
}

#[test]
fn a_token_cut_by_the_end_of_file_is_finished_and_not_resumed() {
    // EOF finishes the pending symbol; bytes fed afterwards start a new one
    let lexed = lex_backend::lex(
        SmtVersion::V2_7,
        &[Feed::Slice(b"ab"), Feed::Eof, Feed::Slice(b"cd"), Feed::Eof],
    );
    assert_eq!(lexed.error, None, "two valid inputs");
    assert_eq!(
        records(&lexed.tokens),
        vec![
            (
                SmtTokenCategory::UnquotedSymbol,
                b"ab".to_vec(),
                (0, 0, 0),
                (2, 0, 2)
            ),
            (SmtTokenCategory::EndOfFile, vec![], (2, 0, 2), (2, 0, 2)),
            (
                SmtTokenCategory::UnquotedSymbol,
                b"cd".to_vec(),
                (0, 0, 0),
                (2, 0, 2)
            ),
            (SmtTokenCategory::EndOfFile, vec![], (2, 0, 2), (2, 0, 2)),
        ]
    );
}

// --- Several line breaks inside one token or run ---
//
// A scanner that handles a run per call has to compute every line feed's
// position from the start of the slice it was given, not from the start of
// the run that follows an earlier line feed. One line break per token does
// not catch that; two or more do.

#[test]
fn quoted_symbol_may_span_several_line_breaks() {
    assert_eq!(
        token_spans(b"|a\nb\nc| d"),
        vec![
            (SmtTokenCategory::QuotedSymbol, (0, 0, 0), (7, 2, 2)),
            (SmtTokenCategory::UnquotedSymbol, (8, 2, 3), (9, 2, 4)),
            (SmtTokenCategory::EndOfFile, (9, 2, 4), (9, 2, 4)),
        ]
    );
    // consecutive line breaks each start a line of their own
    assert_eq!(
        token_spans(b"|a\n\n\nb| d"),
        vec![
            (SmtTokenCategory::QuotedSymbol, (0, 0, 0), (7, 3, 2)),
            (SmtTokenCategory::UnquotedSymbol, (8, 3, 3), (9, 3, 4)),
            (SmtTokenCategory::EndOfFile, (9, 3, 4), (9, 3, 4)),
        ]
    );
}

#[test]
fn string_literal_may_span_several_line_breaks() {
    assert_eq!(
        token_spans(b"\"a\nb\nc\" d"),
        vec![
            (SmtTokenCategory::String, (0, 0, 0), (7, 2, 2)),
            (SmtTokenCategory::UnquotedSymbol, (8, 2, 3), (9, 2, 4)),
            (SmtTokenCategory::EndOfFile, (9, 2, 4), (9, 2, 4)),
        ]
    );
    // an escaped quote between the line breaks is one payload byte
    assert_eq!(
        token_payloads(b"\"a\n\"\"\nb\" c"),
        vec![
            (SmtTokenCategory::String, b"a\n\"\nb".to_vec()),
            (SmtTokenCategory::UnquotedSymbol, b"c".to_vec()),
            (SmtTokenCategory::EndOfFile, vec![]),
        ]
    );
    assert_eq!(
        token_spans(b"\"a\n\"\"\nb\" c"),
        vec![
            (SmtTokenCategory::String, (0, 0, 0), (8, 2, 2)),
            (SmtTokenCategory::UnquotedSymbol, (9, 2, 3), (10, 2, 4)),
            (SmtTokenCategory::EndOfFile, (10, 2, 4), (10, 2, 4)),
        ]
    );
}

#[test]
fn whitespace_and_comments_with_several_line_breaks() {
    assert_eq!(
        token_spans(b"a\n\n\n  b"),
        vec![
            (SmtTokenCategory::UnquotedSymbol, (0, 0, 0), (1, 0, 1)),
            (SmtTokenCategory::UnquotedSymbol, (6, 3, 2), (7, 3, 3)),
            (SmtTokenCategory::EndOfFile, (7, 3, 3), (7, 3, 3)),
        ]
    );
    // a comment ends at the first line break; the blank lines after it are whitespace
    assert_eq!(
        token_spans(b"; c\n\n\n(x)"),
        vec![
            (SmtTokenCategory::ParenOpen, (6, 3, 0), (7, 3, 1)),
            (SmtTokenCategory::UnquotedSymbol, (7, 3, 1), (8, 3, 2)),
            (SmtTokenCategory::ParenClose, (8, 3, 2), (9, 3, 3)),
            (SmtTokenCategory::EndOfFile, (9, 3, 3), (9, 3, 3)),
        ]
    );
}

// --- Fraction digits are decimal digits only ---

#[test]
fn decimal_fraction_ends_at_a_letter() {
    // hexadecimal letters are not fraction digits: the decimal ends before
    // them, and as the letter does not delimit it, that is an error
    assert_error(
        b"1.5a",
        SmtLexicalErrorKind::MissingDelimiter,
        (0, 0, 0),
        (4, 0, 4),
    );
    assert_error(
        b"3.25fed)",
        SmtLexicalErrorKind::MissingDelimiter,
        (0, 0, 0),
        (5, 0, 5),
    );
}

// --- Token separation ---
//
// A token must be followed by whitespace, a parenthesis, a comment start,
// or the end of the input. The error spans the token and the byte that
// should have delimited it, and the token is not handed over.

#[test]
fn a_token_must_be_delimited() {
    // every pair of token classes that can be glued, the first token and
    // the byte after it as the span
    let cases: &[(&[u8], Loc)] = &[
        (b"123abc", (4, 0, 4)),
        (b"0x", (2, 0, 2)),
        (b"1.5x", (4, 0, 4)),
        (b"1.5.3", (4, 0, 4)),
        (b"#x1Fg", (5, 0, 5)),
        (b"#b10a", (5, 0, 5)),
        (b"12|q|", (3, 0, 3)),
        (b"x\"s\"", (2, 0, 2)),
        (b"x|q|", (2, 0, 2)),
        (b"x#x1", (2, 0, 2)),
        (b"x:kw", (2, 0, 2)),
        (b":kw:kw2", (4, 0, 4)),
        (b":a\"s\"", (3, 0, 3)),
        (b"\"s\"t", (4, 0, 4)),
        (b"\"s\"\"t\"x", (7, 0, 7)),
        (b"|a|b", (4, 0, 4)),
        (b"|a||b|", (4, 0, 4)),
        (b"|a|\"s\"", (4, 0, 4)),
    ];
    for &(input, end) in cases {
        let err = lex_all(input).err().unwrap_or_else(|| {
            panic!("{:?} must be a lexer error", String::from_utf8_lossy(input))
        });
        assert_eq!(
            err.kind,
            SmtLexicalErrorKind::MissingDelimiter,
            "{:?}",
            String::from_utf8_lossy(input)
        );
        assert_eq!(
            (err.start, err.end),
            ((0, 0, 0), end),
            "span of {:?}",
            String::from_utf8_lossy(input)
        );
    }
}

#[test]
fn every_delimiter_separates_every_token_kind() {
    // each token kind followed by each delimiter and by the end of the input
    let tokens: &[&[u8]] = &[
        b"x", b"123", b"1.5", b"#x1F", b"#b10", b":kw", b"\"s\"", b"|q|",
    ];
    let delimiters: &[&[u8]] = &[b" ", b"\t", b"\r", b"\n", b"(", b")", b";c", b""];
    for token in tokens {
        for delimiter in delimiters {
            let input = [*token, *delimiter].concat();
            let lexed = lex_all(&input).unwrap_or_else(|err| {
                panic!(
                    "{:?} must lex, got {:?}",
                    String::from_utf8_lossy(&input),
                    err.kind
                )
            });
            // the token, possibly a parenthesis, and the end of file
            let expected = 2 + matches!(delimiter[..], [b'(' | b')']) as usize;
            assert_eq!(
                lexed.len(),
                expected,
                "{:?}",
                String::from_utf8_lossy(&input)
            );
        }
    }
}

#[test]
fn a_keyword_is_delimited_by_a_parenthesised_value() {
    // the parenthesis delimits the keyword, so a glued list value is fine
    assert_eq!(
        token_payloads(b":a(b)"),
        vec![
            (SmtTokenCategory::Keyword, b"a".to_vec()),
            (SmtTokenCategory::ParenOpen, b"(".to_vec()),
            (SmtTokenCategory::UnquotedSymbol, b"b".to_vec()),
            (SmtTokenCategory::ParenClose, b")".to_vec()),
            (SmtTokenCategory::EndOfFile, vec![]),
        ]
    );
}

#[test]
fn a_doubled_quote_continues_a_string_rather_than_ending_it() {
    // one token with the escape resolved, not two glued strings
    assert_eq!(
        token_payloads(b"\"a\"\"b\""),
        vec![
            (SmtTokenCategory::String, b"a\"b".to_vec()),
            (SmtTokenCategory::EndOfFile, vec![]),
        ]
    );
}

#[test]
fn a_token_ending_at_a_slice_end_is_delimited_by_the_next_slice() {
    // the byte that delimits a string or a quoted symbol closed exactly at
    // the end of a slice arrives with the next one, or never if the input ends
    for (first, second, ok) in [
        (&b"|q|"[..], &b")"[..], true),
        (b"|q|", b" x", true),
        (b"|q|", b"", true),
        (b"|q|", b"b", false),
        (b"|q|", b"|r|", false),
        (b"\"s\"", b")", true),
        (b"\"s\"", b"", true),
        (b"\"s\"", b"t", false),
        (b"\"s\"", b"\"t\"", true),
    ] {
        let lexed = lex_backend::lex(
            SmtVersion::V2_7,
            &[Feed::Slice(first), Feed::Slice(second), Feed::Eof],
        );
        assert!(
            !lexed.locations.is_empty(),
            "the first slice lexes: {:?}",
            lexed.error
        );
        let name = format!(
            "{:?} then {:?}",
            String::from_utf8_lossy(first),
            String::from_utf8_lossy(second)
        );
        match lexed.error {
            None => assert!(ok, "{name} must not lex"),
            Some(err) => {
                assert!(!ok, "{name} must lex, got {:?}", err.kind);
                assert_eq!(err.kind, SmtLexicalErrorKind::MissingDelimiter, "{name}");
                // the span covers the token in the first slice and the byte in the second
                assert_eq!(
                    (err.start, err.end),
                    (
                        (0, 0, 0),
                        (first.len() as u64 + 1, 0, first.len() as u64 + 1)
                    ),
                    "span of {name}"
                );
            }
        }
    }
}

#[test]
fn fraction_digit_expected_before_a_letter() {
    // a letter right after the dot is not a fraction digit either
    assert_error(
        b"1.a",
        SmtLexicalErrorKind::FractionDigitExpected,
        (0, 0, 0),
        (3, 0, 3),
    );
    assert_error(
        b"7.F",
        SmtLexicalErrorKind::FractionDigitExpected,
        (0, 0, 0),
        (3, 0, 3),
    );
}

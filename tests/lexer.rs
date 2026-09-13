//! Public-API tests of the lexer: error kinds and spans, token spans and
//! payloads, location tracking, handler errors, and misuse panics.

use std::convert::Infallible;

use smt_parser_rs::{
    SmtLocation, SmtSpan,
    read::lexer::{LexError, Lexer, LexerError, LexerErrorKind},
    token::{GeneralReserved, Reserved, SmtVersion, Token, TokenHandler, TokenKind, TokenType},
};

/// An owned copy of a produced token, collected by [`CollectTokens`].
///
/// Borrowed tokens cannot outlive the lexer's buffer, so tests collect these instead.
#[derive(Debug)]
struct OwnedToken {
    ty: TokenType,
    content: Vec<u8>,
    span: SmtSpan,
    /// The reserved word the token is classified as, if any.
    reserved: Option<Reserved>,
}

/// A token handler that collects owned copies of all tokens for later inspection.
struct CollectTokens(Vec<OwnedToken>);

impl TokenHandler for CollectTokens {
    type Error = Infallible;

    fn handle_token(&mut self, token: Token) -> Result<(), Self::Error> {
        let reserved = match TokenKind::from_token(token, SmtVersion::V2_7) {
            TokenKind::Reserved(reserved) => Some(reserved),
            _ => None,
        };
        self.0.push(OwnedToken {
            ty: token.ty(),
            content: token.content().to_vec(),
            span: token.span(),
            reserved,
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
        (0, 0, 0),
        (1, 0, 1),
    );
    // after other tokens, still just the one byte
    assert_error(
        b"(check-sat) \\",
        LexerErrorKind::UnexpectedCharacter,
        (12, 0, 12),
        (13, 0, 13),
    );
}

#[test]
fn fraction_digit_expected_on_byte() {
    // "7." followed by a space: the space is the byte where the error is detected
    assert_error(
        b"7. ",
        LexerErrorKind::FractionDigitExpected,
        (0, 0, 0),
        (3, 0, 3),
    );
}

#[test]
fn base_selection_expected() {
    assert_error(
        b"#q",
        LexerErrorKind::BaseSelectionExpected,
        (0, 0, 0),
        (2, 0, 2),
    );
}

#[test]
fn hexadecimal_digit_expected() {
    assert_error(
        b"#x ",
        LexerErrorKind::HexadecimalDigitExpected,
        (0, 0, 0),
        (3, 0, 3),
    );
}

#[test]
fn binary_digit_expected() {
    assert_error(
        b"#b)",
        LexerErrorKind::BinaryDigitExpected,
        (0, 0, 0),
        (3, 0, 3),
    );
}

#[test]
fn numeral_leading_zero() {
    assert_error(
        b"01",
        LexerErrorKind::NumeralLeadingZero,
        (0, 0, 0),
        (2, 0, 2),
    );
}

#[test]
fn keyword_name_expected() {
    assert_error(
        b": ",
        LexerErrorKind::ForbiddenKeywordName,
        (0, 0, 0),
        (2, 0, 2),
    );
}

#[test]
fn keyword_leading_digit() {
    assert_error(
        b":0",
        LexerErrorKind::ForbiddenKeywordName,
        (0, 0, 0),
        (2, 0, 2),
    );
    // the leading digit is rejected even when more characters would follow
    assert_error(
        b":0abc",
        LexerErrorKind::ForbiddenKeywordName,
        (0, 0, 0),
        (2, 0, 2),
    );
}

#[test]
fn keyword_spelled_like_a_reserved_word_is_a_keyword() {
    // reserved words are only recognized in symbols, so this is no error
    let tokens = lex_all(b":let ").expect("a keyword spelled like a reserved word must lex");
    assert_eq!(tokens[0].ty, TokenType::Keyword);
    assert_eq!(tokens[0].content, b"let");
    assert_eq!(tokens[0].reserved, None);
}

#[test]
fn backslash_in_quoted_symbol() {
    assert_error(
        b"|a\\b|",
        LexerErrorKind::BackslashInQuotedSymbol,
        (0, 0, 0),
        (3, 0, 3),
    );
}

#[test]
fn forbidden_char_in_string() {
    assert_error(
        b"\"a\x01b\"",
        LexerErrorKind::ForbiddenCharInString,
        (0, 0, 0),
        (3, 0, 3),
    );
}

#[test]
fn forbidden_char_in_quoted_symbol() {
    assert_error(
        b"|a\x7fb|",
        LexerErrorKind::ForbiddenCharInQuotedSymbol,
        (0, 0, 0),
        (3, 0, 3),
    );
}

// --- Errors detected at EOF: span must end exactly at the input length, not past it ---

#[test]
fn fraction_digit_expected_at_eof() {
    assert_error(
        b"7.",
        LexerErrorKind::FractionDigitExpected,
        (0, 0, 0),
        (2, 0, 2),
    );
}

#[test]
fn hexadecimal_digit_expected_at_eof() {
    assert_error(
        b"#x",
        LexerErrorKind::HexadecimalDigitExpected,
        (0, 0, 0),
        (2, 0, 2),
    );
}

#[test]
fn base_selection_expected_at_eof() {
    assert_error(
        b"#",
        LexerErrorKind::BaseSelectionExpected,
        (0, 0, 0),
        (1, 0, 1),
    );
}

#[test]
fn keyword_name_expected_at_eof() {
    assert_error(
        b":",
        LexerErrorKind::ForbiddenKeywordName,
        (0, 0, 0),
        (1, 0, 1),
    );
}

#[test]
fn unclosed_string_literal_at_eof() {
    assert_error(
        b"\"abc",
        LexerErrorKind::UnclosedStringLiteral,
        (0, 0, 0),
        (4, 0, 4),
    );
}

#[test]
fn unclosed_quoted_symbol_at_eof() {
    assert_error(
        b"|abc",
        LexerErrorKind::UnclosedQuotedSymbol,
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
        LexerErrorKind::UnclosedStringLiteral,
        (15, 2, 2),
        (19, 2, 6),
    );
}

#[test]
fn error_spanning_lines() {
    // an unclosed quoted symbol may contain newlines; the end is on a later line
    assert_error(
        b"|ab\ncd",
        LexerErrorKind::UnclosedQuotedSymbol,
        (0, 0, 0),
        (6, 1, 2),
    );
}

#[test]
fn crlf_counts_as_one_line() {
    // CR must not start a new line, so "01" is on zero-based line 1, column 0
    assert_error(
        b"(check-sat)\r\n01",
        LexerErrorKind::NumeralLeadingZero,
        (13, 1, 0),
        (15, 1, 2),
    );
}

#[test]
fn error_after_comment_line() {
    assert_error(
        b"; a comment\n\\",
        LexerErrorKind::UnexpectedCharacter,
        (12, 1, 0),
        (13, 1, 1),
    );
}

// --- Token spans and current location ---

#[test]
fn current_location_follows_consumed_bytes() {
    let mut collected = CollectTokens(Vec::new());
    let mut lexer = Lexer::new(&mut collected);
    assert_eq!(loc(lexer.current_location()), (0, 0, 0));
    for &c in b"ab\nc" {
        lexer
            .lex_next(c)
            .map_err(into_lexer_error)
            .expect("valid input");
    }
    assert_eq!(loc(lexer.current_location()), (4, 1, 1));
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
    // lines and columns are zero-based, columns counted in bytes
    assert_eq!(
        token_spans(b"(a 12)"),
        vec![
            (TokenType::ParenOpen, (0, 0, 0), (1, 0, 1)),
            (TokenType::UnquotedSymbol, (1, 0, 1), (2, 0, 2)),
            (TokenType::Numeral, (3, 0, 3), (5, 0, 5)),
            (TokenType::ParenClose, (5, 0, 5), (6, 0, 6)),
            (TokenType::EndOfFile, (6, 0, 6), (6, 0, 6)),
        ]
    );
}

#[test]
fn spans_restart_the_column_on_every_line() {
    assert_eq!(
        token_spans(b"(a)\n(b)"),
        vec![
            (TokenType::ParenOpen, (0, 0, 0), (1, 0, 1)),
            (TokenType::UnquotedSymbol, (1, 0, 1), (2, 0, 2)),
            (TokenType::ParenClose, (2, 0, 2), (3, 0, 3)),
            (TokenType::ParenOpen, (4, 1, 0), (5, 1, 1)),
            (TokenType::UnquotedSymbol, (5, 1, 1), (6, 1, 2)),
            (TokenType::ParenClose, (6, 1, 2), (7, 1, 3)),
            (TokenType::EndOfFile, (7, 1, 3), (7, 1, 3)),
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
            (TokenType::UnquotedSymbol, (0, 0, 0), (2, 0, 2)),
            (TokenType::UnquotedSymbol, (3, 1, 0), (5, 1, 2)),
            (TokenType::EndOfFile, (5, 1, 2), (5, 1, 2)),
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
            (TokenType::QuotedSymbol, (0, 0, 0), (5, 1, 2)),
            (TokenType::UnquotedSymbol, (6, 1, 3), (7, 1, 4)),
            (TokenType::EndOfFile, (7, 1, 4), (7, 1, 4)),
        ]
    );
}

#[test]
fn string_literal_may_span_a_line_break() {
    assert_eq!(
        token_spans(b"\"a\nb\""),
        vec![
            (TokenType::String, (0, 0, 0), (5, 1, 2)),
            (TokenType::EndOfFile, (5, 1, 2), (5, 1, 2)),
        ]
    );
}

#[test]
fn end_of_file_token_location() {
    // an empty input consists of the end-of-file token alone, at the stream start
    assert_eq!(
        token_spans(b""),
        vec![(TokenType::EndOfFile, (0, 0, 0), (0, 0, 0))]
    );
    // without a trailing line break, the end-of-file token is just past the last token
    assert_eq!(
        token_spans(b"(a)"),
        vec![
            (TokenType::ParenOpen, (0, 0, 0), (1, 0, 1)),
            (TokenType::UnquotedSymbol, (1, 0, 1), (2, 0, 2)),
            (TokenType::ParenClose, (2, 0, 2), (3, 0, 3)),
            (TokenType::EndOfFile, (3, 0, 3), (3, 0, 3)),
        ]
    );
    // with one, its offset is exactly the start of the next line,
    // so it is reported at the first column of that line rather than past the end
    // of the previous one
    assert_eq!(
        token_spans(b"(a)\n"),
        vec![
            (TokenType::ParenOpen, (0, 0, 0), (1, 0, 1)),
            (TokenType::UnquotedSymbol, (1, 0, 1), (2, 0, 2)),
            (TokenType::ParenClose, (2, 0, 2), (3, 0, 3)),
            (TokenType::EndOfFile, (4, 1, 0), (4, 1, 0)),
        ]
    );
}

#[test]
fn crlf_is_a_single_line_break_in_token_spans() {
    // CR terminates the symbol but must not start a line of its own
    assert_eq!(
        token_spans(b"a\r\nb"),
        vec![
            (TokenType::UnquotedSymbol, (0, 0, 0), (1, 0, 1)),
            (TokenType::UnquotedSymbol, (3, 1, 0), (4, 1, 1)),
            (TokenType::EndOfFile, (4, 1, 1), (4, 1, 1)),
        ]
    );
}

#[test]
fn comments_produce_no_tokens_but_still_count_lines() {
    assert_eq!(
        token_spans(b"; c\nx"),
        vec![
            (TokenType::UnquotedSymbol, (4, 1, 0), (5, 1, 1)),
            (TokenType::EndOfFile, (5, 1, 1), (5, 1, 1)),
        ]
    );
}

#[test]
fn keyword_may_contain_digits_after_the_first_character() {
    // only the leading digit is forbidden; later ones are ordinary keyword characters
    assert_eq!(
        token_spans(b":a0 :x1y2"),
        vec![
            (TokenType::Keyword, (0, 0, 0), (3, 0, 3)),
            (TokenType::Keyword, (4, 0, 4), (9, 0, 9)),
            (TokenType::EndOfFile, (9, 0, 9), (9, 0, 9)),
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
            (TokenType::Keyword, (0, 0, 0), (3, 0, 3)),
            (TokenType::Hexadecimal, (4, 0, 4), (8, 0, 8)),
            (TokenType::Binary, (9, 0, 9), (13, 0, 13)),
            (TokenType::Decimal, (14, 0, 14), (17, 0, 17)),
            (TokenType::String, (18, 0, 18), (21, 0, 21)),
            (TokenType::UnquotedSymbol, (22, 0, 22), (25, 0, 25)),
            (TokenType::QuotedSymbol, (26, 0, 26), (29, 0, 29)),
            (TokenType::EndOfFile, (29, 0, 29), (29, 0, 29)),
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
    // the one before it, so any missed buffer clear shows up as leftover bytes
    assert_eq!(
        token_payloads(b"abcd let e :k1 \"s\" |q| 12 3.4 #xA #b0"),
        vec![
            (TokenType::UnquotedSymbol, b"abcd".to_vec()),
            (TokenType::UnquotedSymbol, b"let".to_vec()),
            (TokenType::UnquotedSymbol, b"e".to_vec()),
            (TokenType::Keyword, b"k1".to_vec()),
            (TokenType::String, b"s".to_vec()),
            (TokenType::QuotedSymbol, b"q".to_vec()),
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
            (TokenType::QuotedSymbol, b"abc".to_vec()),
            (TokenType::QuotedSymbol, vec![]),
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
    assert_eq!((loc(span.start()), loc(span.end())), ((0, 0, 0), (1, 0, 1)));
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

// --- Reserved words against similar symbols ---
//
// The lexer produces every symbol alike; the reserved words are recognized
// when the token is classified, from its content.

/// Every token of the input as its type and the reserved word it is
/// classified as, in order.
fn token_classes(input: &[u8]) -> Vec<(TokenType, Option<Reserved>)> {
    lex_all(input)
        .expect("test input must lex")
        .iter()
        .map(|token| (token.ty, token.reserved))
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
                (TokenType::UnquotedSymbol, None),
                (TokenType::EndOfFile, None)
            ],
            "{:?} must be a plain symbol",
            String::from_utf8_lossy(symbol)
        );
    }
    let reserved: &[(&[u8], Reserved)] = &[
        (b"BINARY", Reserved::General(GeneralReserved::Binary)),
        (b"DECIMAL", Reserved::General(GeneralReserved::Decimal)),
        (
            b"HEXADECIMAL",
            Reserved::General(GeneralReserved::Hexadecimal),
        ),
        (b"NUMERAL", Reserved::General(GeneralReserved::Numeral)),
        (b"STRING", Reserved::General(GeneralReserved::String)),
        (b"_", Reserved::General(GeneralReserved::Underscore)),
        (b"!", Reserved::General(GeneralReserved::ExclamationMark)),
        (b"as", Reserved::General(GeneralReserved::As)),
        (b"lambda", Reserved::General(GeneralReserved::Lambda)),
        (b"let", Reserved::General(GeneralReserved::Let)),
        (b"exists", Reserved::General(GeneralReserved::Exists)),
        (b"forall", Reserved::General(GeneralReserved::Forall)),
        (b"match", Reserved::General(GeneralReserved::Match)),
        (b"par", Reserved::General(GeneralReserved::Par)),
    ];
    for (word, expected) in reserved {
        assert_eq!(
            token_classes(word),
            vec![
                (TokenType::UnquotedSymbol, Some(*expected)),
                (TokenType::EndOfFile, None)
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
            (TokenType::QuotedSymbol, b"let".to_vec()),
            (TokenType::QuotedSymbol, b"_".to_vec()),
            (TokenType::QuotedSymbol, b"forall".to_vec()),
            (TokenType::QuotedSymbol, b"!".to_vec()),
            (TokenType::EndOfFile, vec![]),
        ]
    );
    assert_eq!(
        token_classes(b"|let| |_| |forall| |!|"),
        vec![
            (TokenType::QuotedSymbol, None),
            (TokenType::QuotedSymbol, None),
            (TokenType::QuotedSymbol, None),
            (TokenType::QuotedSymbol, None),
            (TokenType::EndOfFile, None),
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
            (TokenType::UnquotedSymbol, b"let".to_vec()),
            (TokenType::ParenOpen, vec![]),
            (TokenType::UnquotedSymbol, b"letx".to_vec()),
            (TokenType::ParenClose, vec![]),
            (TokenType::EndOfFile, vec![]),
        ]
    );
    assert_eq!(
        token_classes(b"let(letx)"),
        vec![
            (
                TokenType::UnquotedSymbol,
                Some(Reserved::General(GeneralReserved::Let))
            ),
            (TokenType::ParenOpen, None),
            (TokenType::UnquotedSymbol, None),
            (TokenType::ParenClose, None),
            (TokenType::EndOfFile, None),
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
            (TokenType::UnquotedSymbol, (4, 0, 4), (5, 0, 5)),
            (TokenType::EndOfFile, (5, 0, 5), (5, 0, 5)),
        ]
    );
}

// --- Failed state after errors raised at EOF ---

/// A token handler that rejects only the end-of-file token.
struct RejectEof;

impl TokenHandler for RejectEof {
    type Error = ();

    fn handle_token(&mut self, token: Token) -> Result<(), Self::Error> {
        if token.ty() == TokenType::EndOfFile {
            Err(())
        } else {
            Ok(())
        }
    }
}

#[test]
#[should_panic(expected = "cannot lex after a lexer error")]
fn lexing_after_a_handler_error_on_the_eof_token_panics() {
    // the EOF token is the last thing lex_eof does; a handler error there
    // must still leave the lexer failed like every other error
    let mut lexer = Lexer::new(RejectEof);
    lexer.lex_slice(b"a").expect("valid input");
    assert!(lexer.lex_eof().is_err(), "expected a handler error");
    let _ = lexer.lex_next(b'b');
}

#[test]
#[should_panic(expected = "cannot lex after a lexer error")]
fn lexing_after_a_lexer_error_at_eof_panics() {
    let mut collected = CollectTokens(Vec::new());
    let mut lexer = Lexer::new(&mut collected);
    lexer
        .lex_slice(b"\"unclosed")
        .map_err(into_lexer_error)
        .expect("valid so far");
    assert!(
        lexer.lex_eof().is_err(),
        "expected an unclosed string error"
    );
    let _ = lexer.lex_next(b'"');
}

// --- Lexing after a successful end of file ---
//
// The behaviour after `lex_eof` has succeeded is not decided yet. These tests
// pin what the lexer does today so that a change is noticed; if another
// behaviour is chosen later, they are to be changed deliberately along with it.

/// Every token as `(type, payload, start, end)`.
type TokenRecord = (TokenType, Vec<u8>, Loc, Loc);

fn records(tokens: &[OwnedToken]) -> Vec<TokenRecord> {
    tokens
        .iter()
        .map(|token| {
            (
                token.ty,
                token.content.clone(),
                loc(token.span.start()),
                loc(token.span.end()),
            )
        })
        .collect()
}

#[test]
fn eof_twice_after_a_pending_symbol_produces_two_eof_tokens() {
    let mut collected = CollectTokens(Vec::new());
    let mut lexer = Lexer::new(&mut collected);
    lexer
        .lex_slice(b"a")
        .map_err(into_lexer_error)
        .expect("valid input");
    lexer
        .lex_eof()
        .map_err(into_lexer_error)
        .expect("first EOF");
    // currently, a second EOF is not rejected: finishing the symbol at the
    // first EOF returns the lexer to the normal state, so the second EOF
    // only repeats the EOF token (a full reset of the lexer is still undecided)
    lexer
        .lex_eof()
        .map_err(into_lexer_error)
        .expect("second EOF");
    assert_eq!(loc(lexer.current_location()), (1, 0, 1));
    drop(lexer);
    assert_eq!(
        records(&collected.0),
        vec![
            (
                TokenType::UnquotedSymbol,
                b"a".to_vec(),
                (0, 0, 0),
                (1, 0, 1)
            ),
            (TokenType::EndOfFile, vec![], (1, 0, 1), (1, 0, 1)),
            (TokenType::EndOfFile, vec![], (1, 0, 1), (1, 0, 1)),
        ]
    );
}

#[test]
fn lexing_continues_after_eof_as_if_the_input_went_on() {
    let mut collected = CollectTokens(Vec::new());
    let mut lexer = Lexer::new(&mut collected);
    lexer
        .lex_slice(b"a\n")
        .map_err(into_lexer_error)
        .expect("valid input");
    lexer
        .lex_eof()
        .map_err(into_lexer_error)
        .expect("first EOF");
    // currently, more input after EOF is lexed normally, with locations
    // continuing from where the first EOF was reported
    lexer
        .lex_slice(b"|b\nc| ")
        .map_err(into_lexer_error)
        .expect("input after EOF");
    lexer
        .lex_eof()
        .map_err(into_lexer_error)
        .expect("second EOF");
    drop(lexer);
    assert_eq!(
        records(&collected.0),
        vec![
            (
                TokenType::UnquotedSymbol,
                b"a".to_vec(),
                (0, 0, 0),
                (1, 0, 1)
            ),
            (TokenType::EndOfFile, vec![], (2, 1, 0), (2, 1, 0)),
            (
                TokenType::QuotedSymbol,
                b"b\nc".to_vec(),
                (2, 1, 0),
                (7, 2, 2)
            ),
            (TokenType::EndOfFile, vec![], (8, 2, 3), (8, 2, 3)),
        ]
    );
}

#[test]
fn a_token_cut_by_eof_is_finished_and_not_resumed() {
    let mut collected = CollectTokens(Vec::new());
    let mut lexer = Lexer::new(&mut collected);
    lexer
        .lex_slice(b"ab")
        .map_err(into_lexer_error)
        .expect("valid input");
    // EOF finishes the pending symbol; bytes fed afterwards start a new one
    lexer.lex_eof().map_err(into_lexer_error).expect("EOF");
    lexer
        .lex_slice(b"cd")
        .map_err(into_lexer_error)
        .expect("input after EOF");
    lexer
        .lex_eof()
        .map_err(into_lexer_error)
        .expect("second EOF");
    drop(lexer);
    assert_eq!(
        records(&collected.0),
        vec![
            (
                TokenType::UnquotedSymbol,
                b"ab".to_vec(),
                (0, 0, 0),
                (2, 0, 2)
            ),
            (TokenType::EndOfFile, vec![], (2, 0, 2), (2, 0, 2)),
            (
                TokenType::UnquotedSymbol,
                b"cd".to_vec(),
                (2, 0, 2),
                (4, 0, 4)
            ),
            (TokenType::EndOfFile, vec![], (4, 0, 4), (4, 0, 4)),
        ]
    );
}

#[test]
fn eof_twice_after_whitespace_produces_two_eof_tokens() {
    // with no token pending at the first EOF, the state is already normal
    // and the second EOF only repeats the EOF token
    let mut collected = CollectTokens(Vec::new());
    let mut lexer = Lexer::new(&mut collected);
    lexer
        .lex_slice(b"a ")
        .map_err(into_lexer_error)
        .expect("valid input");
    lexer
        .lex_eof()
        .map_err(into_lexer_error)
        .expect("first EOF");
    lexer
        .lex_eof()
        .map_err(into_lexer_error)
        .expect("second EOF");
    drop(lexer);
    assert_eq!(
        records(&collected.0),
        vec![
            (
                TokenType::UnquotedSymbol,
                b"a".to_vec(),
                (0, 0, 0),
                (1, 0, 1)
            ),
            (TokenType::EndOfFile, vec![], (2, 0, 2), (2, 0, 2)),
            (TokenType::EndOfFile, vec![], (2, 0, 2), (2, 0, 2)),
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
            (TokenType::QuotedSymbol, (0, 0, 0), (7, 2, 2)),
            (TokenType::UnquotedSymbol, (8, 2, 3), (9, 2, 4)),
            (TokenType::EndOfFile, (9, 2, 4), (9, 2, 4)),
        ]
    );
    // consecutive line breaks each start a line of their own
    assert_eq!(
        token_spans(b"|a\n\n\nb| d"),
        vec![
            (TokenType::QuotedSymbol, (0, 0, 0), (7, 3, 2)),
            (TokenType::UnquotedSymbol, (8, 3, 3), (9, 3, 4)),
            (TokenType::EndOfFile, (9, 3, 4), (9, 3, 4)),
        ]
    );
}

#[test]
fn string_literal_may_span_several_line_breaks() {
    assert_eq!(
        token_spans(b"\"a\nb\nc\" d"),
        vec![
            (TokenType::String, (0, 0, 0), (7, 2, 2)),
            (TokenType::UnquotedSymbol, (8, 2, 3), (9, 2, 4)),
            (TokenType::EndOfFile, (9, 2, 4), (9, 2, 4)),
        ]
    );
    // an escaped quote between the line breaks is one payload byte
    assert_eq!(
        token_payloads(b"\"a\n\"\"\nb\" c"),
        vec![
            (TokenType::String, b"a\n\"\nb".to_vec()),
            (TokenType::UnquotedSymbol, b"c".to_vec()),
            (TokenType::EndOfFile, vec![]),
        ]
    );
    assert_eq!(
        token_spans(b"\"a\n\"\"\nb\" c"),
        vec![
            (TokenType::String, (0, 0, 0), (8, 2, 2)),
            (TokenType::UnquotedSymbol, (9, 2, 3), (10, 2, 4)),
            (TokenType::EndOfFile, (10, 2, 4), (10, 2, 4)),
        ]
    );
}

#[test]
fn whitespace_and_comments_with_several_line_breaks() {
    assert_eq!(
        token_spans(b"a\n\n\n  b"),
        vec![
            (TokenType::UnquotedSymbol, (0, 0, 0), (1, 0, 1)),
            (TokenType::UnquotedSymbol, (6, 3, 2), (7, 3, 3)),
            (TokenType::EndOfFile, (7, 3, 3), (7, 3, 3)),
        ]
    );
    // a comment ends at the first line break; the blank lines after it are whitespace
    assert_eq!(
        token_spans(b"; c\n\n\n(x)"),
        vec![
            (TokenType::ParenOpen, (6, 3, 0), (7, 3, 1)),
            (TokenType::UnquotedSymbol, (7, 3, 1), (8, 3, 2)),
            (TokenType::ParenClose, (8, 3, 2), (9, 3, 3)),
            (TokenType::EndOfFile, (9, 3, 3), (9, 3, 3)),
        ]
    );
}

// --- Fraction digits are decimal digits only ---

#[test]
fn decimal_fraction_ends_at_a_letter() {
    // hexadecimal letters are not fraction digits: the decimal ends before
    // them and the letters start a symbol
    assert_eq!(
        token_payloads(b"1.5a 2.0e 3.25fed)"),
        vec![
            (TokenType::Decimal, b"1.5".to_vec()),
            (TokenType::UnquotedSymbol, b"a".to_vec()),
            (TokenType::Decimal, b"2.0".to_vec()),
            (TokenType::UnquotedSymbol, b"e".to_vec()),
            (TokenType::Decimal, b"3.25".to_vec()),
            (TokenType::UnquotedSymbol, b"fed".to_vec()),
            (TokenType::ParenClose, vec![]),
            (TokenType::EndOfFile, vec![]),
        ]
    );
    assert_eq!(
        token_spans(b"1.5a"),
        vec![
            (TokenType::Decimal, (0, 0, 0), (3, 0, 3)),
            (TokenType::UnquotedSymbol, (3, 0, 3), (4, 0, 4)),
            (TokenType::EndOfFile, (4, 0, 4), (4, 0, 4)),
        ]
    );
}

#[test]
fn fraction_digit_expected_before_a_letter() {
    // a letter right after the dot is not a fraction digit either
    assert_error(
        b"1.a",
        LexerErrorKind::FractionDigitExpected,
        (0, 0, 0),
        (3, 0, 3),
    );
    assert_error(
        b"7.F",
        LexerErrorKind::FractionDigitExpected,
        (0, 0, 0),
        (3, 0, 3),
    );
}

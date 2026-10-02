//! Slice-boundary tests of the lexer: feeding the same input through
//! `lex_slice` in every chunking must produce the same tokens, spans,
//! payloads, errors, and locations as feeding it as one slice.
//!
//! The lexer keeps the state of a token cut off at the end of a slice and
//! continues it in the next one, so every position in every kind of token
//! is a boundary that has to work. The inputs below are small, so the tests
//! can afford to try every fixed chunk length and every two-piece split of
//! each of them.

mod lex_backend;

use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtLocation,
    read::lexer::{Lexer, LexerErrorKind},
    token::{SmtVersion, TokenCursor, TokenHandler, TokenType},
};

use lex_backend::{Feed, LexedError, LexedToken, loc};

/// Where a lexer error was raised.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ErrorSite {
    /// By `lex_slice` on the chunk covering the given byte offsets.
    Slice { start: u64, end: u64 },
    /// By `lex_eof`.
    Eof,
}

/// Everything observable about one lexer run.
#[derive(Debug)]
struct Outcome {
    tokens: Vec<LexedToken>,
    error: Option<(LexedError, ErrorSite)>,
}

impl Outcome {
    fn error_kind(&self) -> Option<&LexerErrorKind> {
        self.error.as_ref().map(|(err, _)| &err.kind)
    }
}

/// The location reached after consuming the given bytes from the given
/// location, computed independently of the lexer.
fn location_after(from: SmtLocation, bytes: &[u8]) -> SmtLocation {
    bytes
        .iter()
        .fold(from, |location, &c| location.after_byte(c))
}

/// Lexes the input as the given sequence of chunks, then EOF, with the lexer
/// under test.
///
/// The chunks must concatenate to the input. After every successfully lexed
/// chunk, the lexer's current location is checked against the independently
/// computed location. Lexing stops at the first error.
#[track_caller]
fn lex_chunks(input: &[u8], chunks: &[&[u8]]) -> Outcome {
    let concatenated: Vec<u8> = chunks.concat();
    assert_eq!(
        concatenated, input,
        "test bug: chunks must concatenate to the input"
    );

    let mut feeds: Vec<Feed<'_>> = chunks.iter().map(|chunk| Feed::Slice(chunk)).collect();
    feeds.push(Feed::Eof);
    let lexed = lex_backend::lex(SmtVersion::V2_7, &feeds);

    // the chunks that were lexed without an error are those with a location
    let mut consumed = 0usize;
    let mut expected_location = SmtLocation::initial();
    for (chunk, location) in chunks.iter().zip(&lexed.locations) {
        consumed += chunk.len();
        expected_location = location_after(expected_location, chunk);
        assert_eq!(
            *location,
            loc(expected_location),
            "current location after {consumed} bytes of {:?} fed as {} chunks",
            String::from_utf8_lossy(input),
            chunks.len()
        );
    }

    // the error was raised by the feed after the ones that have a location
    let error = lexed.error.map(|err| {
        let site = match chunks.get(lexed.locations.len()) {
            Some(chunk) => ErrorSite::Slice {
                start: consumed as u64,
                end: (consumed + chunk.len()) as u64,
            },
            None => ErrorSite::Eof,
        };
        (err, site)
    });

    Outcome {
        tokens: lexed.tokens,
        error,
    }
}

/// Lexes the input as a single slice followed by EOF: the reference.
fn lex_whole(input: &[u8]) -> Outcome {
    lex_chunks(input, &[input])
}

/// Splits the input into consecutive chunks of the given lengths.
///
/// The lengths are used cyclically until the input is exhausted; the last
/// chunk is cut short as needed. Zero lengths produce empty chunks.
fn split_by_lengths<'a>(input: &'a [u8], lengths: &[usize]) -> Vec<&'a [u8]> {
    assert!(
        lengths.iter().any(|&length| length > 0),
        "test bug: chunk lengths must make progress"
    );
    let mut chunks = Vec::new();
    let mut position = 0;
    let mut index = 0;
    while position < input.len() {
        let length = lengths[index % lengths.len()].min(input.len() - position);
        chunks.push(&input[position..position + length]);
        position += length;
        index += 1;
    }
    if input.is_empty() {
        // an empty input still has to be fed as something, so that
        // lex_slice sees an empty slice at least once
        chunks.push(input);
    }
    chunks
}

/// Checks that a chunked run agrees with the reference run in every
/// observable way, and that an error is raised by the chunk holding the
/// offending byte (or by EOF, exactly when the reference raises it there).
#[track_caller]
fn assert_same_outcome(input: &[u8], reference: &Outcome, chunks: &[&[u8]]) {
    let chunked = lex_chunks(input, chunks);
    let describe = || {
        format!(
            "input {:?} fed as chunks of lengths {:?}",
            String::from_utf8_lossy(input),
            chunks.iter().map(|chunk| chunk.len()).collect::<Vec<_>>()
        )
    };

    assert_eq!(
        chunked.tokens,
        reference.tokens,
        "tokens differ: {}",
        describe()
    );

    match (&reference.error, &chunked.error) {
        (None, None) => {}
        (Some((expected, expected_site)), Some((actual, actual_site))) => {
            assert_eq!(actual, expected, "error differs: {}", describe());
            match (expected_site, actual_site) {
                (ErrorSite::Eof, ErrorSite::Eof) => {}
                (ErrorSite::Slice { .. }, ErrorSite::Slice { start, end }) => {
                    // an error detected on a byte is raised by the call that
                    // fed that byte, which is the last byte of the error span
                    let offending = expected
                        .end
                        .0
                        .checked_sub(1)
                        .expect("an error detected on a byte has a nonempty span");
                    assert!(
                        (*start..*end).contains(&offending),
                        "error on byte {offending} raised by chunk {start}..{end}: {}",
                        describe()
                    );
                }
                _ => panic!(
                    "error site differs: expected {expected_site:?}, got {actual_site:?}: {}",
                    describe()
                ),
            }
        }
        _ => panic!(
            "error presence differs: expected {:?}, got {:?}: {}",
            reference.error,
            chunked.error,
            describe()
        ),
    }
}

/// Inputs that lex without error, covering every token type, multi-line
/// tokens, escapes, comments, CRLF, and reserved words.
const VALID_INPUTS: &[&[u8]] = &[
    b"",
    b" ",
    b"\n",
    b"(",
    b"a",
    b"(set-logic QF_UF)\n(declare-fun f (Int) Bool)\n(assert (f 12))\n(check-sat)\n",
    b"7 7.0 #x1F #b10 \"s\" :kw |q s| sym",
    b"abcd let e :k1 \"s\" |q| 12 3.4 #xA #b0",
    b"|abc| || \"xy\" \"\" :a",
    b"\"a\"\"b\" \"\"\"\"",
    b"\"line1\nline2\" |sym\nbol| x",
    b"\"\"\"\n\"\"\" |\n|",
    // several line breaks inside one token: every line feed position must be
    // taken from the start of the slice, not from the previous line feed
    b"|a\nb\nc| d",
    b"|a\n\n\nb| d\n\n\ne",
    b"\"a\nb\nc\" d",
    b"\"a\n\"\"\nb\" c",
    b"|\n\n\n| x\n\n\ny",
    b"; c\n\n\n(x)\n; d\n\n",
    b"; comment\r\n(a)\r\n; trailing comment",
    b"; comment only",
    b"; comment\n",
    b"(a b)\n\n\n  \t (c)",
    b"forall exists let ! _ as match par lambda BINARY DECIMAL HEXADECIMAL NUMERAL STRING",
    // keywords spelled like reserved words, and quoted reserved words
    b":let :_ :par :STRING |let| |_| |assert|",
    b"0 0.5 10.25 123456789 9.0",
    // hexadecimal letters after decimals, delimited; glued they are an error
    b"1.5 a 2.0 e 3.25 fed)",
    b"#xDEADbeef #b0101 #x0 #b1",
    b":named :pattern :a1 :_x :+",
    b"\"\xC3\xA9\" |\xFF|",
    b"(((((x)))))",
    // every token kind delimited only by parentheses or comments
    b"a(b)(c)(\"d\")(e)(|f|)g;h\ni",
    b"1.5(2.5)(#x1)(#b1)(:k)(|q|)(\"s\");c\n:a(b)",
    b"~!@$%^&*_-+=<>.?/ a.b -1 +2",
];

/// Inputs that raise every lexer error kind, detected on a byte and at EOF.
const ERROR_INPUTS: &[&[u8]] = &[
    b"\\",
    b"ab \\ cd",
    b"1.",
    b"1.)",
    b"(assert 1.)",
    b"1.a",
    b"7.F",
    b"#",
    b"# ",
    b"#x",
    b"#x)",
    b"#b",
    b"#b)",
    b"01",
    b"007",
    b"(a\n  01)",
    b":",
    b": ",
    b":1",
    b"|a\\b|",
    b"\"a\x01\"",
    b"|a\x01|",
    b"\"unclosed",
    b"|unclosed",
    b"abc \"a\nb",
    b"|a\nb",
    b"\"a\"\"",
    b"; comment\n\\",
    b"\xC3\xA9",
    b"|\x7F|",
    b"\"\x7F\"",
    // glued tokens: the first token ends and the next byte does not delimit it
    b"123abc",
    b"1.5a 2.0e 3.25fed)",
    b"a(b)c\"d\"e|f|g;h\ni",
    b"1.5(2.5)#x1#b1:k|q|\"s\"",
    b"x:kw",
    b":a\"s\"",
    b"|q|b",
    b"|a||b|",
    b"\"s\"t",
    b"\"s\"\"t\"|u|",
];

fn all_inputs() -> impl Iterator<Item = &'static [u8]> {
    VALID_INPUTS.iter().chain(ERROR_INPUTS).copied()
}

#[test]
fn valid_inputs_lex_and_error_inputs_do_not() {
    for input in VALID_INPUTS {
        let outcome = lex_whole(input);
        assert!(
            outcome.error.is_none(),
            "test bug: valid input {:?} raised {:?}",
            String::from_utf8_lossy(input),
            outcome.error
        );
    }
    for input in ERROR_INPUTS {
        let outcome = lex_whole(input);
        assert!(
            outcome.error.is_some(),
            "test bug: error input {:?} lexed without error",
            String::from_utf8_lossy(input)
        );
    }
}

#[test]
fn inputs_cover_every_token_type_and_error_kind() {
    // keep the input sets expansive: every token type and every error kind
    // must be exercised, so that a boundary inside any of them is tested
    let mut token_types: Vec<TokenType> = Vec::new();
    let mut error_kinds: Vec<LexerErrorKind> = Vec::new();
    for input in all_inputs() {
        let outcome = lex_whole(input);
        for token in &outcome.tokens {
            if !token_types.contains(&token.ty) {
                token_types.push(token.ty);
            }
        }
        if let Some(kind) = outcome.error_kind()
            && !error_kinds.contains(kind)
        {
            error_kinds.push(*kind);
        }
    }

    let expected_types = [
        TokenType::ParenOpen,
        TokenType::ParenClose,
        TokenType::Numeral,
        TokenType::Decimal,
        TokenType::Hexadecimal,
        TokenType::Binary,
        TokenType::UnquotedSymbol,
        TokenType::QuotedSymbol,
        TokenType::String,
        TokenType::Keyword,
        TokenType::EndOfFile,
    ];
    for ty in expected_types {
        assert!(token_types.contains(&ty), "no input produces {ty:?}");
    }

    let expected_kinds = [
        LexerErrorKind::UnexpectedCharacter,
        LexerErrorKind::FractionDigitExpected,
        LexerErrorKind::HexadecimalDigitExpected,
        LexerErrorKind::BinaryDigitExpected,
        LexerErrorKind::BaseSelectionExpected,
        LexerErrorKind::UnclosedStringLiteral,
        LexerErrorKind::ForbiddenCharInString,
        LexerErrorKind::ForbiddenKeywordName,
        LexerErrorKind::BackslashInQuotedSymbol,
        LexerErrorKind::ForbiddenCharInQuotedSymbol,
        LexerErrorKind::UnclosedQuotedSymbol,
        LexerErrorKind::NumeralLeadingZero,
    ];
    for kind in expected_kinds {
        assert!(error_kinds.contains(&kind), "no input raises {kind:?}");
    }

    // both error sites must occur, otherwise the site check tests nothing
    let sites: Vec<ErrorSite> = ERROR_INPUTS
        .iter()
        .filter_map(|input| lex_whole(input).error.map(|(_, site)| site))
        .collect();
    assert!(sites.contains(&ErrorSite::Eof), "no error is raised at EOF");
    assert!(
        sites
            .iter()
            .any(|site| matches!(site, ErrorSite::Slice { .. })),
        "no error is raised on a byte"
    );
}

#[test]
fn every_fixed_chunk_length_matches_the_whole_slice() {
    for input in all_inputs() {
        let reference = lex_whole(input);
        for length in 1..=input.len().max(1) {
            let chunks = split_by_lengths(input, &[length]);
            assert_same_outcome(input, &reference, &chunks);
        }
    }
}

#[test]
fn every_two_piece_split_matches_the_whole_slice() {
    for input in all_inputs() {
        let reference = lex_whole(input);
        for split in 0..=input.len() {
            let (first, second) = input.split_at(split);
            assert_same_outcome(input, &reference, &[first, second]);
        }
    }
}

#[test]
fn every_three_piece_split_matches_the_whole_slice() {
    // two boundaries can fall inside the same token, or bracket a single byte
    for input in all_inputs() {
        let reference = lex_whole(input);
        for first_split in 0..=input.len() {
            for second_split in first_split..=input.len() {
                let (first, rest) = input.split_at(first_split);
                let (second, third) = rest.split_at(second_split - first_split);
                assert_same_outcome(input, &reference, &[first, second, third]);
            }
        }
    }
}

#[test]
fn byte_by_byte_slices_match_the_whole_slice() {
    for input in all_inputs() {
        let reference = lex_whole(input);

        let bytes: Vec<&[u8]> = input.chunks(1).collect();
        let chunked = lex_chunks(input, &bytes);

        assert_eq!(
            chunked.tokens,
            reference.tokens,
            "tokens differ for {:?} fed byte by byte",
            String::from_utf8_lossy(input)
        );
        assert_eq!(
            chunked.error.as_ref().map(|(err, _)| err),
            reference.error.as_ref().map(|(err, _)| err),
            "error differs for {:?} fed byte by byte",
            String::from_utf8_lossy(input)
        );
    }
}

#[test]
fn irregular_chunk_lengths_match_the_whole_slice() {
    // a few fixed patterns of mixed lengths, including one-byte chunks
    // right after longer ones and vice versa
    let patterns: &[&[usize]] = &[
        &[1, 2],
        &[2, 1],
        &[3, 1, 1],
        &[1, 4, 2, 1, 3],
        &[5, 1],
        &[1, 7],
        &[2, 3, 5, 7, 11],
    ];
    for input in all_inputs() {
        let reference = lex_whole(input);
        for pattern in patterns {
            let chunks = split_by_lengths(input, pattern);
            assert_same_outcome(input, &reference, &chunks);
        }
    }
}

#[test]
fn empty_slices_between_chunks_change_nothing() {
    // an empty slice must be a no-op anywhere: before the first byte,
    // between any two bytes, inside any token, and after the last byte
    for input in all_inputs() {
        let reference = lex_whole(input);
        for length in [1usize, 2, 3, 5] {
            let mut chunks: Vec<&[u8]> = vec![b""];
            for chunk in split_by_lengths(input, &[length]) {
                chunks.push(chunk);
                chunks.push(b"");
            }
            assert_same_outcome(input, &reference, &chunks);
        }
    }
}

#[test]
fn whole_slice_agrees_with_lex_all() {
    // lex_all is the convenience the other tests in this crate use, so the
    // reference here must be the same thing
    // this compares two ways of calling the Rust lexer, whatever lexer the
    // other tests run against
    for input in all_inputs() {
        let reference = lex_backend::rust_lex(SmtVersion::V2_7, &[Feed::Slice(input), Feed::Eof]);
        let all = lex_backend::rust_lex_all(SmtVersion::V2_7, input);

        assert_eq!(all.tokens, reference.tokens);
        assert_eq!(all.error, reference.error);
    }
}

// --- Long tokens: runs longer than any scanning chunk, cut at every boundary ---

/// Token lengths around the powers of two a chunked scanner might use,
/// plus one far beyond any of them.
const LONG_LENGTHS: &[usize] = &[1, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 1000];

/// Builds an input whose tokens of every content-carrying type are `length`
/// bytes long, separated by whitespace runs of the same length, with the
/// string containing an escaped quote and the quoted symbol a line break
/// in the middle. Returns the input and the expected payloads in order.
fn long_token_input(length: usize) -> (Vec<u8>, Vec<(TokenType, Vec<u8>)>) {
    let symbol: Vec<u8> = (0..length).map(|i| b"abcxyz_-+.?"[i % 11]).collect();
    let numeral: Vec<u8> = (0..length).map(|i| b"1234567890"[i % 10]).collect();
    let hex: Vec<u8> = (0..length)
        .map(|i| b"0123456789abcdefABCDEF"[i % 22])
        .collect();
    let binary: Vec<u8> = (0..length).map(|i| b"01"[i % 2]).collect();
    let keyword: Vec<u8> = (0..length).map(|i| b"kw-name"[i % 7]).collect();
    // the string gets line breaks at a quarter and three quarters of its
    // length and an escaped quote in the middle, which counts as one payload
    // byte; the quoted symbol gets line breaks at the same three positions,
    // so that both tokens contain several line feeds
    let mut string_source: Vec<u8> = (0..length).map(|i| b"str ing"[i % 7]).collect();
    if length > 4 {
        string_source[length / 4] = b'\n';
        string_source[3 * length / 4] = b'\n';
    }
    let mut string_payload = string_source.clone();
    if length > 2 {
        string_source[length / 2] = b'"';
        string_source.insert(length / 2, b'"');
        string_payload[length / 2] = b'"';
    }
    let mut quoted: Vec<u8> = (0..length).map(|i| b"quo ted"[i % 7]).collect();
    if length > 2 {
        quoted[length / 2] = b'\n';
    }
    if length > 4 {
        quoted[length / 4] = b'\n';
        quoted[3 * length / 4] = b'\n';
    }
    let comment: Vec<u8> = (0..length).map(|i| b"comment "[i % 8]).collect();
    let whitespace: Vec<u8> = (0..length).map(|i| b" \t\n "[i % 4]).collect();

    let mut input = Vec::new();
    let mut expected = Vec::new();
    let mut push = |input: &mut Vec<u8>, source: &[u8], ty: TokenType, payload: &[u8]| {
        input.extend_from_slice(source);
        input.extend_from_slice(&whitespace);
        expected.push((ty, payload.to_vec()));
    };
    push(&mut input, &symbol, TokenType::UnquotedSymbol, &symbol);
    push(&mut input, &numeral, TokenType::Numeral, &numeral);
    let mut decimal = numeral.clone();
    decimal.push(b'.');
    decimal.extend_from_slice(&numeral);
    push(&mut input, &decimal, TokenType::Decimal, &decimal);
    push(
        &mut input,
        &[b"#x", hex.as_slice()].concat(),
        TokenType::Hexadecimal,
        &hex,
    );
    push(
        &mut input,
        &[b"#b", binary.as_slice()].concat(),
        TokenType::Binary,
        &binary,
    );
    push(
        &mut input,
        &[b":", keyword.as_slice()].concat(),
        TokenType::Keyword,
        &keyword,
    );
    push(
        &mut input,
        &[b"\"", string_source.as_slice(), b"\""].concat(),
        TokenType::String,
        &string_payload,
    );
    push(
        &mut input,
        &[b"|", quoted.as_slice(), b"|"].concat(),
        TokenType::QuotedSymbol,
        &quoted,
    );
    // the comment produces no token; the parenthesis after it does
    input.extend_from_slice(b";");
    input.extend_from_slice(&comment);
    input.extend_from_slice(b"\n(");
    expected.push((TokenType::ParenOpen, b"(".to_vec()));
    expected.push((TokenType::EndOfFile, Vec::new()));
    (input, expected)
}

#[test]
fn long_tokens_have_the_expected_payloads() {
    for &length in LONG_LENGTHS {
        let (input, expected) = long_token_input(length);
        let outcome = lex_whole(&input);
        assert!(
            outcome.error.is_none(),
            "length {length}: {:?}",
            outcome.error
        );
        let payloads: Vec<(TokenType, Vec<u8>)> = outcome
            .tokens
            .iter()
            .map(|token| (token.ty, token.content.clone()))
            .collect();
        assert_eq!(payloads, expected, "payloads for token length {length}");
    }
}

#[test]
fn long_tokens_match_across_chunk_lengths() {
    for &length in LONG_LENGTHS {
        let (input, _) = long_token_input(length);
        let reference = lex_whole(&input);
        for chunk_length in [1usize, 2, 3, 7, 15, 16, 17, 64, 1000] {
            let chunks = split_by_lengths(&input, &[chunk_length]);
            assert_same_outcome(&input, &reference, &chunks);
        }
        // and with boundaries just before and just after every token start
        for split in [length - 1, length, length + 1, 2 * length, 3 * length + 1] {
            if split <= input.len() {
                let (first, second) = input.split_at(split);
                assert_same_outcome(&input, &reference, &[first, second]);
            }
        }
    }
}

// --- Contents against spans: the payload is what the span selects, for every token ---

/// The payload the span of a token selects in the input, independent of the
/// lexer's own content buffer.
fn payload_from_span(input: &[u8], token: &LexedToken) -> Vec<u8> {
    let start = token.start.0 as usize;
    let end = token.end.0 as usize;
    let text = &input[start..end];
    match token.ty {
        TokenType::QuotedSymbol => text[1..text.len() - 1].to_vec(),
        // parentheses carry their own byte, like every other borrowed token
        TokenType::UnquotedSymbol
        | TokenType::Numeral
        | TokenType::Decimal
        | TokenType::ParenOpen
        | TokenType::ParenClose => text.to_vec(),
        TokenType::Keyword => text[1..].to_vec(),
        TokenType::Hexadecimal | TokenType::Binary => text[2..].to_vec(),
        TokenType::String => {
            let mut payload = Vec::new();
            let mut rest = &text[1..text.len() - 1];
            while let Some(&c) = rest.first() {
                payload.push(c);
                // an escaped quote is two quote bytes in the source
                rest = if c == b'"' { &rest[2..] } else { &rest[1..] };
            }
            payload
        }
        TokenType::EndOfFile => {
            assert_eq!((start, end), (input.len(), input.len()), "EOF span");
            Vec::new()
        }
    }
}

#[test]
fn token_contents_match_their_spans() {
    let long_inputs: Vec<Vec<u8>> = LONG_LENGTHS
        .iter()
        .map(|&length| long_token_input(length).0)
        .collect();
    let inputs = VALID_INPUTS
        .iter()
        .map(|input| input.to_vec())
        .chain(long_inputs);
    for input in inputs {
        let outcome = lex_whole(&input);
        for token in &outcome.tokens {
            assert_eq!(
                token.content,
                payload_from_span(&input, token),
                "{:?} token at {:?} in {:?}",
                token.ty,
                token.start,
                String::from_utf8_lossy(&input)
            );
        }
    }
}

// --- Handler errors under chunking ---

/// A token handler that accepts the first `n` tokens and rejects the next.
struct RejectNth {
    remaining: usize,
}

impl TokenHandler for RejectNth {
    type Result = ();
    type Error = ();

    fn handle_tokens(
        &mut self,
        cursor: &mut TokenCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        while cursor.next().is_some() {
            if self.remaining == 0 {
                return Err(());
            }
            self.remaining -= 1;
        }
        Ok(ControlFlow::Continue(()))
    }
}

#[test]
fn handler_errors_are_raised_where_the_token_is_produced_in_every_chunking() {
    for input in VALID_INPUTS {
        let reference = lex_whole(input);
        for (n, rejected) in reference.tokens.iter().enumerate() {
            for chunk_length in [1usize, 2, 3, 5, input.len().max(1)] {
                let chunks = split_by_lengths(input, &[chunk_length]);
                let mut lexer = Lexer::new(RejectNth { remaining: n }, SmtVersion::V2_7);
                let mut consumed = 0;
                let mut site = None;
                for chunk in &chunks {
                    if lexer.lex_slice(chunk).is_err() {
                        site = Some(ErrorSite::Slice {
                            start: consumed as u64,
                            end: (consumed + chunk.len()) as u64,
                        });
                        break;
                    }
                    consumed += chunk.len();
                }
                if site.is_none() {
                    assert!(
                        lexer.lex_eof().is_err(),
                        "the rejected token must be produced"
                    );
                    site = Some(ErrorSite::Eof);
                }

                // a token is produced when its last byte or the byte after it
                // is fed, or at EOF when nothing follows it
                let end = rejected.end.0;
                let describe = format!(
                    "token {n} ({:?}) of {:?} with chunks of {chunk_length}",
                    rejected.ty,
                    String::from_utf8_lossy(input)
                );
                match site.expect("site is set") {
                    ErrorSite::Eof => assert_eq!(end as usize, input.len(), "{describe}"),
                    ErrorSite::Slice {
                        start,
                        end: chunk_end,
                    } => assert!(
                        (start..chunk_end).contains(&end.saturating_sub(1))
                            || (start..chunk_end).contains(&end),
                        "raised by chunk {start}..{chunk_end}, token ends at {end}: {describe}"
                    ),
                }
            }
        }
    }
}

// --- Every run length at every alignment ---
//
// A scanner that works in 16- or 32-byte windows can fail at any run length
// relative to a window and at any alignment of the run within the slice.
// The long-token tests sample lengths; these try every length up to 70 and
// every start position up to 3, for every kind of run the lexer scans.

/// Builds the token source of a given run length and says what token and
/// payload to expect, or `None` if the length is not valid for the kind.
type BuildRun = fn(usize) -> Option<(Vec<u8>, TokenType, Vec<u8>)>;

/// One kind of run the lexer scans.
struct RunKind {
    name: &'static str,
    build: BuildRun,
}

const RUN_KINDS: &[RunKind] = &[
    RunKind {
        name: "simple symbol",
        build: |n| (n > 0).then(|| (vec![b'a'; n], TokenType::UnquotedSymbol, vec![b'a'; n])),
    },
    RunKind {
        name: "quoted symbol",
        build: |n| {
            let source = [b"|".as_slice(), &vec![b'q'; n], b"|"].concat();
            Some((source, TokenType::QuotedSymbol, vec![b'q'; n]))
        },
    },
    RunKind {
        name: "string literal",
        build: |n| {
            let source = [b"\"".as_slice(), &vec![b's'; n], b"\""].concat();
            Some((source, TokenType::String, vec![b's'; n]))
        },
    },
    RunKind {
        name: "keyword",
        build: |n| {
            (n > 0).then(|| {
                let source = [b":".as_slice(), &vec![b'k'; n]].concat();
                (source, TokenType::Keyword, vec![b'k'; n])
            })
        },
    },
    RunKind {
        name: "numeral",
        build: |n| (n > 0).then(|| (vec![b'7'; n], TokenType::Numeral, vec![b'7'; n])),
    },
    RunKind {
        name: "decimal fraction",
        build: |n| {
            (n > 0).then(|| {
                let source = [b"1.".as_slice(), &vec![b'5'; n]].concat();
                (source.clone(), TokenType::Decimal, source)
            })
        },
    },
    RunKind {
        name: "hexadecimal",
        build: |n| {
            (n > 0).then(|| {
                let source = [b"#x".as_slice(), &vec![b'A'; n]].concat();
                (source, TokenType::Hexadecimal, vec![b'A'; n])
            })
        },
    },
    RunKind {
        name: "binary",
        build: |n| {
            (n > 0).then(|| {
                let source = [b"#b".as_slice(), &vec![b'1'; n]].concat();
                (source, TokenType::Binary, vec![b'1'; n])
            })
        },
    },
];

#[test]
fn every_run_length_at_every_alignment_lexes_correctly() {
    for kind in RUN_KINDS {
        for prefix in 0..4usize {
            for run_length in 0..=70usize {
                let Some((source, ty, payload)) = (kind.build)(run_length) else {
                    continue;
                };
                // the token starts at `prefix`, ends at a parenthesis, and
                // is followed by another token so that its end is inside the slice
                let mut input = vec![b' '; prefix];
                input.extend_from_slice(&source);
                input.extend_from_slice(b")x");

                let reference = lex_whole(&input);
                assert!(
                    reference.error.is_none(),
                    "{}: {:?}",
                    kind.name,
                    reference.error
                );
                let token = &reference.tokens[0];
                let describe = format!("{} of length {run_length} at {prefix}", kind.name);
                assert_eq!(token.ty, ty, "{describe}");
                assert_eq!(token.content, payload, "{describe}");
                assert_eq!(
                    (token.start.0 as usize, token.end.0 as usize),
                    (prefix, prefix + source.len()),
                    "{describe}: span"
                );
                assert_eq!(reference.tokens[1].ty, TokenType::ParenClose, "{describe}");

                for chunk_length in [1usize, 3, 16, 17, 32, 33] {
                    let chunks = split_by_lengths(&input, &[chunk_length]);
                    assert_same_outcome(&input, &reference, &chunks);
                }
            }
        }
    }
}

#[test]
fn every_comment_and_whitespace_run_length_at_every_alignment() {
    for prefix in 0..4usize {
        for run_length in 0..=70usize {
            // a comment of the given length, then a symbol on the next line
            let mut input = vec![b' '; prefix];
            input.push(b';');
            input.extend(std::iter::repeat_n(b'c', run_length));
            input.extend_from_slice(b"\nx");
            let reference = lex_whole(&input);
            let x_start = (prefix + 1 + run_length + 1) as u64;
            assert_eq!(
                (
                    reference.tokens[0].ty,
                    reference.tokens[0].start,
                    reference.tokens[0].end
                ),
                (
                    TokenType::UnquotedSymbol,
                    (x_start, 1, 0),
                    (x_start + 1, 1, 1)
                ),
                "comment of length {run_length} at {prefix}"
            );
            for chunk_length in [1usize, 3, 16, 17, 32, 33] {
                let chunks = split_by_lengths(&input, &[chunk_length]);
                assert_same_outcome(&input, &reference, &chunks);
            }

            // a whitespace run of the given length between two symbols, with a
            // line feed in it when there is room, so the line changes too
            // (without whitespace the two symbols would be one)
            if run_length == 0 {
                continue;
            }
            let mut whitespace = vec![b' '; run_length];
            if run_length > 2 {
                whitespace[run_length / 2] = b'\n';
            }
            let mut input = vec![b'\t'; prefix];
            input.push(b'a');
            input.extend_from_slice(&whitespace);
            input.push(b'b');
            let reference = lex_whole(&input);
            let b_start = (prefix + 1 + run_length) as u64;
            let (line, column) = if run_length > 2 {
                (1, (run_length - run_length / 2 - 1) as u64)
            } else {
                (0, b_start)
            };
            assert_eq!(
                (reference.tokens[1].ty, reference.tokens[1].start),
                (TokenType::UnquotedSymbol, (b_start, line, column)),
                "whitespace run of length {run_length} at {prefix}"
            );
            for chunk_length in [1usize, 3, 16, 17, 32, 33] {
                let chunks = split_by_lengths(&input, &[chunk_length]);
                assert_same_outcome(&input, &reference, &chunks);
            }
        }
    }
}

// --- Slices inside a larger buffer ---
//
// Scanning must look only at the slice it was given. The bytes after a slice
// in the same buffer are chosen so that reading them would change the
// outcome: they continue the last run, or terminate it differently.

#[test]
fn a_slice_inside_a_larger_buffer_lexes_like_a_copy_of_itself() {
    // what follows the slice in memory: run continuations of every kind,
    // terminators, delimiters, and line feeds
    let trailers: &[&[u8]] = &[
        b"abc",
        b"123",
        b"fff",
        b")",
        b"\"\"",
        b"|",
        b"\n\n",
        b" ; comment\n",
        b"\\",
        b"\x01",
    ];
    let leaders: &[&[u8]] = &[b"", b"xyz", b"\"", b"|", b"\n"];
    for input in all_inputs() {
        let reference = lex_whole(input);
        for leader in leaders {
            for trailer in trailers {
                let buffer = [leader, input, trailer].concat();
                let inner = &buffer[leader.len()..leader.len() + input.len()];
                // as one slice
                assert_same_outcome(inner, &reference, &[inner]);
                // and cut in two inside the buffer, so both chunks have
                // foreign bytes right after them
                for split in [1usize, input.len() / 2, input.len().saturating_sub(1)] {
                    if split <= inner.len() {
                        let (first, second) = inner.split_at(split);
                        assert_same_outcome(inner, &reference, &[first, second]);
                    }
                }
            }
        }
    }
}

// --- Payloads from different sources in one slice ---
//
// Once token contents borrow from the input where they can, a slice may hand
// out payloads that live in the input (tokens fully inside the slice), in the
// lexer's own buffer (tokens cut by the previous boundary, strings with
// escapes), and in the input again, in any order. Every payload must be the
// token's own bytes regardless of where it came from and what came before.

#[test]
fn payloads_from_cut_tokens_escaped_strings_and_plain_tokens_alternate_correctly() {
    let chunks: &[&[u8]] = &[
        b"ab",                     // symbol cut here
        b"cd \"x\"\"y\" \"z\" |q", // continued symbol, escaped string, plain string, quoted cut here
        b"r| s #x1",               // continued quoted, plain symbol, hex cut here
        b"F 12",                   // continued hex, numeral cut here (at slice end)
        b"3.5 |\n| :k",            // continued decimal, quoted with line feed, keyword cut
        b"w \"\"\"\"",             // continued keyword, string of one escaped quote
    ];
    let input: Vec<u8> = chunks.concat();
    let outcome = lex_chunks(&input, chunks);
    assert!(outcome.error.is_none(), "{:?}", outcome.error);
    let payloads: Vec<(TokenType, Vec<u8>)> = outcome
        .tokens
        .iter()
        .map(|token| (token.ty, token.content.clone()))
        .collect();
    assert_eq!(
        payloads,
        vec![
            (TokenType::UnquotedSymbol, b"abcd".to_vec()),
            (TokenType::String, b"x\"y".to_vec()),
            (TokenType::String, b"z".to_vec()),
            (TokenType::QuotedSymbol, b"qr".to_vec()),
            (TokenType::UnquotedSymbol, b"s".to_vec()),
            (TokenType::Hexadecimal, b"1F".to_vec()),
            (TokenType::Decimal, b"123.5".to_vec()),
            (TokenType::QuotedSymbol, b"\n".to_vec()),
            (TokenType::Keyword, b"kw".to_vec()),
            (TokenType::String, b"\"".to_vec()),
            (TokenType::EndOfFile, vec![]),
        ]
    );
    // and the same input in every other chunking agrees
    let reference = lex_whole(&input);
    assert_same_outcome(&input, &reference, chunks);
    for chunk_length in 1..=input.len() {
        let chunks = split_by_lengths(&input, &[chunk_length]);
        assert_same_outcome(&input, &reference, &chunks);
    }
}

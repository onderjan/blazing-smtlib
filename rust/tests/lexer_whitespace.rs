//! Black-box tests of the lexer with a consumer that takes whitespace and
//! comments: what the two kinds of token carry, that the tokens then cover
//! the whole input, and that everything else stays as it is for a consumer
//! that does not take them.
//!
//! These run against the Rust lexer only: the driver protocol has no request
//! for this kind of consumer.

mod lex_backend;

use blazing_smtlib::{
    SmtLocation,
    token::{SmtTokenCategory, SmtVersion},
};

use lex_backend::{Feed, Lexed, LexedToken, loc};

use SmtTokenCategory::{
    Comment, EndOfFile, Keyword, Numeral, ParenClose, ParenOpen, QuotedSymbol, String as Str,
    UnquotedSymbol, Whitespace,
};

const VERSIONS: [SmtVersion; 4] = [
    SmtVersion::V2_0,
    SmtVersion::V2_5,
    SmtVersion::V2_6,
    SmtVersion::V2_7,
];

/// Inputs without lexical errors under every version, chosen for where their
/// whitespace and comments lie: at the start and the end of the input, next
/// to every kind of token, with every line-breaking character, and inside
/// strings and quoted symbols, where they are content.
const INPUTS: [&[u8]; 22] = [
    b"",
    b" ",
    b"\t",
    b"\r",
    b"\n",
    b"\r\n\t \n\n",
    b";",
    b"; c",
    b";\n",
    b";\r",
    b";\r\n",
    b"; c\r\n; d\n",
    b";;; a ; b\n;\n;",
    b"(a  b)\n",
    b"a;b\rc ;\n\n x",
    b"  (assert\n\t(= x #x1F #b01 12 1.5 :kw |q\ns| \"s\nt\")) ; end\n\n; last",
    b"|a| |b|\n|c|;x\n(\n)\n",
    b"\"a ; b\" |c ; d| ; e",
    b"\n\n\n(check-sat)\n\n\n",
    b"x \n",
    b"x\n ",
    b"( ) ( )",
];

fn lex_with_whitespace(version: SmtVersion, pieces: &[&[u8]]) -> Lexed {
    let mut feeds: Vec<Feed<'_>> = pieces.iter().map(|piece| Feed::Slice(piece)).collect();
    feeds.push(Feed::Eof);
    lex_backend::rust_lex_with_whitespace(version, &feeds)
}

fn lex_without_whitespace(version: SmtVersion, pieces: &[&[u8]]) -> Lexed {
    let mut feeds: Vec<Feed<'_>> = pieces.iter().map(|piece| Feed::Slice(piece)).collect();
    feeds.push(Feed::Eof);
    lex_backend::rust_lex(version, &feeds)
}

fn show(input: &[u8]) -> String {
    String::from_utf8_lossy(input).into_owned()
}

/// The categories and contents of the tokens of the input, without the
/// end-of-file token, which must come last.
fn tokens_of(input: &[u8]) -> Vec<(SmtTokenCategory, Vec<u8>)> {
    let lexed = lex_with_whitespace(SmtVersion::V2_7, &[input]);
    assert_eq!(lexed.error, None, "error in {:?}", show(input));
    let mut tokens: Vec<_> = lexed
        .tokens
        .into_iter()
        .map(|token| (token.ty, token.content))
        .collect();
    assert_eq!(
        tokens.pop().map(|(ty, _)| ty),
        Some(EndOfFile),
        "the last token of {:?}",
        show(input)
    );
    tokens
}

fn assert_tokens(input: &[u8], expected: &[(SmtTokenCategory, &[u8])]) {
    let expected: Vec<(SmtTokenCategory, Vec<u8>)> = expected
        .iter()
        .map(|(ty, content)| (*ty, content.to_vec()))
        .collect();
    assert_eq!(tokens_of(input), expected, "tokens of {:?}", show(input));
}

fn is_whitespace_or_comment(token: &LexedToken) -> bool {
    matches!(token.ty, Whitespace | Comment)
}

// --- What the two kinds of token carry ---

#[test]
fn a_whitespace_token_is_a_maximal_run_of_whitespace_characters() {
    assert_tokens(b" ", &[(Whitespace, b" ")]);
    assert_tokens(b"\t", &[(Whitespace, b"\t")]);
    assert_tokens(b"\r", &[(Whitespace, b"\r")]);
    assert_tokens(b"\n", &[(Whitespace, b"\n")]);
    // every whitespace character continues the run, also across lines
    assert_tokens(b" \t\r\n \n\n\t", &[(Whitespace, b" \t\r\n \n\n\t")]);
    assert_tokens(
        b"a \n b",
        &[
            (UnquotedSymbol, b"a"),
            (Whitespace, b" \n "),
            (UnquotedSymbol, b"b"),
        ],
    );
    assert_tokens(
        b"a\n\nb",
        &[
            (UnquotedSymbol, b"a"),
            (Whitespace, b"\n\n"),
            (UnquotedSymbol, b"b"),
        ],
    );
}

#[test]
fn whitespace_tokens_stand_wherever_whitespace_is_written() {
    assert_tokens(
        b" ( a  :k\t1 ) ",
        &[
            (Whitespace, b" "),
            (ParenOpen, b"("),
            (Whitespace, b" "),
            (UnquotedSymbol, b"a"),
            (Whitespace, b"  "),
            (Keyword, b"k"),
            (Whitespace, b"\t"),
            (Numeral, b"1"),
            (Whitespace, b" "),
            (ParenClose, b")"),
            (Whitespace, b" "),
        ],
    );
    // tokens written without whitespace between them have none between them
    assert_tokens(
        b"(a)(|b|)",
        &[
            (ParenOpen, b"("),
            (UnquotedSymbol, b"a"),
            (ParenClose, b")"),
            (ParenOpen, b"("),
            (QuotedSymbol, b"b"),
            (ParenClose, b")"),
        ],
    );
}

#[test]
fn a_comment_token_carries_what_follows_its_semicolon_through_its_line_break() {
    assert_tokens(b"; c\n", &[(Comment, b" c\n")]);
    assert_tokens(b";\n", &[(Comment, b"\n")]);
    // a carriage return ends a comment as a line feed does
    assert_tokens(b"; c\r", &[(Comment, b" c\r")]);
    // so the line feed of a two-character line break is whitespace after it
    assert_tokens(b"; c\r\n", &[(Comment, b" c\r"), (Whitespace, b"\n")]);
    // further semicolons and any other bytes are a part of the comment
    assert_tokens(
        b";; a ; (b) \"|\x00\xff\t\n",
        &[(Comment, b"; a ; (b) \"|\x00\xff\t\n")],
    );
}

#[test]
fn a_comment_that_runs_to_the_end_of_the_input_has_no_line_break() {
    assert_tokens(b"; c", &[(Comment, b" c")]);
    assert_tokens(b";", &[(Comment, b"")]);
    assert_tokens(b"a;", &[(UnquotedSymbol, b"a"), (Comment, b"")]);
}

#[test]
fn comments_and_whitespace_are_separate_tokens() {
    assert_tokens(
        b" ; a\n ; b\n\n;c",
        &[
            (Whitespace, b" "),
            (Comment, b" a\n"),
            (Whitespace, b" "),
            (Comment, b" b\n"),
            (Whitespace, b"\n"),
            (Comment, b"c"),
        ],
    );
    // a comment delimits the token before it
    assert_tokens(
        b"a;b\nc",
        &[
            (UnquotedSymbol, b"a"),
            (Comment, b"b\n"),
            (UnquotedSymbol, b"c"),
        ],
    );
}

#[test]
fn whitespace_and_semicolons_inside_strings_and_quoted_symbols_are_content() {
    assert_tokens(
        b"\"a ; b\n\" |c ; d\n|",
        &[
            (Str, b"a ; b\n"),
            (Whitespace, b" "),
            (QuotedSymbol, b"c ; d\n"),
        ],
    );
}

// --- The tokens cover the input ---

/// Checks the tokens of the input against the input itself: the spans follow
/// one another from the start of the input to its end with nothing between
/// them, each ends where the bytes it spans lead to, and a whitespace or
/// comment token carries the bytes it spans (a comment without its
/// semicolon), which are of the right kind.
fn assert_covers(version: SmtVersion, input: &[u8]) {
    let lexed = lex_with_whitespace(version, &[input]);
    let context = format!("{:?} under {version:?}", show(input));
    assert_eq!(lexed.error, None, "error in {context}");

    let mut at = SmtLocation::initial();
    let mut previous: Option<SmtTokenCategory> = None;
    for token in &lexed.tokens {
        assert_eq!(token.start, loc(at), "start of {token:?} in {context}");
        let text = &input[token.start.0 as usize..token.end.0 as usize];
        at = text.iter().fold(at, |location, &c| location.after_byte(c));
        assert_eq!(token.end, loc(at), "end of {token:?} in {context}");

        match token.ty {
            Whitespace => {
                assert_eq!(token.content, text, "content of {token:?} in {context}");
                assert!(!text.is_empty(), "empty whitespace in {context}");
                assert!(
                    text.iter()
                        .all(|c| matches!(c, b'\t' | b'\n' | b'\r' | b' ')),
                    "{token:?} in {context}"
                );
                assert_ne!(
                    previous,
                    Some(Whitespace),
                    "a whitespace run in two tokens in {context}"
                );
            }
            Comment => {
                assert_eq!(text.first(), Some(&b';'), "{token:?} in {context}");
                assert_eq!(
                    token.content,
                    text[1..],
                    "content of {token:?} in {context}"
                );
                // a line break ends the comment, only the end of the input does otherwise
                let (last, inside) = text.split_last().expect("a comment has its semicolon");
                assert!(
                    inside.iter().all(|c| !matches!(c, b'\n' | b'\r')),
                    "{token:?} in {context}"
                );
                assert!(
                    matches!(last, b'\n' | b'\r') || token.end.0 as usize == input.len(),
                    "{token:?} in {context}"
                );
            }
            EndOfFile => assert!(text.is_empty(), "{token:?} in {context}"),
            _ => {}
        }
        previous = Some(token.ty);
    }
    assert_eq!(
        at.offset() as usize,
        input.len(),
        "the tokens end in {context}"
    );
    assert_eq!(previous, Some(EndOfFile), "the last token in {context}");
}

#[test]
fn the_tokens_cover_the_whole_input() {
    for version in VERSIONS {
        for input in INPUTS {
            assert_covers(version, input);
        }
    }
}

#[test]
fn the_tokens_cover_an_input_of_many_batches() {
    // more tokens than a hand-over holds, with whitespace on and across lines
    let input: Vec<u8> = b"(a b)\n  ; c\n"
        .iter()
        .copied()
        .cycle()
        .take(12 * 300)
        .collect();
    assert_covers(SmtVersion::V2_7, &input);
}

// --- The tokens do not depend on how the input is sliced ---

#[test]
fn the_tokens_are_the_same_for_every_slicing() {
    for version in VERSIONS {
        for input in INPUTS {
            let whole = lex_with_whitespace(version, &[input]);
            for first in 0..=input.len() {
                for second in first..=input.len() {
                    let pieces = [&input[..first], &input[first..second], &input[second..]];
                    assert_eq!(
                        lex_with_whitespace(version, &pieces).tokens,
                        whole.tokens,
                        "{:?} cut at {first} and {second} under {version:?}",
                        show(input)
                    );
                }
            }
            let bytes: Vec<&[u8]> = input.chunks(1).collect();
            assert_eq!(
                lex_with_whitespace(version, &bytes).tokens,
                whole.tokens,
                "{:?} byte by byte under {version:?}",
                show(input)
            );
        }
    }
}

// --- A consumer that does not take them sees everything else unchanged ---

#[test]
fn the_other_tokens_are_the_same_without_whitespace_and_comments() {
    for version in VERSIONS {
        for input in INPUTS {
            let with = lex_with_whitespace(version, &[input]);
            let without = lex_without_whitespace(version, &[input]);
            let kept: Vec<LexedToken> = with
                .tokens
                .iter()
                .filter(|token| !is_whitespace_or_comment(token))
                .cloned()
                .collect();
            assert_eq!(kept, without.tokens, "{:?} under {version:?}", show(input));
            assert!(
                !without.tokens.iter().any(is_whitespace_or_comment),
                "whitespace or a comment handed over unasked in {:?}",
                show(input)
            );
            assert_eq!(with.locations, without.locations, "{:?}", show(input));
        }
    }
}

#[test]
fn lexical_errors_are_the_same_with_whitespace_and_comments() {
    let inputs: [&[u8]; 8] = [
        b" \n #q",
        b"; c\n  \"open",
        b"\n\n |open ; c",
        b" a|b| ",
        b"; c\r\n\t01 ",
        b"  :",
        b" \n|a|b",
        b";\n \x00",
    ];
    for version in VERSIONS {
        for input in inputs {
            let with = lex_with_whitespace(version, &[input]);
            let without = lex_without_whitespace(version, &[input]);
            assert_ne!(with.error, None, "{:?} under {version:?}", show(input));
            assert_eq!(
                with.error,
                without.error,
                "{:?} under {version:?}",
                show(input)
            );
            // and for every cut of the input in two
            for cut in 0..=input.len() {
                let pieces = [&input[..cut], &input[cut..]];
                assert_eq!(
                    lex_with_whitespace(version, &pieces).error,
                    with.error,
                    "{:?} cut at {cut} under {version:?}",
                    show(input)
                );
            }
        }
    }
}

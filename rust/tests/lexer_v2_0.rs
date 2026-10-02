//! Public-API tests of the lexer under SMT-LIB 2.0, whose string literals
//! differ from those of the later versions: `\"` and `\\` are escape
//! sequences, and a double quote always ends the literal.
//!
//! Every input is lexed whole, in every two-piece split and byte by byte,
//! and must give the same tokens or the same error each time.

use std::convert::Infallible;
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtLocation,
    read::lexer::{LexError, Lexer, LexerErrorKind},
    token::{SmtVersion, TokenCursor, TokenHandler, TokenType},
};

/// Expected location as `(offset, line, column)`.
type Loc = (u64, u64, u64);

fn loc(location: SmtLocation) -> Loc {
    (location.offset(), location.line(), location.column())
}

/// An owned copy of a token: its type, content, and the start and end of its span.
type OwnedToken = (TokenType, Vec<u8>, Loc, Loc);

/// The tokens of an input, or the kind and the span of the lexer error.
type Outcome = Result<Vec<OwnedToken>, (LexerErrorKind, Loc, Loc)>;

struct CollectTokens(Vec<OwnedToken>);

impl TokenHandler for &mut CollectTokens {
    type Result = Infallible;
    type Error = Infallible;

    fn handle_tokens(
        &mut self,
        cursor: &mut TokenCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        while let Some(token) = cursor.next() {
            let span = token.span();
            self.0.push((
                token.ty(),
                token.content().to_vec(),
                loc(span.start()),
                loc(span.end()),
            ));
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Lexes the pieces and the end of the input under the version.
fn lex_pieces(pieces: &[&[u8]], version: SmtVersion) -> Outcome {
    let mut collected = CollectTokens(Vec::new());
    let mut lexer = Lexer::new(&mut collected, version);
    let failed = |err| match err {
        LexError::Lexer(err) => (*err.kind(), loc(err.span().start()), loc(err.span().end())),
        LexError::Handler(never) => match never {},
    };
    for piece in pieces {
        let flow = lexer.lex_slice(piece).map_err(failed)?;
        assert!(flow.is_continue(), "the collecting handler never finishes");
    }
    let flow = lexer.lex_eof().map_err(failed)?;
    assert!(flow.is_continue(), "the collecting handler never finishes");
    drop(lexer);
    Ok(collected.0)
}

/// Lexes the input whole, in every two-piece split and byte by byte,
/// requires the same outcome each time, and returns it.
#[track_caller]
fn lex(input: &[u8], version: SmtVersion) -> Outcome {
    let whole = lex_pieces(&[input], version);
    for at in 0..=input.len() {
        let (first, second) = input.split_at(at);
        assert_eq!(
            lex_pieces(&[first, second], version),
            whole,
            "the outcome differs when {:?} is split at {at}",
            input.escape_ascii().to_string()
        );
    }
    let bytes: Vec<&[u8]> = input.chunks(1).collect();
    assert_eq!(
        lex_pieces(&bytes, version),
        whole,
        "the outcome differs when {:?} is fed byte by byte",
        input.escape_ascii().to_string()
    );
    whole
}

/// The types and contents of the tokens of an input that must lex, without the EOF token.
#[track_caller]
fn contents(input: &[u8], version: SmtVersion) -> Vec<(TokenType, Vec<u8>)> {
    let mut tokens = lex(input, version).unwrap_or_else(|err| {
        panic!(
            "{:?} must lex in {version:?}: {err:?}",
            input.escape_ascii().to_string()
        )
    });
    let eof = tokens.pop().expect("the EOF token is always produced");
    assert_eq!(eof.0, TokenType::EndOfFile);
    tokens
        .into_iter()
        .map(|(ty, content, _, _)| (ty, content))
        .collect()
}

fn string(content: &[u8]) -> (TokenType, Vec<u8>) {
    (TokenType::String, content.to_vec())
}

fn symbol(content: &[u8]) -> (TokenType, Vec<u8>) {
    (TokenType::UnquotedSymbol, content.to_vec())
}

#[test]
fn the_two_escapes_denote_their_second_character() {
    for (literal, content) in [
        // no escape
        (&br#""""#[..], &b""[..]),
        (br#""plain text""#, b"plain text"),
        // an escaped quote does not end the literal
        (br#""\"""#, b"\""),
        (br#""x\"y""#, b"x\"y"),
        (br#""\"x\"""#, b"\"x\""),
        (br#""She said: \"Hello!\"""#, b"She said: \"Hello!\""),
        // an escaped backslash lets a backslash end the literal
        (br#""\\""#, b"\\"),
        (br#""x\\""#, b"x\\"),
        (br#""Here is a backslash: \\""#, b"Here is a backslash: \\"),
        // the escapes next to each other
        (br#""\\\"""#, b"\\\""),
        (br#""\"\\""#, b"\"\\"),
        (br#""\\\\""#, b"\\\\"),
        (br#""\\\\\"\"\\""#, b"\\\\\"\"\\"),
        (br#""a\\\"b\"\\c""#, b"a\\\"b\"\\c"),
    ] {
        // the literal alone, and between other tokens
        assert_eq!(
            contents(literal, SmtVersion::V2_0),
            [string(content)],
            "{:?}",
            literal.escape_ascii().to_string()
        );
        let input = [b"(a ", literal, b" b)"].concat();
        assert_eq!(
            contents(&input, SmtVersion::V2_0)[2],
            string(content),
            "{:?}",
            input.escape_ascii().to_string()
        );
    }
}

#[test]
fn a_backslash_before_another_character_is_an_ordinary_character() {
    // there are no other escape sequences: the backslash and what follows it are content
    for (literal, content) in [
        (&br#""\n""#[..], &br#"\n"#[..]),
        (br#""one \n two""#, br#"one \n two"#),
        (br#""\012 \x0A \u0008""#, br#"\012 \x0A \u0008"#),
        (br#""\a\\b\"c\d""#, br#"\a\b"c\d"#),
        (br#""\ ""#, br#"\ "#),
        (br#""\|""#, br#"\|"#),
        (b"\"\\\t\"", b"\\\t"),
        (b"\"\\\xC3\xA9\"", b"\\\xC3\xA9"),
    ] {
        assert_eq!(
            contents(literal, SmtVersion::V2_0),
            [string(content)],
            "{:?}",
            literal.escape_ascii().to_string()
        );
    }
}

#[test]
fn the_other_content_of_a_string_is_as_in_the_later_versions() {
    // a bar, whitespace including line breaks, and bytes from 128 on are content
    // in every version
    for literal in [
        &b"\"a|b\""[..],
        b"\"|\"",
        b"\"||x||\"",
        b"\"a\tb\"",
        b"\"a\nb\"",
        b"\"a\r\nb\"",
        b"\"\n\"",
        b"\"h\xC3\xA9llo \xE4\xB8\x96\"",
        b"\"lone \xE9 byte\"",
        b"\"(not a comment ; nor a list)\"",
    ] {
        let content = &literal[1..literal.len() - 1];
        for version in [SmtVersion::V2_0, SmtVersion::V2_7] {
            assert_eq!(
                contents(literal, version),
                [string(content)],
                "{:?} in {version:?}",
                literal.escape_ascii().to_string()
            );
        }
    }
}

#[test]
fn line_breaks_in_strings_are_counted() {
    // a line feed in a string starts a new line, also right after a backslash;
    // the token after the string is on the third line (zero-based 2)
    for input in [&b"\"a\nb\"\n x"[..], b"\"a\\\nb\"\n x", b"\"\\\\\n\"\n x"] {
        let tokens = lex(input, SmtVersion::V2_0).expect("the input must lex");
        let string_end = (input.len() as u64 - 3, 1, tokens[0].3.2);
        assert_eq!(tokens[0].2, (0, 0, 0));
        assert_eq!(
            tokens[0].3,
            string_end,
            "{:?}",
            input.escape_ascii().to_string()
        );
        let x_start = input.len() as u64 - 1;
        assert_eq!(tokens[1].2, (x_start, 2, 1));
        assert_eq!(tokens[1].3, (x_start + 1, 2, 2));
    }
}

#[test]
fn the_span_of_a_string_covers_its_quotes_and_escapes() {
    let input = br#"(echo "x\"\\y" z)"#;
    let tokens = lex(input, SmtVersion::V2_0).expect("the input must lex");
    assert_eq!(
        tokens[2],
        (
            TokenType::String,
            b"x\"\\y".to_vec(),
            (6, 0, 6),
            (14, 0, 14)
        )
    );
    assert_eq!(tokens[3].2, (15, 0, 15));
}

#[test]
fn the_same_text_is_cut_differently_by_the_two_string_regimes() {
    use LexerErrorKind::*;
    use TokenType::*;

    // an escaped quote: one string in 2.0; from 2.5 on the string ends at its
    // second quote, right before the rest
    assert_eq!(
        contents(br#""a\"b" c"#, SmtVersion::V2_0),
        [string(b"a\"b"), symbol(b"c")]
    );
    assert_eq!(
        lex(br#""a\"b" c"#, SmtVersion::V2_7),
        Err((MissingDelimiter, (0, 0, 0), (5, 0, 5)))
    );
    assert_eq!(
        contents(br#""a\" b"#, SmtVersion::V2_7),
        [string(b"a\\"), symbol(b"b")]
    );
    assert_eq!(
        lex(br#""a\" b"#, SmtVersion::V2_0),
        Err((UnclosedStringLiteral, (0, 0, 0), (6, 0, 6)))
    );

    // a doubled quote: one string from 2.5 on; two glued strings in 2.0
    assert_eq!(
        contents(br#""a""b" c"#, SmtVersion::V2_7),
        [string(b"a\"b"), symbol(b"c")]
    );
    assert_eq!(
        lex(br#""a""b" c"#, SmtVersion::V2_0),
        Err((MissingDelimiter, (0, 0, 0), (4, 0, 4)))
    );
    assert_eq!(
        contents(br#""a" "b" c"#, SmtVersion::V2_0),
        [string(b"a"), string(b"b"), symbol(b"c")]
    );
    assert_eq!(
        lex(br#""""""#, SmtVersion::V2_0),
        Err((MissingDelimiter, (0, 0, 0), (3, 0, 3)))
    );

    // a backslash at the end: it ends the string from 2.5 on and escapes the quote in 2.0
    assert_eq!(
        contents(br#""abc\" d"#, SmtVersion::V2_7),
        [string(b"abc\\"), symbol(b"d")]
    );
    assert_eq!(
        lex(br#""abc\""#, SmtVersion::V2_0),
        Err((UnclosedStringLiteral, (0, 0, 0), (6, 0, 6)))
    );

    // a doubled backslash is one backslash in 2.0 and two from 2.5 on
    assert_eq!(contents(br#""\\""#, SmtVersion::V2_0), [string(b"\\")]);
    assert_eq!(contents(br#""\\""#, SmtVersion::V2_7), [string(b"\\\\")]);

    // 2.5 and 2.6 read strings like 2.7
    for version in [SmtVersion::V2_5, SmtVersion::V2_6] {
        assert_eq!(
            contents(br#""a""b\" c"#, version),
            [
                (String, b"a\"b\\".to_vec()),
                (UnquotedSymbol, b"c".to_vec())
            ]
        );
    }
}

#[test]
fn a_string_must_be_closed_and_delimited() {
    use LexerErrorKind::*;

    for (input, kind, end) in [
        // the end of the input inside the string, also right after a backslash
        (&br#""abc"#[..], UnclosedStringLiteral, 4),
        (br#"""#, UnclosedStringLiteral, 1),
        (br#""a\"#, UnclosedStringLiteral, 3),
        (br#""a\\"#, UnclosedStringLiteral, 4),
        (br#""a\"b"#, UnclosedStringLiteral, 5),
        // a token glued to the closing quote
        (br#""a"b"#, MissingDelimiter, 4),
        (br#""a\\"b"#, MissingDelimiter, 6),
        (br#""a"|b|"#, MissingDelimiter, 4),
        (br#""a":k"#, MissingDelimiter, 4),
        (br#""a"1"#, MissingDelimiter, 4),
    ] {
        assert_eq!(
            lex(input, SmtVersion::V2_0),
            Err((kind, (0, 0, 0), (end, 0, end))),
            "{:?}",
            input.escape_ascii().to_string()
        );
    }

    // the delimiters after a string are those of any token
    for delimiter in [&b" "[..], b"\t", b"\n", b"\r", b"(", b")", b";c", b""] {
        let input = [br#""a\"""#, delimiter].concat();
        let tokens = lex(&input, SmtVersion::V2_0).expect("a delimited string must lex");
        assert_eq!(tokens[0].0, TokenType::String);
        assert_eq!(tokens[0].1, b"a\"");
        assert_eq!(tokens[0].3.0, 5);
    }
}

#[test]
fn a_control_character_is_forbidden_in_a_string() {
    // also right after a backslash, where it is no escape
    for forbidden in [0u8, 1, 8, 11, 12, 27, 31, 127] {
        for prefix in [&b"\"ab"[..], b"\"a\\", b"\"\\\\"] {
            let input = [prefix, &[forbidden], b"c\""].concat();
            assert_eq!(
                lex(&input, SmtVersion::V2_0),
                Err((LexerErrorKind::ForbiddenCharInString, (0, 0, 0), (4, 0, 4))),
                "{:?}",
                input.escape_ascii().to_string()
            );
        }
    }
}

#[test]
fn everything_but_strings_lexes_as_in_the_later_versions() {
    for input in [
        &b"(set-logic QF_BV)\n(check-sat)\n"[..],
        b"7 7.0 #x1F #b10 :kw |q s| sym + <= .8 ~!@$%^&*_-+=<>.?/",
        b"; a comment with \"a quote, a \\ and h\xC3\xA9llo\n(x)",
        b"|quoted \" with a quote|  |and \xE9 a byte| || |a\nb|",
        b"(f\t(g\r\nx) ; end\r y)",
        b"\"no escapes in this string\" x",
    ] {
        let reference = lex(input, SmtVersion::V2_7).expect("the input must lex");
        for version in [SmtVersion::V2_0, SmtVersion::V2_5, SmtVersion::V2_6] {
            assert_eq!(
                lex(input, version).as_ref(),
                Ok(&reference),
                "{:?} in {version:?}",
                input.escape_ascii().to_string()
            );
        }
    }

    // and so do the errors outside of strings
    for input in [
        &b"|a\\b|"[..],
        b"a\\b",
        b"007",
        b"1.x",
        b"#y",
        b"|unclosed",
        b"1a",
    ] {
        let reference = lex(input, SmtVersion::V2_7);
        assert!(reference.is_err(), "{:?}", input.escape_ascii().to_string());
        assert_eq!(
            lex(input, SmtVersion::V2_0),
            reference,
            "{:?}",
            input.escape_ascii().to_string()
        );
    }
}

#[test]
fn a_long_string_of_escapes_is_lexed_in_one_pass() {
    // every escape ends a run; the work must stay proportional to the length
    let pairs = 200_000;
    let mut input = Vec::with_capacity(4 * pairs + 2);
    input.push(b'"');
    for _ in 0..pairs {
        input.extend_from_slice(br#"\\\""#);
    }
    input.push(b'"');
    let tokens = lex_pieces(&[&input], SmtVersion::V2_0).expect("the string must lex");
    assert_eq!(tokens[0].0, TokenType::String);
    assert_eq!(tokens[0].1, b"\\\"".repeat(pairs));
    // also when the escapes are cut by the slices at every possible place
    for piece in [1, 2, 3, 5] {
        let pieces: Vec<&[u8]> = input.chunks(piece).collect();
        assert_eq!(lex_pieces(&pieces, SmtVersion::V2_0).as_ref(), Ok(&tokens));
    }
}

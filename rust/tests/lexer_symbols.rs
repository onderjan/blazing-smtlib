//! Public-API tests of symbol tokens: the lexer produces unquoted and quoted
//! symbols alike, whatever they spell, with the content of a quoted symbol
//! excluding its pipes; `SmtSyntaxToken::from_lexer_token` classifies an unquoted symbol
//! spelled like a reserved word as that reserved word, and a quoted one never.
//! The same holds wherever the input is cut into slices.

mod lex_backend;
mod reserved_words;

use blazing_smtlib::{SmtVersion, token::SmtTokenCategory};

// What `SmtSyntaxToken::from_lexer_token` says about a token, owned.
use lex_backend::LexedKind as Kind;
use reserved_words::reserved_words;

/// An owned copy of everything observable about a token.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Lexed {
    ty: SmtTokenCategory,
    content: Vec<u8>,
    kind: Kind,
    /// The span as byte offsets.
    span: (u64, u64),
}

/// Lexes the input as the given pieces, then the end of the input, with the
/// lexer under test, requiring success, and returns every token.
#[track_caller]
fn lex_pieces(pieces: &[&[u8]]) -> Vec<Lexed> {
    let run = lex_backend::lex_pieces(SmtVersion::V2_7, pieces);
    if let Some(err) = run.error {
        panic!("{:?} must lex, got {err:?}", text(&pieces.concat()));
    }
    run.tokens
        .into_iter()
        .map(|token| Lexed {
            ty: token.ty,
            content: token.content,
            kind: token.kind,
            span: (token.start.0, token.end.0),
        })
        .collect()
}

#[track_caller]
fn lex(input: &[u8]) -> Vec<Lexed> {
    lex_pieces(&[input])
}

fn text(input: &[u8]) -> String {
    String::from_utf8_lossy(input).into_owned()
}

fn lexed(ty: SmtTokenCategory, content: &[u8], kind: Kind, span: (u64, u64)) -> Lexed {
    Lexed {
        ty,
        content: content.to_vec(),
        kind,
        span,
    }
}

#[test]
fn symbols_are_unquoted_or_quoted_without_pipes() {
    use SmtTokenCategory::{EndOfFile, QuotedSymbol, UnquotedSymbol};
    fn symbol(content: &[u8]) -> Kind {
        Kind::Symbol(content.to_vec())
    }
    assert_eq!(
        lex(b"x |x| || |a b| |a\nb| +-*"),
        [
            lexed(UnquotedSymbol, b"x", symbol(b"x"), (0, 1)),
            lexed(QuotedSymbol, b"x", symbol(b"x"), (2, 5)),
            lexed(QuotedSymbol, b"", symbol(b""), (6, 8)),
            lexed(QuotedSymbol, b"a b", symbol(b"a b"), (9, 14)),
            lexed(QuotedSymbol, b"a\nb", symbol(b"a\nb"), (15, 20)),
            lexed(UnquotedSymbol, b"+-*", symbol(b"+-*"), (21, 24)),
            lexed(EndOfFile, b"", Kind::EndOfFile, (24, 24)),
        ]
    );
}

#[test]
fn unquoted_reserved_words_are_unquoted_symbols_classified_as_reserved() {
    for word in reserved_words() {
        let tokens = lex(word.as_bytes());
        let end = word.len() as u64;
        assert_eq!(
            tokens.len(),
            2,
            "one token and the end of input for {word:?}"
        );
        let token = &tokens[0];
        assert_eq!(
            (token.ty, token.content.as_slice(), token.span),
            (SmtTokenCategory::UnquotedSymbol, word.as_bytes(), (0, end)),
            "token for {word:?}"
        );
        assert!(
            matches!(token.kind, Kind::Reserved(reserved) if reserved.as_str() == word),
            "{word:?} must be classified as its reserved word, got {:?}",
            token.kind
        );
    }
}

#[test]
fn quoted_reserved_words_are_quoted_symbols_never_classified_as_reserved() {
    for word in reserved_words() {
        let input = format!("|{word}|");
        let end = input.len() as u64;
        assert_eq!(
            lex(input.as_bytes())[0],
            lexed(
                SmtTokenCategory::QuotedSymbol,
                word.as_bytes(),
                Kind::Symbol(word.as_bytes().to_vec()),
                (0, end)
            ),
            "token for {input:?}"
        );
    }
}

#[test]
fn keywords_spelled_like_reserved_words_are_keywords() {
    for word in reserved_words() {
        let input = format!(":{word}");
        let end = input.len() as u64;
        assert_eq!(
            lex(input.as_bytes())[0],
            lexed(
                SmtTokenCategory::Keyword,
                word.as_bytes(),
                Kind::Keyword(word.as_bytes().to_vec()),
                (0, end)
            ),
            "token for {input:?}"
        );
    }
}

#[test]
fn end_of_input_has_no_content_and_an_empty_span_at_the_end() {
    let input = b"(a)\n  b ";
    assert_eq!(
        lex(input).last(),
        Some(&lexed(
            SmtTokenCategory::EndOfFile,
            b"",
            Kind::EndOfFile,
            (8, 8)
        ))
    );
    // the end-of-input location with its line and column, which the
    // offsets alone do not show
    let run = lex_backend::lex_whole(SmtVersion::V2_7, input);
    let ends: Vec<_> = run
        .tokens
        .iter()
        .filter(|token| token.ty == SmtTokenCategory::EndOfFile)
        .map(|token| token.end)
        .collect();
    assert_eq!(ends, [(8, 1, 4)], "end of input as (offset, line, column)");
}

#[test]
fn symbols_are_the_same_across_slice_boundaries() {
    // a symbol cut by a slice boundary is continued from the lexer's own
    // buffer, which must keep whether it was quoted and what it contains
    let inputs: [&[u8]; 4] = [
        b"(|let| |_| |assert| |a\nb| ||) |STRING| let assert",
        b"|check-sat-assuming|",
        b"check-sat-assuming",
        b"(declare-fun |par| () x) :let",
    ];
    for input in inputs {
        let reference = lex(input);
        let mut splits: Vec<Vec<&[u8]>> = (0..=input.len())
            .map(|at| {
                let (first, second) = input.split_at(at);
                vec![first, second]
            })
            .collect();
        splits.push(input.chunks(1).collect());
        for pieces in splits {
            assert_eq!(
                lex_pieces(&pieces),
                reference,
                "{:?} fed as pieces of lengths {:?}",
                text(input),
                pieces.iter().map(|piece| piece.len()).collect::<Vec<_>>()
            );
        }
    }
    // the reference itself is right, so the comparison above means something
    assert_eq!(
        lex(b"|check-sat-assuming|")[0].kind,
        Kind::Symbol(b"check-sat-assuming".to_vec())
    );
    assert!(matches!(
        lex(b"check-sat-assuming")[0].kind,
        Kind::Reserved(reserved) if reserved.as_str() == "check-sat-assuming"
    ));
}

//! Public-API tests of the tokens a user keeps and hands over: owned syntax
//! tokens, the owned token list, the cursor over tokens put into it, and
//! the values that put their tokens into that cursor.
//!
//! They check the Rust interface itself and call the library directly.

use std::convert::Infallible;
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtSyntaxChecker, SmtVersion,
    lexer::{SmtLexer, SmtLexerCursor},
    lexicon::{
        SmtBinDigits, SmtComment, SmtDecimal, SmtGeneralReserved, SmtHexDigits, SmtKeyword,
        SmtNumeral, SmtReserved, SmtStringContent, SmtSymbol, SmtWhitespace,
    },
    parser::{SmtParse, SmtParseState, SmtTermParser},
    token::{
        SmtAppendTokens, SmtConsume, SmtConsumeFrom, SmtCursor, SmtToken, SmtTokenBuf,
        SmtTokensBuf, SmtTokensCursor,
    },
};

/// An input with every kind of token, empty ones included, with whitespace
/// and comments between them.
const EVERY_KIND: &[u8] = b"(assert (= x #x1F #b01 12 1.5 :kw |q\ns| || \"\" \"a\"\"b\" |assert|))\
    \t; comment\n(par lambda) x;last";

/// A consumer that keeps every token, whitespace and comments included, as
/// it is debugged, and in an owned token list.
#[derive(Default)]
struct Keep {
    debugged: Vec<String>,
    tokens: SmtTokensBuf,
}

impl SmtConsume for Keep {
    type Result = (Vec<String>, SmtTokensBuf);
    type Error = Infallible;
    const IS_CONCRETE: bool = true;
}

impl<'a> SmtConsumeFrom<SmtLexerCursor<'a>> for Keep {
    fn consume(
        &mut self,
        cursor: &mut SmtLexerCursor<'a>,
    ) -> Result<ControlFlow<Self::Result>, Infallible> {
        while let Some(token) = cursor.next() {
            let token = cursor.syntax(&token);
            self.debugged.push(format!("{token:?}"));
            self.tokens.push(token);
            if matches!(token, SmtToken::EndOfFile) {
                let kept = std::mem::take(self);
                return Ok(ControlFlow::Break((kept.debugged, kept.tokens)));
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Lexes the input in 2.7 into every token as debugged and as an owned
/// token list, the end of the input included.
fn keep(input: &[u8]) -> (Vec<String>, SmtTokensBuf) {
    SmtLexer::new(Keep::default(), SmtVersion::V2_7)
        .lex_all(input)
        .expect("the test input should lex")
        .into_value()
}

/// The tokens as debugged.
fn debugged<'a>(tokens: impl IntoIterator<Item = SmtToken<'a>>) -> Vec<String> {
    tokens
        .into_iter()
        .map(|token| format!("{token:?}"))
        .collect()
}

/// Takes every token the cursor has left, as debugged.
fn drain(cursor: &mut SmtTokensCursor<'_>) -> Vec<String> {
    let mut tokens = Vec::new();
    while let Some(token) = cursor.next() {
        tokens.push(format!("{:?}", cursor.syntax(&token)));
    }
    tokens
}

/// The tokens the value appends to an empty cursor, as debugged.
fn appended<V: SmtAppendTokens + ?Sized>(value: &V) -> Vec<String> {
    let mut cursor = SmtTokensCursor::new(SmtVersion::V2_7);
    value.append_tokens(&mut cursor);
    drain(&mut cursor)
}

#[test]
fn a_token_owned_and_viewed_again_is_the_token() {
    let (expected, tokens) = keep(EVERY_KIND);
    let owned: Vec<SmtTokenBuf> = tokens.iter().map(SmtToken::into_owned).collect();
    assert_eq!(debugged(owned.iter().map(SmtTokenBuf::view)), expected);
}

#[test]
fn a_token_list_keeps_every_pushed_token_in_order() {
    let (expected, tokens) = keep(EVERY_KIND);
    assert_eq!(tokens.len(), expected.len());
    assert!(!tokens.is_empty());
    assert_eq!(tokens.iter().len(), expected.len());
    assert_eq!(debugged(tokens.iter()), expected);
    let by_index = (0..tokens.len()).map(|index| tokens.get(index).expect("within the list"));
    assert_eq!(debugged(by_index), expected);
    assert!(tokens.get(tokens.len()).is_none());
    // a copy keeps the same tokens
    assert_eq!(debugged(tokens.clone().iter()), expected);
}

#[test]
fn a_cleared_token_list_is_empty_and_takes_new_tokens() {
    let (_, mut tokens) = keep(EVERY_KIND);
    tokens.clear();
    assert_eq!(tokens.len(), 0);
    assert!(tokens.is_empty());
    assert!(tokens.get(0).is_none());
    let (expected, again) = keep(b"(check-sat) |a b| y");
    for token in again.iter() {
        tokens.push(token);
    }
    assert_eq!(debugged(tokens.iter()), expected);
    assert!(SmtTokensBuf::new().is_empty() && SmtTokensBuf::default().is_empty());
}

#[test]
fn a_tokens_cursor_hands_over_the_pushed_tokens_in_order() {
    let (expected, tokens) = keep(EVERY_KIND);
    for version in [SmtVersion::V2_0, SmtVersion::V2_7] {
        let mut cursor = SmtTokensCursor::new(version);
        assert!(cursor.is_empty() && cursor.peek().is_none());
        for token in tokens.iter() {
            cursor.push(token);
        }
        assert_eq!(cursor.version(), version);
        let mut handed_over = Vec::new();
        while !cursor.is_empty() {
            let peeked = cursor.peek().expect("a token is left");
            let token = cursor.next().expect("a token is left");
            assert_eq!(format!("{peeked:?}"), format!("{token:?}"));
            handed_over.push(format!("{:?}", cursor.syntax(&token)));
        }
        assert_eq!(handed_over, expected);
        assert!(cursor.next().is_none() && cursor.peek().is_none());
    }
}

#[test]
fn a_tokens_cursor_keeps_its_own_version_refuses_others_and_keeps_its_tokens() {
    let (expected, tokens) = keep(b"(echo \"a\"\"b\") x");
    let mut cursor = SmtTokensCursor::new(SmtVersion::V2_6);
    for token in tokens.iter() {
        cursor.push(token);
    }
    // the tokens were classified under the cursor's version
    assert_eq!(cursor.set_version(SmtVersion::V2_6), Ok(()));
    assert_eq!(cursor.version(), SmtVersion::V2_6);
    for version in [SmtVersion::V2_0, SmtVersion::V2_5, SmtVersion::V2_7] {
        assert!(cursor.set_version(version).is_err(), "{version:?}");
        assert_eq!(cursor.version(), SmtVersion::V2_6);
    }
    assert_eq!(drain(&mut cursor), expected);
}

#[test]
fn discarding_skips_the_tokens_before_the_next_end_of_the_input() {
    let x = SmtSymbol::new_unquoted(b"x").expect("a symbol");
    let y = SmtSymbol::new_unquoted(b"y").expect("a symbol");
    let (_, ab) = keep(b"(a b)");
    let mut cursor = SmtTokensCursor::new(SmtVersion::V2_7);
    for token in [
        SmtToken::ParenOpen,
        SmtToken::Symbol(x),
        SmtToken::ParenClose,
        SmtToken::EndOfFile,
        SmtToken::Symbol(y),
        SmtToken::EndOfFile,
    ] {
        cursor.push(token);
    }
    cursor.next();
    cursor.discard_rest();
    // the end of the input is the first token after discarding, and what
    // follows it stays
    assert_eq!(
        drain(&mut cursor),
        debugged([
            SmtToken::EndOfFile,
            SmtToken::Symbol(y),
            SmtToken::EndOfFile
        ])
    );
    // with no end of the input ahead, every token is discarded
    cursor.clear();
    cursor.push(SmtToken::Symbol(x));
    cursor.push(SmtToken::Symbol(y));
    cursor.discard_rest();
    assert!(cursor.is_empty());
    // and so is every token pushed or appended until the end of the input:
    // the list ends with one, which is kept
    cursor.push(SmtToken::Symbol(x));
    ab.append_tokens(&mut cursor);
    assert_eq!(drain(&mut cursor), debugged([SmtToken::EndOfFile]));
    // the end of the input is kept with what follows it
    cursor.push(SmtToken::Symbol(x));
    cursor.discard_rest();
    cursor.push(SmtToken::Symbol(x));
    assert!(cursor.is_empty());
    cursor.push(SmtToken::EndOfFile);
    cursor.push(SmtToken::Symbol(y));
    assert_eq!(
        drain(&mut cursor),
        debugged([SmtToken::EndOfFile, SmtToken::Symbol(y)])
    );
    // discarding right before the end of the input keeps it
    cursor.push(SmtToken::EndOfFile);
    cursor.discard_rest();
    cursor.push(SmtToken::Symbol(y));
    assert_eq!(
        drain(&mut cursor),
        debugged([SmtToken::EndOfFile, SmtToken::Symbol(y)])
    );
    // clearing ends discarding
    cursor.discard_rest();
    cursor.clear();
    cursor.push(SmtToken::Symbol(x));
    assert_eq!(drain(&mut cursor), debugged([SmtToken::Symbol(x)]));
}

#[test]
fn consuming_all_and_clearing_empty_the_cursor() {
    let (expected, tokens) = keep(b"(a b) c");
    let mut cursor = SmtTokensCursor::new(SmtVersion::V2_7);
    for token in tokens.iter() {
        cursor.push(token);
    }
    cursor.next();
    cursor.consume_all();
    assert!(cursor.is_empty() && cursor.next().is_none());
    // tokens pushed after consuming all are handed over
    cursor.push(SmtToken::ParenOpen);
    assert_eq!(drain(&mut cursor), debugged([SmtToken::ParenOpen]));
    // clearing removes the consumed and the unconsumed tokens alike
    for token in tokens.iter() {
        cursor.push(token);
    }
    cursor.next();
    cursor.clear();
    assert!(cursor.is_empty());
    for token in tokens.iter() {
        cursor.push(token);
    }
    assert_eq!(drain(&mut cursor), expected);
}

#[test]
fn a_parser_reads_from_a_tokens_cursor_and_leaves_the_rest() {
    let (_, tokens) = keep(b"(f x 1) (g)");
    let mut cursor = SmtTokensCursor::new(SmtVersion::V2_7);
    // an abstract stream: no whitespace or comments
    for token in tokens
        .iter()
        .filter(|token| !matches!(token, SmtToken::Whitespace(_) | SmtToken::Comment(_)))
    {
        cursor.push(token);
    }
    let flow = SmtTermParser::default()
        .parse(
            &mut SmtSyntaxChecker,
            &mut SmtParseState::new(),
            &mut cursor,
        )
        .expect("the term should parse");
    assert!(matches!(flow, ControlFlow::Break(_)));
    assert_eq!(
        drain(&mut cursor),
        debugged([
            SmtToken::ParenOpen,
            SmtToken::Symbol(SmtSymbol::new_unquoted(b"g").expect("a symbol")),
            SmtToken::ParenClose,
            SmtToken::EndOfFile,
        ])
    );
}

#[test]
fn a_plain_value_appends_the_token_of_its_kind() {
    let numeral = SmtNumeral::new(b"42").expect("a numeral");
    let decimal = SmtDecimal::new(b"4.2").expect("a decimal");
    let hex = SmtHexDigits::new(b"2A").expect("hexadecimal digits");
    let bin = SmtBinDigits::new(b"101").expect("binary digits");
    let string = SmtStringContent::new(b"a b").expect("string content");
    let keyword = SmtKeyword::new(b"named").expect("a keyword");
    let unquoted = SmtSymbol::new_unquoted(b"x").expect("a symbol");
    let quoted = SmtSymbol::new_quoted(b"x").expect("a symbol");
    let whitespace = SmtWhitespace::new(b" \n").expect("whitespace");
    let comment = SmtComment::new(b" note").expect("a comment");

    let cases: [(Vec<String>, Vec<String>, SmtToken<'_>); 10] = [
        (
            appended(&numeral),
            appended(&numeral.into_owned()),
            SmtToken::Numeral(numeral),
        ),
        (
            appended(&decimal),
            appended(&decimal.into_owned()),
            SmtToken::Decimal(decimal),
        ),
        (
            appended(&hex),
            appended(&hex.into_owned()),
            SmtToken::Hexadecimal(hex),
        ),
        (
            appended(&bin),
            appended(&bin.into_owned()),
            SmtToken::Binary(bin),
        ),
        (
            appended(&string),
            appended(&string.into_owned()),
            SmtToken::String(string),
        ),
        (
            appended(&keyword),
            appended(&keyword.into_owned()),
            SmtToken::Keyword(keyword),
        ),
        (
            appended(&unquoted),
            appended(&unquoted.into_owned()),
            SmtToken::Symbol(unquoted),
        ),
        (
            appended(&quoted),
            appended(&quoted.into_owned()),
            SmtToken::Symbol(quoted),
        ),
        (
            appended(&whitespace),
            appended(&whitespace.into_owned()),
            SmtToken::Whitespace(whitespace),
        ),
        (
            appended(&comment),
            appended(&comment.into_owned()),
            SmtToken::Comment(comment),
        ),
    ];
    for (viewed, owned, token) in cases {
        assert_eq!(viewed, debugged([token]));
        assert_eq!(owned, debugged([token]));
    }
}

#[test]
fn a_token_appends_itself_and_a_list_appends_its_tokens_in_order() {
    let (expected, tokens) = keep(EVERY_KIND);
    assert_eq!(appended(&tokens), expected);
    for token in tokens.iter() {
        assert_eq!(appended(&token), debugged([token]));
        assert_eq!(appended(&token.into_owned()), debugged([token]));
    }
    let reserved = SmtReserved::General(SmtGeneralReserved::Let);
    assert_eq!(
        appended(&reserved),
        debugged([SmtToken::Reserved(reserved)])
    );
    // a slice appends each of its values in turn
    let owned: Vec<SmtTokenBuf> = tokens.iter().map(SmtToken::into_owned).collect();
    assert_eq!(appended(owned.as_slice()), expected);
    let lists = [keep(b"(a)").1, SmtTokensBuf::new(), keep(b"b c").1];
    let mut each = Vec::new();
    for list in &lists {
        each.extend(appended(list));
    }
    assert_eq!(appended(lists.as_slice()), each);
    let none: &[SmtTokensBuf] = &[];
    assert!(appended(none).is_empty());
    // an array and a vector append as their slice does
    assert_eq!(appended(&owned), expected);
    assert_eq!(appended(&lists), each);
    let no_tokens: [SmtTokensBuf; 0] = [];
    assert!(appended(&no_tokens).is_empty());
    assert!(appended(&Vec::<SmtTokensBuf>::new()).is_empty());
}

#[test]
fn appending_keeps_the_tokens_already_in_the_cursor_first() {
    let (first, first_tokens) = keep(b"(a b)");
    let (second, second_tokens) = keep(b"c");
    let mut cursor = SmtTokensCursor::new(SmtVersion::V2_7);
    first_tokens.append_tokens(&mut cursor);
    // a consumed token stays consumed after appending
    cursor.next();
    second_tokens.append_tokens(&mut cursor);
    let mut expected = first[1..].to_vec();
    expected.extend(second);
    assert_eq!(drain(&mut cursor), expected);
}

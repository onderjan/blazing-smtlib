//! Tests of writing tokens back as SMT-LIB text, each token by itself: that
//! lexed text is written back as it was, how strings of 2.0 are escaped,
//! that symbols spelling a reserved word are quoted, and the errors of
//! writing.
//!
//! They run against `write_backend`, and read the written text back through
//! `lex_backend`, so that the driver runs them against the Lean port too.

mod lex_backend;
mod reserved_words;
mod write_backend;

use blazing_smtlib::{
    SmtVersion,
    lexicon::{
        SmtBinDigitsBuf, SmtCommentBuf, SmtDecimalBuf, SmtHexDigitsBuf, SmtKeywordBuf,
        SmtNumeralBuf, SmtStringContentBuf, SmtSymbolBuf, SmtWhitespaceBuf,
    },
    token::{SmtReserved, SmtToken, SmtTokenCategory},
};
use lex_backend::Feed;
use write_backend::{Answer, Item, WriteFailure, Writing};

const VERSIONS: [SmtVersion; 4] = [
    SmtVersion::V2_0,
    SmtVersion::V2_5,
    SmtVersion::V2_6,
    SmtVersion::V2_7,
];

/// What a script lexes into: the text its tokens are written back as, and
/// the tokens themselves, without the end of the input.
#[derive(Debug, Default)]
struct WrittenBack {
    text: Vec<u8>,
    tokens: Vec<(SmtTokenCategory, Vec<u8>)>,
}

/// Lexes the whole input in the version, whitespace and comments included,
/// and writes every token back by itself in the version.
fn write_back(version: SmtVersion, input: &[u8]) -> WrittenBack {
    let text = write_backend::written(version, Writing::TokenByToken, &[Item::lex(input)]);
    let lexed = lex_backend::lex_with_whitespace(version, &[Feed::Slice(input), Feed::Eof]);
    assert_eq!(
        lexed.error,
        None,
        "{:?} should lex in {version:?}",
        input.escape_ascii().to_string()
    );
    let tokens = lexed
        .tokens
        .into_iter()
        .filter(|token| token.ty != SmtTokenCategory::EndOfFile)
        .map(|token| (token.ty, token.content))
        .collect();
    WrittenBack { text, tokens }
}

/// Writes the token by itself.
fn written(token: SmtToken<'_>, version: SmtVersion) -> Result<Vec<u8>, WriteFailure> {
    let written = write_backend::write(
        version,
        Writing::TokenByToken,
        false,
        &[Item::write([token])],
    );
    match &written.answers[..] {
        [Answer::Ok] => Ok(written.out),
        [Answer::Failed(failure)] => {
            assert!(
                written.out.is_empty(),
                "a failed token wrote {:?}",
                written.out
            );
            Err(failure.clone())
        }
        other => panic!("one write should be answered once, got {other:?}"),
    }
}

/// Inputs that every version lexes alike, with every kind of token, and
/// whitespace and comments around and between them.
const COMMON_INPUTS: [&[u8]; 14] = [
    b"",
    b"()",
    b" \t\r\n",
    b"(assert (= x #x1F #b01 12 0 1.5 0.0 10.050))",
    b"(set-info :smt-lib-version 2.6)\n(check-sat)\n",
    b"(! x :named |a name|) |q\ns| || |x| x |;| |\"|",
    b"(let ((_ x)) (forall ((x Int)) (exists ((y Int)) (as x Int))))",
    b"\"\" \"a\" \"a ; b\" \"line\nbreak\" \"|pipe|\"",
    b"; comment\n(echo \"hi\") ; trailing\r\n",
    b";;; a ; b\n;\n;",
    b"(par lambda match declare-datatype declare-sort-parameter define-const)",
    b"BINARY DECIMAL HEXADECIMAL NUMERAL STRING :BINARY :let :0",
    b"  (assert\n\t(= x #x1F #b01 12 1.5 :kw |q\ns| \"s\nt\")) ; end\n\n; last",
    b"x;comment at the end without a line feed",
];

/// Inputs that only the versions from 2.5 on lex, or lex differently from
/// 2.0: strings with doubled quotes and with backslashes.
const INPUTS_FROM_2_5: [&[u8]; 6] = [
    b"\"\"\"\"",
    b"\"\"\"\"\"\"",
    b"\"a\"\"b\" \"\"\"x\"\"\"",
    b"\"\\\" \"a\\b\"",
    b"\"\\\"\"\"",
    b"(echo \"say \"\"hi\"\"\") ; done",
];

/// Inputs whose strings use the two escapes of 2.0.
const INPUTS_2_0: [&[u8]; 5] = [
    b"\"\\\"\"",
    b"\"\\\\\"",
    b"\"a\\\\\\\"b\\\"\\\\c\"",
    b"(echo \"say \\\"hi\\\"\") ; done",
    b"\"\\\\\\\\\"",
];

#[test]
fn lexed_text_is_written_back_byte_for_byte() {
    for version in VERSIONS {
        let own: &[&[u8]] = if version == SmtVersion::V2_0 {
            &INPUTS_2_0
        } else {
            &INPUTS_FROM_2_5
        };
        for input in COMMON_INPUTS.iter().chain(own) {
            assert_eq!(
                write_back(version, input).text.escape_ascii().to_string(),
                input.escape_ascii().to_string(),
                "in {version:?}"
            );
        }
    }
}

#[test]
fn a_backslash_in_a_2_0_string_is_written_escaped_and_reads_back_alike() {
    let version = SmtVersion::V2_0;
    for (input, expected) in [
        (&b"\"c\\nd\""[..], &b"\"c\\\\nd\""[..]),
        (b"\"\\a\\\\b\\\"c\\d\"", b"\"\\\\a\\\\b\\\"c\\\\d\""),
        (b"\"\\ \"", b"\"\\\\ \""),
        (b"\"\\|\" x", b"\"\\\\|\" x"),
    ] {
        let first = write_back(version, input);
        assert_eq!(
            first.text.escape_ascii().to_string(),
            expected.escape_ascii().to_string(),
            "written from {:?}",
            input.escape_ascii().to_string()
        );
        // the written text holds the same tokens with the same content,
        // and is written back as it is
        let second = write_back(version, &first.text);
        assert_eq!(
            second.tokens,
            first.tokens,
            "read back from {:?}",
            expected.escape_ascii().to_string()
        );
        assert_eq!(
            second.text.escape_ascii().to_string(),
            expected.escape_ascii().to_string(),
            "written again from {:?}",
            expected.escape_ascii().to_string()
        );
    }
}

#[test]
fn a_symbol_spelling_a_word_reserved_in_the_version_is_written_quoted() {
    for version in VERSIONS {
        for word in reserved_words::reserved_words() {
            let symbol = SmtSymbolBuf::new_unquoted(word.as_bytes().to_vec())
                .expect("a reserved word is a simple symbol");
            let text = written(SmtToken::Symbol(symbol.view()), version)
                .expect("a symbol is written in every version");
            let reserved = SmtReserved::from_bytes(word.as_bytes(), SmtVersion::V2_7)
                .expect("the word is reserved in the latest version");
            let expected = if reserved.is_in_version(version) {
                format!("|{word}|")
            } else {
                word.to_string()
            };
            assert_eq!(
                String::from_utf8_lossy(&text),
                expected,
                "{word} in {version:?}"
            );
            // the text reads back as the symbol, not as the reserved word
            let back = write_back(version, &text);
            let category = if reserved.is_in_version(version) {
                SmtTokenCategory::QuotedSymbol
            } else {
                SmtTokenCategory::UnquotedSymbol
            };
            assert_eq!(
                back.tokens,
                [(category, word.as_bytes().to_vec())],
                "{word} in {version:?}"
            );
        }
    }
}

#[test]
fn words_reserved_in_later_versions_are_quoted_only_from_those_on() {
    for (word, unquoted_until, quoted_from) in [
        ("lambda", SmtVersion::V2_6, SmtVersion::V2_7),
        ("match", SmtVersion::V2_5, SmtVersion::V2_6),
        ("echo", SmtVersion::V2_0, SmtVersion::V2_5),
    ] {
        let symbol = SmtSymbolBuf::new_unquoted(word.as_bytes().to_vec()).expect("a symbol");
        let token = SmtToken::Symbol(symbol.view());
        let before = written(token, unquoted_until).expect("a symbol is written");
        assert_eq!(String::from_utf8_lossy(&before), word);
        let from = written(token, quoted_from).expect("a symbol is written");
        assert_eq!(String::from_utf8_lossy(&from), format!("|{word}|"));
    }
    // a symbol that is not reserved stays as it is, and a quoted one is
    // written quoted even when it need not be
    for version in VERSIONS {
        let plain = SmtSymbolBuf::new_unquoted(b"x".to_vec()).expect("a symbol");
        let text = written(SmtToken::Symbol(plain.view()), version);
        assert_eq!(text.expect("a symbol is written"), b"x");
        let quoted = SmtSymbolBuf::new_quoted(b"x".to_vec()).expect("a symbol");
        let text = written(SmtToken::Symbol(quoted.view()), version);
        assert_eq!(text.expect("a symbol is written"), b"|x|");
    }
}

#[test]
fn a_reserved_word_is_written_only_in_the_versions_that_reserve_it() {
    for version in VERSIONS {
        for word in reserved_words::reserved_words() {
            let reserved = SmtReserved::from_bytes(word.as_bytes(), SmtVersion::V2_7)
                .expect("the word is reserved in the latest version");
            // `written` checks that a refused word writes nothing
            let result = written(SmtToken::Reserved(reserved), version);
            if reserved.is_in_version(version) {
                let text = result.unwrap_or_else(|err| panic!("{word} in {version:?}: {err:?}"));
                assert_eq!(String::from_utf8_lossy(&text), reserved.as_str());
            } else {
                match result {
                    Err(WriteFailure::NotInVersion(refused)) => {
                        assert_eq!(refused, reserved, "{word} in {version:?}")
                    }
                    other => panic!("{word} in {version:?} should be refused, got {other:?}"),
                }
            }
        }
    }
}

#[test]
fn a_failure_of_the_writer_is_an_io_error() {
    let numeral = SmtNumeralBuf::new(b"12".to_vec()).expect("a numeral");
    let decimal = SmtDecimalBuf::new(b"1.5".to_vec()).expect("a decimal");
    let hex = SmtHexDigitsBuf::new(b"1F".to_vec()).expect("hexadecimal digits");
    let bin = SmtBinDigitsBuf::new(b"01".to_vec()).expect("binary digits");
    let string = SmtStringContentBuf::new(b"a\"b\\c".to_vec()).expect("string content");
    let empty_string = SmtStringContentBuf::new(Vec::new()).expect("string content");
    let keyword = SmtKeywordBuf::new(b"kw".to_vec()).expect("a keyword");
    let symbol = SmtSymbolBuf::new_unquoted(b"x".to_vec()).expect("a symbol");
    let quoted = SmtSymbolBuf::new_quoted(b"a b".to_vec()).expect("a symbol");
    let let_word = SmtReserved::from_bytes(b"let", SmtVersion::V2_0).expect("a reserved word");
    let whitespace = SmtWhitespaceBuf::new(b" \n".to_vec()).expect("whitespace");
    let comment = SmtCommentBuf::new(b" c\n".to_vec()).expect("a comment");
    let tokens = [
        SmtToken::ParenOpen,
        SmtToken::ParenClose,
        SmtToken::Numeral(numeral.view()),
        SmtToken::Decimal(decimal.view()),
        SmtToken::Hexadecimal(hex.view()),
        SmtToken::Binary(bin.view()),
        SmtToken::String(string.view()),
        SmtToken::String(empty_string.view()),
        SmtToken::Keyword(keyword.view()),
        SmtToken::Symbol(symbol.view()),
        SmtToken::Symbol(quoted.view()),
        SmtToken::Reserved(let_word),
        SmtToken::Whitespace(whitespace.view()),
        SmtToken::Comment(comment.view()),
    ];
    for version in VERSIONS {
        // each token in a write of its own
        let items: Vec<Item> = tokens.iter().map(|token| Item::write([*token])).collect();
        let written = write_backend::write(version, Writing::TokenByToken, true, &items);
        assert_eq!(written.answers.len(), tokens.len());
        for (token, answer) in tokens.iter().zip(&written.answers) {
            assert!(
                matches!(answer, Answer::Failed(WriteFailure::Io(_))),
                "{token:?} in {version:?} should fail to be written, got {answer:?}"
            );
        }
    }
}

#[test]
fn the_end_of_the_input_writes_nothing() {
    for version in VERSIONS {
        let text = written(SmtToken::EndOfFile, version);
        assert_eq!(text.expect("the end of the input is written"), b"");
        // not even a failing writer is written to
        let written = write_backend::write(
            version,
            Writing::TokenByToken,
            true,
            &[Item::write([SmtToken::EndOfFile])],
        );
        assert_eq!(
            written.answers,
            [Answer::Ok],
            "the end of the input touches no writer"
        );
    }
}

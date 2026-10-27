//! Tests of the writer in its three styles: the line style, which writes
//! tokens on one line as far as comments allow; the compact style, which
//! writes the compact form, and the canonical form when handed no comments;
//! and the layout style, which writes tokens in the layout they are handed
//! over in. The writer is fed by the lexer, through a cursor and by `write`.
//!
//! They run against `write_backend`, so that the driver runs them against
//! the Lean port too. The token values handed to the writer, and the tokens
//! of the written text that the tests compare, are lexed by the Rust lexer.
//! The tests of the Rust interface itself call the writer directly and say
//! so.

mod write_backend;

use std::convert::Infallible;
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtVersion, SmtWriteStyle, SmtWriter, SmtWriterConfig,
    lexer::{SmtLexer, SmtLexerCursor},
    lexicon::{SmtCommentBuf, SmtGeneralReserved, SmtNumeralBuf, SmtReserved, SmtSymbol},
    token::{SmtConsume, SmtConsumeFrom, SmtCursor, SmtToken, SmtTokensBuf},
};
use write_backend::{Answer, Item, WriteFailure, Writing};

/// Inputs that every version from 2.5 on lexes alike, with every kind of
/// token, and whitespace and comments around and between them.
const INPUTS: [&[u8]; 12] = [
    b"",
    b"()",
    b" \t\r\n",
    b"(assert (= x #x1F #b01 12 0 1.5 0.0 10.050))",
    b"(set-info :smt-lib-version 2.6)\n(check-sat)\n",
    b"(! x :named |a name|) |q\ns| || |x| x |;| |\"|",
    b"(let ((_ x)) (forall ((x Int)) (exists ((y Int)) (as x Int))))",
    b"\"\" \"a\" \"a ; b\" \"line\nbreak\" \"|pipe|\" \"say \"\"hi\"\"\"",
    b"; comment\n(echo \"hi\") ; trailing\r\n",
    b";;; a ; b\n;\n;",
    b"  (assert\n\t(= x #x1F #b01 12 1.5 :kw |q\ns| \"s\nt\")) ; end\n\n; last",
    b"x;comment at the end without a line feed",
];

/// A consumer that keeps every token, or only the abstract ones, in an
/// owned token list, the end of the input included.
struct Keep {
    concrete: bool,
    tokens: SmtTokensBuf,
}

impl SmtConsume for Keep {
    type Result = SmtTokensBuf;
    type Error = Infallible;
    const IS_CONCRETE: bool = true;
}

impl<'a> SmtConsumeFrom<SmtLexerCursor<'a>> for Keep {
    fn consume(
        &mut self,
        cursor: &mut SmtLexerCursor<'a>,
    ) -> Result<ControlFlow<SmtTokensBuf>, Infallible> {
        while let Some(token) = cursor.next() {
            let token = cursor.syntax(&token);
            let layout = matches!(token, SmtToken::Whitespace(_) | SmtToken::Comment(_));
            if self.concrete || !layout {
                self.tokens.push(token);
            }
            if matches!(token, SmtToken::EndOfFile) {
                return Ok(ControlFlow::Break(std::mem::take(&mut self.tokens)));
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Lexes the input in the version into its tokens, concrete or abstract,
/// with the Rust lexer.
fn lexed(input: &[u8], version: SmtVersion, concrete: bool) -> SmtTokensBuf {
    let keep = Keep {
        concrete,
        tokens: SmtTokensBuf::new(),
    };
    SmtLexer::new(keep, version)
        .lex_all(input)
        .unwrap_or_else(|err| panic!("{:?} should lex: {err:?}", input.escape_ascii()))
        .into_value()
}

/// The tokens as debugged, for comparing token lists.
fn debugged(tokens: &SmtTokensBuf) -> Vec<String> {
    tokens.iter().map(|token| format!("{token:?}")).collect()
}

/// What a writer in the style writes for the tokens, handed over in one
/// write, in 2.7.
fn written_tokens<'t>(
    tokens: impl IntoIterator<Item = SmtToken<'t>>,
    style: SmtWriteStyle,
) -> String {
    let text = write_backend::written(
        SmtVersion::V2_7,
        Writing::Writer(style),
        &[Item::write(tokens)],
    );
    String::from_utf8(text).expect("the test text is UTF-8")
}

/// What a writer in the style writes for the value, in 2.7.
fn written(value: &SmtTokensBuf, style: SmtWriteStyle) -> String {
    written_tokens(value.iter(), style)
}

/// What the compact writer writes for the value, in 2.7.
fn compact(value: &SmtTokensBuf) -> String {
    written(value, SmtWriteStyle::Compact)
}

/// What the layout writer writes for the value, in 2.7.
fn layout(value: &SmtTokensBuf) -> String {
    written(value, SmtWriteStyle::Layout)
}

/// What a writer in the style writes for the inputs lexed one after another
/// into it, in the version.
fn written_lexed(inputs: &[&[u8]], version: SmtVersion, style: SmtWriteStyle) -> Vec<u8> {
    let items: Vec<Item> = inputs.iter().map(|input| Item::lex(input)).collect();
    write_backend::written(version, Writing::Writer(style), &items)
}

/// What the compact writer writes for the inputs lexed one after another
/// into it, in the version.
fn compact_lexed(inputs: &[&[u8]], version: SmtVersion) -> Vec<u8> {
    written_lexed(inputs, version, SmtWriteStyle::Compact)
}

/// What the layout writer writes for the inputs lexed one after another
/// into it, in the version.
fn layout_lexed(inputs: &[&[u8]], version: SmtVersion) -> Vec<u8> {
    written_lexed(inputs, version, SmtWriteStyle::Layout)
}

#[test]
fn the_compact_writer_writes_abstract_tokens_in_the_canonical_form() {
    let cases: [(&[u8], &str); 8] = [
        (b"", ""),
        (b"( )", "()\n"),
        (
            b"(set-logic QF_UF)\n  (assert   (= x  (f  y)))  x  42",
            "(set-logic QF_UF)\n(assert (= x (f y)))\nx\n42\n",
        ),
        (b"((a)(b) c)", "((a) (b) c)\n"),
        (b"(f (g) h)", "(f (g) h)\n"),
        (b"( ( ) )", "(())\n"),
        (b"(! x :named |a b|)\"s\"", "(! x :named |a b|)\n\"s\"\n"),
        // a closing parenthesis outside of parentheses ends an item too
        (b") x (y", ")\nx\n(y\n"),
    ];
    for (input, expected) in cases {
        let tokens = lexed(input, SmtVersion::V2_7, false);
        assert_eq!(compact(&tokens), expected, "{:?}", input.escape_ascii());
        // the same through the lexer, without comments
        let lexed_text = compact_lexed(&[input], SmtVersion::V2_7);
        assert_eq!(String::from_utf8_lossy(&lexed_text), expected);
    }
}

#[test]
fn the_compact_writer_writes_each_comment_on_a_line_of_its_own() {
    let cases: [(&[u8], &str); 6] = [
        (b"; head\n(check-sat)", "; head\n(check-sat)\n"),
        (
            b"(assert ; in\n x) ; tail\r\n",
            "(assert\n; in\nx)\n; tail\n",
        ),
        (b"(a;b\n)", "(a\n;b\n)\n"),
        (b"x;comment at the end", "x\n;comment at the end\n"),
        (b";\n;", ";\n;\n"),
        (b"(f x ;c\r y)", "(f x\n;c\ny)\n"),
    ];
    for (input, expected) in cases {
        let tokens = lexed(input, SmtVersion::V2_7, true);
        assert_eq!(compact(&tokens), expected, "{:?}", input.escape_ascii());
        let lexed_text = compact_lexed(&[input], SmtVersion::V2_7);
        assert_eq!(String::from_utf8_lossy(&lexed_text), expected);
    }
}

#[test]
fn the_compact_and_line_forms_read_back_as_the_tokens_and_are_written_alike_again() {
    for style in [SmtWriteStyle::Compact, SmtWriteStyle::Line] {
        for version in [SmtVersion::V2_5, SmtVersion::V2_6, SmtVersion::V2_7] {
            for input in INPUTS {
                let written = written_lexed(&[input], version, style);
                // the abstract tokens are kept
                assert_eq!(
                    debugged(&lexed(&written, version, false)),
                    debugged(&lexed(input, version, false)),
                    "{:?} in {version:?}, {style:?}",
                    input.escape_ascii()
                );
                // and the comments too, each with a line feed for an ending
                let comments = |tokens: &SmtTokensBuf| -> Vec<Vec<u8>> {
                    // a comment ends in a single carriage return or line feed
                    tokens
                        .iter()
                        .filter_map(|token| match token {
                            SmtToken::Comment(comment) => {
                                let content = comment.as_slice();
                                let content = content
                                    .strip_suffix(b"\n")
                                    .or_else(|| content.strip_suffix(b"\r"))
                                    .unwrap_or(content);
                                Some(content.to_vec())
                            }
                            _ => None,
                        })
                        .collect()
                };
                assert_eq!(
                    comments(&lexed(&written, version, true)),
                    comments(&lexed(input, version, true))
                );
                // the form is a fixed point
                assert_eq!(
                    written_lexed(&[&written], version, style),
                    written,
                    "{:?} in {version:?}, {style:?}",
                    input.escape_ascii()
                );
            }
        }
    }
}

#[test]
fn the_compact_writer_ends_the_line_and_starts_anew_at_the_end_of_an_input() {
    // the unfinished item of the first input is not continued by the second
    let written = compact_lexed(&[b"(a (b", b"(c) d", b"e"], SmtVersion::V2_7);
    assert_eq!(String::from_utf8_lossy(&written), "(a (b\n(c)\nd\ne\n");
    // an end of the input inside written tokens does the same
    let mut tokens = lexed(b"(a (b", SmtVersion::V2_7, false);
    for token in lexed(b"(c)", SmtVersion::V2_7, false).iter() {
        tokens.push(token);
    }
    assert_eq!(compact(&tokens), "(a (b\n(c)\n");
}

#[test]
fn the_line_writer_writes_abstract_tokens_on_one_line() {
    // the lexed tokens end with the end of the input, which writes nothing
    let cases: [(&[u8], &str); 8] = [
        (b"", ""),
        (b"( )", "()"),
        (
            b"(set-logic QF_UF)\n  (assert   (= x  (f  y)))  x  42",
            "(set-logic QF_UF) (assert (= x (f y))) x 42",
        ),
        (b"((a)(b) c)", "((a) (b) c)"),
        (b"(f (g) h)", "(f (g) h)"),
        (b"( ( ) )", "(())"),
        (b"(! x :named |a b|)\"s\"", "(! x :named |a b|) \"s\""),
        (b") x (y", ") x (y"),
    ];
    for (input, expected) in cases {
        let tokens = lexed(input, SmtVersion::V2_7, false);
        assert_eq!(
            written(&tokens, SmtWriteStyle::Line),
            expected,
            "{:?}",
            input.escape_ascii()
        );
        let lexed_text = written_lexed(&[input], SmtVersion::V2_7, SmtWriteStyle::Line);
        assert_eq!(String::from_utf8_lossy(&lexed_text), expected);
    }
}

#[test]
fn the_line_writer_ends_a_comment_with_a_line_feed_only_before_a_token() {
    let cases: [(&[u8], &str); 6] = [
        (b"; head\n(check-sat)", "; head\n(check-sat)"),
        (b"(assert ; in\n x) ; tail\r\n", "(assert ; in\nx) ; tail"),
        (b"(a;b\n)", "(a ;b\n)"),
        (b"x;comment at the end", "x ;comment at the end"),
        (b";\n;", ";\n;"),
        (b"(f x ;c\r y)", "(f x ;c\ny)"),
    ];
    for (input, expected) in cases {
        let tokens = lexed(input, SmtVersion::V2_7, true);
        assert_eq!(
            written(&tokens, SmtWriteStyle::Line),
            expected,
            "{:?}",
            input.escape_ascii()
        );
        let lexed_text = written_lexed(&[input], SmtVersion::V2_7, SmtWriteStyle::Line);
        assert_eq!(String::from_utf8_lossy(&lexed_text), expected);
    }
    // nor is it ended without an end of the input
    let x = SmtSymbol::new_unquoted(b"x").expect("a symbol");
    let comment = SmtCommentBuf::new(b" c".to_vec()).expect("a comment");
    let tokens = [SmtToken::Symbol(x), SmtToken::Comment(comment.view())];
    assert_eq!(written_tokens(tokens, SmtWriteStyle::Line), "x ; c");
}

#[test]
fn the_line_writer_starts_each_input_on_a_line_of_its_own() {
    // the line is ended when the next input begins, not at the end of one
    let cases: [(&[&[u8]], &str); 4] = [
        (&[b"(a (b", b"(c) d", b"e"], "(a (b\n(c) d\ne"),
        // an empty input writes nothing, not even a line
        (&[b"", b"x", b"", b"", b"y", b""], "x\ny"),
        // a comment at the end of an input is ended once
        (&[b"x ;c", b"y ;d\n"], "x ;c\ny ;d"),
        (&[b";c", b";d"], ";c\n;d"),
    ];
    for (inputs, expected) in cases {
        let written = written_lexed(inputs, SmtVersion::V2_7, SmtWriteStyle::Line);
        assert_eq!(String::from_utf8_lossy(&written), expected, "{inputs:?}");
    }
}

#[test]
fn the_layout_writer_writes_lexed_text_back_byte_for_byte() {
    for version in [SmtVersion::V2_5, SmtVersion::V2_6, SmtVersion::V2_7] {
        for input in INPUTS {
            assert_eq!(
                layout_lexed(&[input], version),
                input,
                "{:?} in {version:?}",
                input.escape_ascii()
            );
        }
    }
    // 2.0 strings are written back with their escapes
    let input: &[u8] = b"(echo \"say \\\"hi\\\"\") ; done";
    assert_eq!(layout_lexed(&[input], SmtVersion::V2_0), input);
    // but a backslash 2.0 does not escape is written escaped, and the
    // string reads back alike
    let input: &[u8] = b"(echo \"a\\q\")";
    let written = layout_lexed(&[input], SmtVersion::V2_0);
    assert_eq!(written, b"(echo \"a\\\\q\")");
    assert_eq!(
        debugged(&lexed(&written, SmtVersion::V2_0, true)),
        debugged(&lexed(input, SmtVersion::V2_0, true))
    );
}

#[test]
fn the_layout_writer_writes_only_the_spaces_that_keep_tokens_apart() {
    let cases: [(&[u8], &str); 5] = [
        (b"(assert (= x (f y)))", "(assert(= x(f y)))"),
        (b"( a  b )", "(a b)"),
        (
            b"x 1 \"s\" |q| :k #x1 #b0 1.5",
            "x 1 \"s\" |q| :k #x1 #b0 1.5",
        ),
        (b"(a) (b)", "(a)(b)"),
        (b"", ""),
    ];
    for (input, expected) in cases {
        let tokens = lexed(input, SmtVersion::V2_7, false);
        assert_eq!(layout(&tokens), expected, "{:?}", input.escape_ascii());
    }
}

#[test]
fn the_layout_writer_ends_a_comment_without_a_line_ending_before_a_token() {
    let open = SmtCommentBuf::new(b" open".to_vec()).expect("a comment");
    let ended = SmtCommentBuf::new(b" ended\n".to_vec()).expect("a comment");
    let x = SmtSymbol::new_unquoted(b"x").expect("a symbol");
    let mut tokens = SmtTokensBuf::new();
    for token in [
        SmtToken::Comment(open.view()),
        SmtToken::Symbol(x),
        SmtToken::Comment(ended.view()),
        SmtToken::Symbol(x),
        SmtToken::Comment(open.view()),
        SmtToken::ParenOpen,
    ] {
        tokens.push(token);
    }
    assert_eq!(layout(&tokens), "; open\nx; ended\nx; open\n(");
    // a comment at the end of the input keeps its missing ending, and the
    // next input starts on a new line
    let written = layout_lexed(&[b"x;c", b"y", b"z"], SmtVersion::V2_7);
    assert_eq!(String::from_utf8_lossy(&written), "x;c\ny\nz");
}

#[test]
fn the_layout_writer_starts_each_input_on_a_line_of_its_own() {
    let cases: [(&[&[u8]], &str); 6] = [
        (&[b"x", b"y"], "x\ny"),
        (&[b"(a) ", b"(b)"], "(a) \n(b)"),
        // no line feed is added after one that is there
        (&[b"x\n", b"y"], "x\ny"),
        (&[b"x;c\n", b"y"], "x;c\ny"),
        // a comment ended by a carriage return is not on a line of its own
        (&[b"x;c\r", b"y"], "x;c\r\ny"),
        // an empty input adds nothing, and nothing is added before the first
        (&[b"", b"x", b"", b"y", b""], "x\ny"),
    ];
    for (inputs, expected) in cases {
        let written = layout_lexed(inputs, SmtVersion::V2_7);
        assert_eq!(String::from_utf8_lossy(&written), expected, "{inputs:?}");
    }
    // an end of the input inside written tokens does the same
    let mut tokens = lexed(b"(a)", SmtVersion::V2_7, true);
    for token in lexed(b"(b)", SmtVersion::V2_7, true).iter() {
        tokens.push(token);
    }
    assert_eq!(layout(&tokens), "(a)\n(b)");
}

#[test]
fn both_writers_quote_a_symbol_that_spells_a_word_reserved_in_their_version() {
    // `lambda` is a simple symbol in 2.6 and a reserved word from 2.7 on
    let tokens = lexed(b"(lambda x)", SmtVersion::V2_6, false);
    assert_eq!(compact(&tokens), "(|lambda| x)\n");
    assert_eq!(layout(&tokens), "(|lambda| x)");
    // in their own version, the same tokens are written as they are
    for (style, expected) in [
        (SmtWriteStyle::Compact, &b"(lambda x)\n"[..]),
        (SmtWriteStyle::Layout, b"(lambda x)"),
    ] {
        let text = write_backend::written(
            SmtVersion::V2_7,
            Writing::Writer(style),
            &[Item::version(SmtVersion::V2_6), Item::write(tokens.iter())],
        );
        assert_eq!(text, expected, "{style:?}");
    }
}

/// Tests the Rust interface itself: the getters of the writer. Calls the
/// writer directly.
#[test]
fn a_writer_shows_its_version_and_what_it_wrote_into() {
    let tokens = lexed(b"(lambda x)", SmtVersion::V2_6, false);
    let mut writer = SmtWriter::new(
        Vec::new(),
        SmtWriterConfig::new(SmtVersion::V2_7).with_style(SmtWriteStyle::Compact),
    );
    writer.set_version(SmtVersion::V2_6);
    assert_eq!(writer.version(), SmtVersion::V2_6);
    writer
        .write(&tokens)
        .expect("writing into a vector succeeds");
    assert_eq!(writer.get_ref().as_slice(), b"(lambda x)\n");
    let mut writer = SmtWriter::new(
        Vec::new(),
        SmtWriterConfig::new(SmtVersion::V2_7).with_style(SmtWriteStyle::Layout),
    );
    writer.set_version(SmtVersion::V2_6);
    assert_eq!(writer.version(), SmtVersion::V2_6);
    writer
        .write(&tokens)
        .expect("writing into a vector succeeds");
    assert_eq!(writer.get_mut().as_slice(), b"(lambda x)");
}

#[test]
fn both_writers_fail_on_a_reserved_word_their_version_does_not_have() {
    // the failing write stops at the reserved word: the symbol after it is
    // not written
    let lambda = SmtReserved::General(SmtGeneralReserved::Lambda);
    let x = SmtSymbol::new_unquoted(b"x").expect("a symbol");
    let tokens = [SmtToken::Reserved(lambda), SmtToken::Symbol(x)];
    for style in [SmtWriteStyle::Compact, SmtWriteStyle::Layout] {
        let written = write_backend::write(
            SmtVersion::V2_6,
            Writing::Writer(style),
            false,
            &[Item::write(tokens)],
        );
        // 2.6 has no `lambda`
        assert_eq!(
            written.answers,
            [Answer::Failed(WriteFailure::NotInVersion(lambda))],
            "{style:?}"
        );
        assert!(written.out.is_empty(), "{style:?}");
    }
}

#[test]
fn a_failure_of_the_underlying_writer_is_an_io_error_of_both_writers() {
    let numeral = SmtNumeralBuf::new(b"12".to_vec()).expect("a numeral");
    let numeral = SmtToken::Numeral(numeral.view());
    for style in [SmtWriteStyle::Compact, SmtWriteStyle::Layout] {
        let written = write_backend::write(
            SmtVersion::V2_7,
            Writing::Writer(style),
            true,
            &[Item::write([numeral])],
        );
        assert!(
            matches!(&written.answers[..], [Answer::Failed(WriteFailure::Io(_))]),
            "the writer fails, got {:?}",
            written.answers
        );
    }
    // a writer that failed in one write writes the next value
    let lambda = SmtReserved::General(SmtGeneralReserved::Lambda);
    // a failing write stops at the failing token
    let failing = [SmtToken::Reserved(lambda), numeral];
    let written = write_backend::write(
        SmtVersion::V2_7,
        Writing::Writer(SmtWriteStyle::Compact),
        false,
        &[
            Item::version(SmtVersion::V2_6),
            Item::write(failing),
            Item::write([numeral]),
        ],
    );
    // 2.6 has no `lambda`, and the failing write writes nothing
    assert_eq!(
        written.answers,
        [
            Answer::Ok,
            Answer::Failed(WriteFailure::NotInVersion(lambda)),
            Answer::Ok
        ]
    );
    assert_eq!(written.out, b"12\n");
}

#[test]
fn the_writers_write_each_value_handed_to_write_in_turn() {
    let numeral = SmtNumeralBuf::new(b"12".to_vec()).expect("a numeral");
    let numeral = SmtToken::Numeral(numeral.view());
    let x = SmtToken::Symbol(SmtSymbol::new_unquoted(b"x").expect("a symbol"));
    let lexed_value = lexed(b"(f\n x)", SmtVersion::V2_7, true);
    let values = [
        Item::write([numeral]),
        Item::write([x, x]),
        Item::write(lexed_value.iter()),
    ];
    for (style, expected) in [
        (SmtWriteStyle::Compact, &b"12\nx\nx\n(f x)\n"[..]),
        (SmtWriteStyle::Layout, b"12 x x(f\n x)"),
        (SmtWriteStyle::Line, b"12 x x (f x)"),
    ] {
        let text = write_backend::written(SmtVersion::V2_7, Writing::Writer(style), &values);
        assert_eq!(text, expected, "{style:?}");
    }
    // a single value is written without a line feed
    let text = write_backend::written(
        SmtVersion::V2_7,
        Writing::Writer(SmtWriteStyle::Line),
        &values[..1],
    );
    assert_eq!(text, b"12");
}

#[test]
fn the_writers_consume_a_tokens_cursor_and_break_at_its_end_of_the_input() {
    let tokens = lexed(b"(a b) c", SmtVersion::V2_7, false);
    let written = write_backend::write(
        SmtVersion::V2_7,
        Writing::Writer(SmtWriteStyle::Compact),
        false,
        &[Item::consume(tokens.iter())],
    );
    // the writer takes every token
    assert_eq!(written.answers, [Answer::Break(0)]);
    assert_eq!(written.out, b"(a b)\nc\n");
    // without an end of the input, the writer continues
    let written = write_backend::write(
        SmtVersion::V2_7,
        Writing::Writer(SmtWriteStyle::Layout),
        false,
        &[Item::consume([SmtToken::ParenOpen])],
    );
    assert_eq!(written.answers, [Answer::Continue(0)]);
    assert_eq!(written.out, b"(");
}

/// Tests the Rust interface itself: the configuration and its getters.
/// Calls the writer directly.
#[test]
fn a_writer_keeps_its_configuration_and_writes_in_the_layout_style_by_default() {
    let config = SmtWriterConfig::new(SmtVersion::V2_6);
    assert_eq!(config.version(), SmtVersion::V2_6);
    assert_eq!(config.style(), SmtWriteStyle::Layout);
    let compact = config.with_style(SmtWriteStyle::Compact);
    let line = config.with_style(SmtWriteStyle::Line);
    assert_eq!(line.style(), SmtWriteStyle::Line);
    assert_eq!(compact.version(), SmtVersion::V2_6);
    assert_eq!(compact.style(), SmtWriteStyle::Compact);
    for config in [config, compact, line] {
        let mut writer = SmtWriter::new(Vec::new(), config);
        assert_eq!(writer.config(), config);
        // a changed version is a part of the configuration
        writer.set_version(SmtVersion::V2_7);
        assert_eq!(
            writer.config(),
            SmtWriterConfig::new(SmtVersion::V2_7).with_style(config.style())
        );
    }
}

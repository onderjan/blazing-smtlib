//! Public-API tests of the token writers: the compact writer, which writes
//! the compact form, and the canonical form when handed no comments; and
//! the layout writer, which writes tokens in the layout they are handed over
//! in. The writers are fed by the lexer, through a cursor and by `write`.
//!
//! They check the Rust interface itself and call the library directly.

use std::convert::Infallible;
use std::io::{self, Write};
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtCommentBuf, SmtNumeralBuf, SmtSymbol,
    lexer::SmtLexer,
    token::{
        SmtAppendTokens, SmtBatchCursor, SmtCompactTokenWriter, SmtConsume, SmtConsumeFrom,
        SmtCursor, SmtGeneralReserved, SmtLayoutTokenWriter, SmtReserved, SmtSyntaxToken,
        SmtTokensBuf, SmtTokensCursor, SmtWriteErrorCause,
    },
    version::SmtVersion,
};

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

impl<'a> SmtConsumeFrom<SmtBatchCursor<'a>> for Keep {
    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'a>,
    ) -> Result<ControlFlow<SmtTokensBuf>, Infallible> {
        while let Some(token) = cursor.next() {
            let token = cursor.syntax(&token);
            let layout = matches!(
                token,
                SmtSyntaxToken::Whitespace(_) | SmtSyntaxToken::Comment(_)
            );
            if self.concrete || !layout {
                self.tokens.push(token);
            }
            if matches!(token, SmtSyntaxToken::EndOfFile) {
                return Ok(ControlFlow::Break(std::mem::take(&mut self.tokens)));
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Lexes the input in the version into its tokens, concrete or abstract.
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

/// What the compact writer writes for the value, in 2.7.
fn compact(value: &SmtTokensBuf) -> String {
    let mut writer = SmtCompactTokenWriter::new(Vec::new(), SmtVersion::V2_7);
    writer.write(value).expect("writing into a vector succeeds");
    String::from_utf8(writer.into_inner()).expect("the test text is UTF-8")
}

/// What the layout writer writes for the value, in 2.7.
fn layout(value: &SmtTokensBuf) -> String {
    let mut writer = SmtLayoutTokenWriter::new(Vec::new(), SmtVersion::V2_7);
    writer.write(value).expect("writing into a vector succeeds");
    String::from_utf8(writer.into_inner()).expect("the test text is UTF-8")
}

/// What the compact writer writes for the inputs lexed one after another
/// into it, in the version.
fn compact_lexed(inputs: &[&[u8]], version: SmtVersion) -> Vec<u8> {
    let mut writer = SmtCompactTokenWriter::new(Vec::new(), version);
    let mut lexer = SmtLexer::new(&mut writer, version);
    for input in inputs {
        lexer.lex_all(input).expect("the test input should lex");
    }
    drop(lexer);
    writer.into_inner()
}

/// What the layout writer writes for the inputs lexed one after another
/// into it, in the version.
fn layout_lexed(inputs: &[&[u8]], version: SmtVersion) -> Vec<u8> {
    let mut writer = SmtLayoutTokenWriter::new(Vec::new(), version);
    let mut lexer = SmtLexer::new(&mut writer, version);
    for input in inputs {
        lexer.lex_all(input).expect("the test input should lex");
    }
    drop(lexer);
    writer.into_inner()
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
fn the_compact_form_reads_back_as_the_tokens_and_is_written_alike_again() {
    for version in [SmtVersion::V2_5, SmtVersion::V2_6, SmtVersion::V2_7] {
        for input in INPUTS {
            let written = compact_lexed(&[input], version);
            // the abstract tokens are kept
            assert_eq!(
                debugged(&lexed(&written, version, false)),
                debugged(&lexed(input, version, false)),
                "{:?} in {version:?}",
                input.escape_ascii()
            );
            // and the comments too, each with a line feed for an ending
            let comments = |tokens: &SmtTokensBuf| -> Vec<Vec<u8>> {
                // a comment ends in a single carriage return or line feed
                tokens
                    .iter()
                    .filter_map(|token| match token {
                        SmtSyntaxToken::Comment(comment) => {
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
            // the compact form is a fixed point
            assert_eq!(
                compact_lexed(&[&written], version),
                written,
                "{:?} in {version:?}",
                input.escape_ascii()
            );
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
        SmtSyntaxToken::Comment(open.view()),
        SmtSyntaxToken::Symbol(x),
        SmtSyntaxToken::Comment(ended.view()),
        SmtSyntaxToken::Symbol(x),
        SmtSyntaxToken::Comment(open.view()),
        SmtSyntaxToken::ParenOpen,
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
    let mut writer = SmtCompactTokenWriter::new(Vec::new(), SmtVersion::V2_7);
    writer.set_version(SmtVersion::V2_6);
    assert_eq!(writer.version(), SmtVersion::V2_6);
    writer
        .write(&tokens)
        .expect("writing into a vector succeeds");
    assert_eq!(writer.get_ref().as_slice(), b"(lambda x)\n");
    let mut writer = SmtLayoutTokenWriter::new(Vec::new(), SmtVersion::V2_7);
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
    let tokens = [SmtSyntaxToken::Reserved(lambda), SmtSyntaxToken::Symbol(x)];
    let mut compact_writer = SmtCompactTokenWriter::new(Vec::new(), SmtVersion::V2_6);
    let err = compact_writer
        .write(tokens.as_slice())
        .expect_err("2.6 has no `lambda`");
    assert!(matches!(err.cause(), SmtWriteErrorCause::NotInVersion(word) if *word == lambda));
    assert!(compact_writer.get_ref().is_empty());
    let mut layout_writer = SmtLayoutTokenWriter::new(Vec::new(), SmtVersion::V2_6);
    let err = layout_writer
        .write(tokens.as_slice())
        .expect_err("2.6 has no `lambda`");
    assert!(matches!(err.cause(), SmtWriteErrorCause::NotInVersion(word) if *word == lambda));
    assert!(layout_writer.get_ref().is_empty());
}

struct FailingWriter;

impl Write for FailingWriter {
    fn write(&mut self, _buf: &[u8]) -> io::Result<usize> {
        Err(io::Error::other("the test writer fails every write"))
    }

    fn flush(&mut self) -> io::Result<()> {
        Err(io::Error::other("the test writer fails every flush"))
    }
}

#[test]
fn a_failure_of_the_underlying_writer_is_an_io_error_of_both_writers() {
    let numeral = SmtNumeralBuf::new(b"12".to_vec()).expect("a numeral");
    let err = SmtCompactTokenWriter::new(FailingWriter, SmtVersion::V2_7)
        .write(&numeral)
        .expect_err("the writer fails");
    assert!(matches!(err.cause(), SmtWriteErrorCause::Io(_)));
    let err = SmtLayoutTokenWriter::new(FailingWriter, SmtVersion::V2_7)
        .write(&numeral)
        .expect_err("the writer fails");
    assert!(matches!(err.cause(), SmtWriteErrorCause::Io(_)));
    // a writer that failed in one write writes the next value
    let mut writer = SmtCompactTokenWriter::new(Vec::new(), SmtVersion::V2_7);
    let lambda = SmtReserved::General(SmtGeneralReserved::Lambda);
    writer.set_version(SmtVersion::V2_6);
    // a failing write stops at the failing token
    let failing = [
        SmtSyntaxToken::Reserved(lambda),
        SmtSyntaxToken::Numeral(numeral.view()),
    ];
    writer
        .write(failing.as_slice())
        .expect_err("2.6 has no `lambda`");
    assert!(writer.get_ref().is_empty());
    writer
        .write(&numeral)
        .expect("writing into a vector succeeds");
    assert_eq!(writer.into_inner(), b"12\n");
}

#[test]
fn the_writers_write_each_value_handed_to_write_in_turn() {
    let numeral = SmtNumeralBuf::new(b"12".to_vec()).expect("a numeral");
    let x = SmtSymbol::new_unquoted(b"x").expect("a symbol");
    let mut writer = SmtCompactTokenWriter::new(Vec::new(), SmtVersion::V2_7);
    writer
        .write(&numeral)
        .expect("writing into a vector succeeds");
    writer
        .write([x, x].as_slice())
        .expect("writing into a vector succeeds");
    writer
        .write(&lexed(b"(f\n x)", SmtVersion::V2_7, true))
        .expect("writing into a vector succeeds");
    assert_eq!(writer.into_inner(), b"12\nx\nx\n(f x)\n");
    let mut writer = SmtLayoutTokenWriter::new(Vec::new(), SmtVersion::V2_7);
    writer
        .write(&numeral)
        .expect("writing into a vector succeeds");
    writer
        .write([x, x].as_slice())
        .expect("writing into a vector succeeds");
    writer
        .write(&lexed(b"(f\n x)", SmtVersion::V2_7, true))
        .expect("writing into a vector succeeds");
    assert_eq!(writer.into_inner(), b"12 x x(f\n x)");
}

#[test]
fn the_writers_consume_a_tokens_cursor_and_break_at_its_end_of_the_input() {
    let tokens = lexed(b"(a b) c", SmtVersion::V2_7, false);
    let mut cursor = SmtTokensCursor::new(SmtVersion::V2_7);
    tokens.append_tokens(&mut cursor);
    let mut writer = SmtCompactTokenWriter::new(Vec::new(), SmtVersion::V2_7);
    let flow = writer
        .consume(&mut cursor)
        .expect("writing into a vector succeeds");
    assert!(matches!(flow, ControlFlow::Break(())));
    assert!(cursor.is_empty());
    assert_eq!(writer.into_inner(), b"(a b)\nc\n");
    // without an end of the input, the writer continues
    let mut cursor = SmtTokensCursor::new(SmtVersion::V2_7);
    cursor.push(SmtSyntaxToken::ParenOpen);
    let mut writer = SmtLayoutTokenWriter::new(Vec::new(), SmtVersion::V2_7);
    let flow = writer
        .consume(&mut cursor)
        .expect("writing into a vector succeeds");
    assert!(matches!(flow, ControlFlow::Continue(())));
    assert_eq!(writer.into_inner(), b"(");
}

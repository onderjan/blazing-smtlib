//! The writer requests of the driver protocol, answered by the Rust library.
//!
//! The protocol is described in `lean/driver-protocol.md`, section "The
//! writer". This module is the reference answer to it: the tests call it in
//! process, and the executable in `tools/rust-lex-driver` prints what it
//! returns.

use std::io::{self, Write};
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtVersion, SmtWriteError, SmtWriteErrorKind, SmtWriteStyle, SmtWriter, SmtWriterConfig,
    lexer::{SmtLexer, SmtLexerCursor, SmtLexerErrorKind},
    lexicon::{
        SmtBinDigitsBuf, SmtCommentBuf, SmtDecimal, SmtDecimalBuf, SmtHexDigitsBuf, SmtKeywordBuf,
        SmtNumeralBuf, SmtStringContentBuf, SmtSymbolBuf, SmtWhitespaceBuf,
    },
    span::SmtLocation,
    token::{
        SmtAppendTokens, SmtConsume, SmtConsumeFrom, SmtCursor, SmtReserved, SmtToken,
        SmtTokensBuf, SmtTokensCursor,
    },
};

/// The message of the failure of the writer under a request with `fail`.
pub const WRITER_FAILURE: &str = "the test writer fails every write";

/// What the bytes are written into: kept, or refused by every write.
struct Sink {
    bytes: Vec<u8>,
    fails: bool,
}

impl Write for Sink {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if self.fails {
            return Err(io::Error::other(WRITER_FAILURE));
        }
        self.bytes.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        if self.fails {
            return Err(io::Error::other(WRITER_FAILURE));
        }
        Ok(())
    }
}

/// What a request hands to the writer, by its items.
enum Item {
    /// The bytes, lexed as one whole input into the writer.
    Lex(Vec<u8>),
    /// One write of the tokens.
    Write(SmtTokensBuf),
    /// One consumption of a tokens cursor that holds the tokens.
    Consume(SmtTokensBuf),
    /// The version to write the following tokens in.
    Version(SmtVersion),
}

/// A request, read from its line.
struct Request {
    version: SmtVersion,
    /// The style of the writer, or `None` for each token written by itself.
    style: Option<SmtWriteStyle>,
    fails: bool,
    items: Vec<Item>,
}

fn location(location: SmtLocation) -> String {
    format!(
        "{}:{}:{}",
        location.offset(),
        location.line(),
        location.column()
    )
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn unhex(digits: &str) -> Result<Vec<u8>, String> {
    if !digits.len().is_multiple_of(2) {
        return Err(format!("odd number of hexadecimal digits in {digits:?}"));
    }
    (0..digits.len())
        .step_by(2)
        .map(|at| {
            digits
                .get(at..at + 2)
                .and_then(|pair| u8::from_str_radix(pair, 16).ok())
                .ok_or_else(|| format!("bad hexadecimal digits in {digits:?}"))
        })
        .collect()
}

fn read_version(word: &str) -> Result<SmtVersion, String> {
    SmtDecimal::new(word.as_bytes())
        .ok()
        .and_then(SmtVersion::from_decimal)
        .ok_or_else(|| format!("unknown version {word:?}"))
}

/// The reserved word of the spelling, in whichever version reserves it.
fn read_reserved(spelling: &str) -> Result<SmtReserved, String> {
    [
        SmtVersion::V2_7,
        SmtVersion::V2_6,
        SmtVersion::V2_5,
        SmtVersion::V2_0,
    ]
    .into_iter()
    .find_map(|version| SmtReserved::from_bytes(spelling.as_bytes(), version))
    .ok_or_else(|| format!("unknown reserved word {spelling:?}"))
}

/// Reads the token of the word and pushes it onto the tokens.
fn push_token(tokens: &mut SmtTokensBuf, word: &str) -> Result<(), String> {
    let bad = |_| format!("bad token {word:?}");
    match word {
        "(" => tokens.push(SmtToken::ParenOpen),
        ")" => tokens.push(SmtToken::ParenClose),
        "e" => tokens.push(SmtToken::EndOfFile),
        _ => {
            let (letter, rest) = word
                .split_at_checked(1)
                .ok_or_else(|| format!("bad token {word:?}"))?;
            if letter == "r" {
                tokens.push(SmtToken::Reserved(read_reserved(rest)?));
                return Ok(());
            }
            let bytes = unhex(rest)?;
            match letter {
                "N" => tokens.push(SmtToken::Numeral(
                    SmtNumeralBuf::new(bytes).map_err(bad)?.view(),
                )),
                "D" => tokens.push(SmtToken::Decimal(
                    SmtDecimalBuf::new(bytes).map_err(bad)?.view(),
                )),
                "X" => tokens.push(SmtToken::Hexadecimal(
                    SmtHexDigitsBuf::new(bytes).map_err(bad)?.view(),
                )),
                "B" => tokens.push(SmtToken::Binary(
                    SmtBinDigitsBuf::new(bytes).map_err(bad)?.view(),
                )),
                "S" => tokens.push(SmtToken::String(
                    SmtStringContentBuf::new(bytes).map_err(bad)?.view(),
                )),
                "k" => tokens.push(SmtToken::Keyword(
                    SmtKeywordBuf::new(bytes).map_err(bad)?.view(),
                )),
                "u" => tokens.push(SmtToken::Symbol(
                    SmtSymbolBuf::new_unquoted(bytes).map_err(bad)?.view(),
                )),
                "q" => tokens.push(SmtToken::Symbol(
                    SmtSymbolBuf::new_quoted(bytes).map_err(bad)?.view(),
                )),
                "w" => tokens.push(SmtToken::Whitespace(
                    SmtWhitespaceBuf::new(bytes).map_err(bad)?.view(),
                )),
                "c" => tokens.push(SmtToken::Comment(
                    SmtCommentBuf::new(bytes).map_err(bad)?.view(),
                )),
                _ => return Err(format!("bad token {word:?}")),
            }
        }
    }
    Ok(())
}

/// The tokens of the operand of an item, separated by commas.
fn read_tokens(operand: &str) -> Result<SmtTokensBuf, String> {
    let mut tokens = SmtTokensBuf::new();
    for word in operand.split(',').filter(|_| !operand.is_empty()) {
        push_token(&mut tokens, word)?;
    }
    Ok(tokens)
}

fn read_item(word: &str) -> Result<Item, String> {
    let (name, operand) = word
        .split_once(':')
        .ok_or_else(|| format!("unknown item {word:?}"))?;
    match name {
        "lex" => Ok(Item::Lex(unhex(operand)?)),
        "write" => Ok(Item::Write(read_tokens(operand)?)),
        "consume" => Ok(Item::Consume(read_tokens(operand)?)),
        "version" => Ok(Item::Version(read_version(operand)?)),
        _ => Err(format!("unknown item {word:?}")),
    }
}

fn read_request(line: &str) -> Result<Request, String> {
    let mut words = line.split(' ');
    if words.next() != Some("write") {
        return Err("unknown request".into());
    }
    let version = read_version(words.next().ok_or("no version")?)?;
    let style = match words.next().ok_or("no style")? {
        "-" => None,
        "line" => Some(SmtWriteStyle::Line),
        "compact" => Some(SmtWriteStyle::Compact),
        "layout" => Some(SmtWriteStyle::Layout),
        other => return Err(format!("unknown style {other:?}")),
    };
    let mut request = Request {
        version,
        style,
        fails: false,
        items: Vec::new(),
    };
    for word in words {
        if word == "fail" && request.items.is_empty() && !request.fails {
            request.fails = true;
            continue;
        }
        let item = read_item(word)?;
        if request.style.is_none() && matches!(item, Item::Consume(_)) {
            return Err("consume needs a writer of a style".into());
        }
        if matches!(&item, Item::Consume(tokens) if tokens.is_empty()) {
            return Err("consume needs a token".into());
        }
        request.items.push(item);
    }
    Ok(request)
}

/// The line of an error of writing.
fn write_error_line(err: &SmtWriteError) -> String {
    match err.kind() {
        SmtWriteErrorKind::Io(io) => format!("werr io x{}", hex(io.to_string().as_bytes())),
        SmtWriteErrorKind::NotInVersion(reserved) => {
            format!("werr not-in-version {}", reserved.as_str())
        }
    }
}

/// Lexes the bytes as one whole input with the consumer, answering the item.
fn lex_into<C>(consumer: C, version: SmtVersion, bytes: &[u8]) -> String
where
    C: for<'a> SmtConsumeFrom<SmtLexerCursor<'a>, Error = SmtWriteError>,
{
    let err = match SmtLexer::new(consumer, version).lex_all(bytes) {
        Ok(_) => return "ok".into(),
        Err(err) => err,
    };
    match err.kind() {
        SmtLexerErrorKind::Lexical(kind) => format!(
            "err {kind:?} {} {}",
            location(err.span().start()),
            location(err.span().end())
        ),
        SmtLexerErrorKind::Consumer(err) => write_error_line(err),
    }
}

/// A consumer that takes every token, whitespace and comments included,
/// and writes each by itself in the version of the cursor.
struct WriteBack<'s> {
    sink: &'s mut Sink,
}

impl SmtConsume for WriteBack<'_> {
    type Result = ();
    type Error = SmtWriteError;
    const IS_CONCRETE: bool = true;
}

impl<'a> SmtConsumeFrom<SmtLexerCursor<'a>> for WriteBack<'_> {
    fn consume(
        &mut self,
        cursor: &mut SmtLexerCursor<'a>,
    ) -> Result<ControlFlow<()>, SmtWriteError> {
        while let Some(token) = cursor.next() {
            let token = cursor.syntax(&token);
            token.write_smt(self.sink, cursor.version())?;
            if matches!(token, SmtToken::EndOfFile) {
                return Ok(ControlFlow::Break(()));
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Answers the items with each token written by itself, writing the lines.
fn answer_alone(request: &Request, sink: &mut Sink, out: &mut String) {
    let mut version = request.version;
    for item in &request.items {
        let line = match item {
            Item::Lex(bytes) => lex_into(WriteBack { sink: &mut *sink }, version, bytes),
            Item::Write(tokens) => tokens
                .iter()
                .try_for_each(|token| token.write_smt(&mut *sink, version))
                .map_or_else(|err| write_error_line(&err), |()| "ok".into()),
            Item::Consume(_) => panic!("a request is read with a writer for every consume"),
            Item::Version(next) => {
                version = *next;
                "ok".into()
            }
        };
        out.push_str(&line);
        out.push('\n');
    }
}

/// Answers the items with a writer of the style, writing the lines.
fn answer_styled(request: &Request, style: SmtWriteStyle, sink: Sink, out: &mut String) -> Sink {
    let config = SmtWriterConfig::new(request.version).with_style(style);
    let mut writer = SmtWriter::new(sink, config);
    for item in &request.items {
        let line = match item {
            Item::Lex(bytes) => {
                let version = writer.version();
                lex_into(&mut writer, version, bytes)
            }
            Item::Write(tokens) => writer
                .write(tokens)
                .map_or_else(|err| write_error_line(&err), |()| "ok".into()),
            Item::Consume(tokens) => {
                let mut cursor = SmtTokensCursor::new(writer.version());
                tokens.append_tokens(&mut cursor);
                let answer = writer.consume(&mut cursor);
                let mut left = 0;
                while cursor.next().is_some() {
                    left += 1;
                }
                match answer {
                    Ok(ControlFlow::Break(())) => format!("break {left}"),
                    Ok(ControlFlow::Continue(())) => format!("continue {left}"),
                    Err(err) => write_error_line(&err),
                }
            }
            Item::Version(version) => {
                writer.set_version(*version);
                "ok".into()
            }
        };
        out.push_str(&line);
        out.push('\n');
    }
    writer.into_inner()
}

/// Answers one request line with the lines of its response.
pub fn answer(line: &str) -> Result<String, String> {
    // decode the whole request first, so that a malformed one produces no lines
    let request = read_request(line)?;
    let mut sink = Sink {
        bytes: Vec::new(),
        fails: request.fails,
    };
    let mut out = String::new();
    match request.style {
        None => answer_alone(&request, &mut sink, &mut out),
        Some(style) => sink = answer_styled(&request, style, sink, &mut out),
    }
    out.push_str(&format!("out x{}\n", hex(&sink.bytes)));
    Ok(out)
}

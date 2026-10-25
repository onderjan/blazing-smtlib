//! The writer that the black-box writer tests run against.
//!
//! A request names the version and the style to write in, and what is
//! handed to the writer: inputs lexed into it, values written with `write`,
//! cursors it consumes, and changes of the version. Without a style, each
//! token is written by itself, as `SmtToken::write_smt` writes it.
//!
//! By default the request is answered by the Rust library, through the
//! reference answer of `driver`. When the environment variable
//! `BLAZING_SMTLIB_LEAN_DRIVER` holds the path of the Lean driver
//! executable, the same requests are sent to that driver instead, so the
//! same tests check the Lean port. The protocol is described in
//! `lean/driver-protocol.md`, section "The writer".
//!
//! Either way the answers are reported in plain values, as the library's
//! error types cannot be built from the driver's answer.

// Every test file that includes this module uses its own part of it.
#![allow(dead_code)]

pub mod driver;

use std::cell::RefCell;
use std::ffi::OsString;
use std::io::{BufRead, BufReader, Write};
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use blazing_smtlib::{
    SmtVersion, SmtWriteStyle,
    token::{SmtReserved, SmtToken},
};

/// How a request writes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Writing {
    /// Each token by itself, as `SmtToken::write_smt` writes it.
    TokenByToken,
    /// With a writer of the style.
    Writer(SmtWriteStyle),
}

/// What is handed to the writer, as a word of the request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Item(String);

impl Item {
    /// The bytes, lexed as one whole input into the writer in the version it
    /// writes in.
    pub fn lex(bytes: &[u8]) -> Self {
        Item(format!("lex:{}", hex(bytes)))
    }

    /// One write of the tokens.
    pub fn write<'t>(tokens: impl IntoIterator<Item = SmtToken<'t>>) -> Self {
        Item(format!("write:{}", token_words(tokens)))
    }

    /// One consumption by the writer of a cursor that holds the tokens.
    pub fn consume<'t>(tokens: impl IntoIterator<Item = SmtToken<'t>>) -> Self {
        Item(format!("consume:{}", token_words(tokens)))
    }

    /// A change of the version the writer writes the following tokens in.
    pub fn version(version: SmtVersion) -> Self {
        Item(format!("version:{}", version_name(version)))
    }
}

/// Why writing failed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WriteFailure {
    /// The writer under the writer failed, with this message.
    Io(Vec<u8>),
    /// The reserved word is not reserved in the version written in.
    NotInVersion(SmtReserved),
}

/// The answer to an item.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Answer {
    /// The item was done.
    Ok,
    /// The writer consumed the cursor and broke, leaving this many tokens.
    Break(usize),
    /// The writer consumed the cursor and continued, leaving this many
    /// tokens.
    Continue(usize),
    /// Writing failed.
    Failed(WriteFailure),
    /// The input of a lexed item does not lex: the response line.
    Lexical(String),
}

/// What a request reported.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Written {
    /// The answer to each item, in order.
    pub answers: Vec<Answer>,
    /// Everything written.
    pub out: Vec<u8>,
}

impl Written {
    /// What was written, for a request whose items all succeeded.
    pub fn text(self) -> Vec<u8> {
        assert!(
            self.answers.iter().all(|answer| *answer == Answer::Ok),
            "every item should succeed: {:?}",
            self.answers
        );
        self.out
    }
}

/// Writes the items in the version, as `writing` says, into a writer that
/// fails every write if `fails` is set.
pub fn write(version: SmtVersion, writing: Writing, fails: bool, items: &[Item]) -> Written {
    let style = match writing {
        Writing::TokenByToken => "-",
        Writing::Writer(SmtWriteStyle::Line) => "line",
        Writing::Writer(SmtWriteStyle::Compact) => "compact",
        Writing::Writer(SmtWriteStyle::Layout) => "layout",
    };
    let mut request = format!("write {} {style}", version_name(version));
    if fails {
        request.push_str(" fail");
    }
    for item in items {
        request.push(' ');
        request.push_str(&item.0);
    }
    let mut answers = Vec::new();
    for line in respond(&request) {
        let line = line.as_str();
        let fields: Vec<&str> = line.split(' ').collect();
        let answer = match fields.as_slice() {
            ["out", bytes] => {
                return Written {
                    answers,
                    out: unhex(prefixed('x', bytes, line), line),
                };
            }
            ["ok"] => Answer::Ok,
            ["break", left] => Answer::Break(count(left, line)),
            ["continue", left] => Answer::Continue(count(left, line)),
            ["werr", "io", message] => {
                Answer::Failed(WriteFailure::Io(unhex(prefixed('x', message, line), line)))
            }
            ["werr", "not-in-version", word] => {
                let reserved = [
                    SmtVersion::V2_7,
                    SmtVersion::V2_6,
                    SmtVersion::V2_5,
                    SmtVersion::V2_0,
                ]
                .into_iter()
                .find_map(|version| SmtReserved::from_bytes(word.as_bytes(), version))
                .unwrap_or_else(|| panic!("the driver sent an unknown reserved word: {line:?}"));
                Answer::Failed(WriteFailure::NotInVersion(reserved))
            }
            ["err", ..] => Answer::Lexical(line.to_string()),
            ["fail", ..] => panic!("the driver refused {request:?}: {line:?}"),
            _ => panic!("the driver sent a line that is not understood: {line:?}"),
        };
        answers.push(answer);
    }
    panic!("the response to {request:?} has no closing line")
}

/// Writes the items in the version, as `writing` says, and returns what was
/// written, for items that all succeed.
pub fn written(version: SmtVersion, writing: Writing, items: &[Item]) -> Vec<u8> {
    write(version, writing, false, items).text()
}

// --- The words of the request ---

fn version_name(version: SmtVersion) -> &'static str {
    std::str::from_utf8(version.as_decimal().as_slice()).expect("a version decimal is ASCII")
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn unhex(digits: &str, line: &str) -> Vec<u8> {
    assert!(
        digits.len().is_multiple_of(2),
        "the driver sent an odd number of hexadecimal digits: {line:?}"
    );
    (0..digits.len())
        .step_by(2)
        .map(|at| {
            digits
                .get(at..at + 2)
                .and_then(|pair| u8::from_str_radix(pair, 16).ok())
                .unwrap_or_else(|| panic!("the driver sent bad hexadecimal digits: {line:?}"))
        })
        .collect()
}

fn prefixed<'f>(prefix: char, field: &'f str, line: &str) -> &'f str {
    field
        .strip_prefix(prefix)
        .unwrap_or_else(|| panic!("the driver sent a field without its prefix: {line:?}"))
}

fn count(field: &str, line: &str) -> usize {
    field
        .parse()
        .unwrap_or_else(|_| panic!("the driver sent a bad count: {line:?}"))
}

/// The word of a token.
fn token_word(token: SmtToken<'_>) -> String {
    match token {
        SmtToken::ParenOpen => "(".into(),
        SmtToken::ParenClose => ")".into(),
        SmtToken::Numeral(digits) => format!("N{}", hex(digits.as_slice())),
        SmtToken::Decimal(text) => format!("D{}", hex(text.as_slice())),
        SmtToken::Hexadecimal(digits) => format!("X{}", hex(digits.as_slice())),
        SmtToken::Binary(digits) => format!("B{}", hex(digits.as_slice())),
        SmtToken::String(content) => format!("S{}", hex(content.as_slice())),
        SmtToken::Keyword(name) => format!("k{}", hex(name.as_slice())),
        SmtToken::Symbol(symbol) if symbol.is_quoted() => format!("q{}", hex(symbol.as_slice())),
        SmtToken::Symbol(symbol) => format!("u{}", hex(symbol.as_slice())),
        SmtToken::Reserved(reserved) => format!("r{}", reserved.as_str()),
        SmtToken::Whitespace(text) => format!("w{}", hex(text.as_slice())),
        SmtToken::Comment(text) => format!("c{}", hex(text.as_slice())),
        SmtToken::EndOfFile => "e".into(),
    }
}

/// The words of the tokens, separated by commas.
fn token_words<'t>(tokens: impl IntoIterator<Item = SmtToken<'t>>) -> String {
    tokens
        .into_iter()
        .map(token_word)
        .collect::<Vec<_>>()
        .join(",")
}

// --- The Lean driver ---

/// Whether the tests run against the Lean driver.
fn lean_driver() -> Option<OsString> {
    std::env::var_os("BLAZING_SMTLIB_LEAN_DRIVER")
}

/// A running driver. One serves all the requests of a test thread.
struct Driver {
    child: Child,
    requests: Option<ChildStdin>,
    responses: BufReader<ChildStdout>,
}

impl Drop for Driver {
    fn drop(&mut self) {
        // the driver exits when its input ends
        self.requests = None;
        let _ = self.child.wait();
    }
}

thread_local! {
    static DRIVER: RefCell<Option<Driver>> = const { RefCell::new(None) };
}

fn start_driver(path: &OsString) -> Driver {
    let mut child = Command::new(path)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap_or_else(|err| panic!("cannot start the Lean driver {path:?}: {err}"));
    let requests = child.stdin.take().expect("the driver's input is piped");
    let responses = BufReader::new(child.stdout.take().expect("the driver's output is piped"));
    Driver {
        child,
        requests: Some(requests),
        responses,
    }
}

/// The lines of the response to the request, from the Lean driver if the
/// tests run against it and from the Rust library otherwise.
fn respond(request: &str) -> Vec<String> {
    let Some(path) = lean_driver() else {
        let response = driver::answer(request)
            .unwrap_or_else(|message| panic!("the request {request:?} is refused: {message}"));
        return response.lines().map(str::to_string).collect();
    };
    DRIVER.with(|driver| {
        let mut driver = driver.borrow_mut();
        let driver = driver.get_or_insert_with(|| start_driver(&path));
        let requests = driver
            .requests
            .as_mut()
            .expect("a running driver has its input open");
        requests
            .write_all(format!("{request}\n").as_bytes())
            .and_then(|()| requests.flush())
            .unwrap_or_else(|err| panic!("cannot send a request to the Lean driver: {err}"));
        let mut lines = Vec::new();
        loop {
            let mut line = String::new();
            let read = driver
                .responses
                .read_line(&mut line)
                .unwrap_or_else(|err| panic!("cannot read the Lean driver's response: {err}"));
            assert!(
                read > 0,
                "the Lean driver ended in the middle of its response to {request:?}"
            );
            let line = line.trim_end_matches('\n').to_string();
            let last = line.starts_with("out ") || line.starts_with("fail ");
            lines.push(line);
            if last {
                return lines;
            }
        }
    })
}

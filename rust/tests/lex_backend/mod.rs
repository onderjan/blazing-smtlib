//! The lexer that the black-box lexer tests run against.
//!
//! By default it is the Rust lexer, called directly. When the environment
//! variable `BLAZING_SMTLIB_LEAN_DRIVER` holds the path of the Lean driver
//! executable, the same inputs are sent to that driver instead, so the same
//! tests check the Lean port. The protocol is described in
//! `lean/driver-protocol.md`.
//!
//! Either way a run is reported in plain values: the library's span and
//! error types cannot be built from the driver's answer, so the tests compare
//! locations as `(offset, line, column)` triples.

// Every test file that includes this module uses its own part of it.
#![allow(dead_code)]

pub mod driver;

use std::cell::RefCell;
use std::convert::Infallible;
use std::ffi::OsString;
use std::io::{BufRead, BufReader, Write};
use std::ops::ControlFlow;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use blazing_smtlib::{
    SmtLocation,
    lexer::{SmtLexErrorCause, SmtLexer, SmtLexicalErrorKind},
    token::{
        SmtBatchCursor, SmtConsume, SmtReserved, SmtSyntaxToken, SmtTokenCategory, SmtVersion,
    },
};

/// A location as `(offset, line, column)`, all zero-based.
pub type Loc = (u64, u64, u64);

pub fn loc(location: SmtLocation) -> Loc {
    (location.offset(), location.line(), location.column())
}

/// What a token is once it is classified under the version of the run.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexedKind {
    Symbol(Vec<u8>),
    Reserved(SmtReserved),
    Keyword(Vec<u8>),
    EndOfFile,
    Other,
}

/// A token as the handler received it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexedToken {
    pub ty: SmtTokenCategory,
    pub content: Vec<u8>,
    pub start: Loc,
    pub end: Loc,
    pub kind: LexedKind,
}

impl LexedToken {
    /// The reserved word the token is, if any.
    pub fn reserved(&self) -> Option<SmtReserved> {
        match self.kind {
            LexedKind::Reserved(reserved) => Some(reserved),
            _ => None,
        }
    }
}

/// A lexer error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexedError {
    pub kind: SmtLexicalErrorKind,
    pub start: Loc,
    pub end: Loc,
}

/// One thing fed to the lexer.
#[derive(Debug, Clone, Copy)]
pub enum Feed<'a> {
    Slice(&'a [u8]),
    Eof,
}

/// Everything observable about one run of the lexer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lexed {
    /// The tokens handed over, in order.
    pub tokens: Vec<LexedToken>,
    /// The lexer's current location after each feed that succeeded.
    pub locations: Vec<Loc>,
    /// The error that ended the run. The feed that raised it is the one
    /// after those counted in `locations`.
    pub error: Option<LexedError>,
}

/// Whether the tests run against the Lean driver.
pub fn lean_driver() -> Option<OsString> {
    std::env::var_os("BLAZING_SMTLIB_LEAN_DRIVER")
}

/// Runs a fresh lexer of the version over the feeds, stopping at the first
/// error. The handler behind it takes every token and always continues.
pub fn lex(version: SmtVersion, feeds: &[Feed<'_>]) -> Lexed {
    match lean_driver() {
        Some(path) => lex_with_driver(&path, version, feeds),
        None => rust_lex(version, feeds),
    }
}

/// Runs a fresh lexer over the input as one slice, then the end of the input.
pub fn lex_whole(version: SmtVersion, input: &[u8]) -> Lexed {
    lex(version, &[Feed::Slice(input), Feed::Eof])
}

/// Runs a fresh lexer over the pieces as one slice each, then the end of the
/// input.
pub fn lex_pieces(version: SmtVersion, pieces: &[&[u8]]) -> Lexed {
    let mut feeds: Vec<Feed<'_>> = pieces.iter().map(|piece| Feed::Slice(piece)).collect();
    feeds.push(Feed::Eof);
    lex(version, &feeds)
}

// --- The Rust lexer ---

/// Takes every token. `WHITESPACE` says whether it consumes whitespace and
/// comments.
struct Collect<'a, const WHITESPACE: bool> {
    version: SmtVersion,
    tokens: &'a mut Vec<LexedToken>,
}

impl<const WHITESPACE: bool> SmtConsume for Collect<'_, WHITESPACE> {
    type Result = ();
    type Error = Infallible;
    const CONSUMES_WHITESPACE_AND_COMMENTS: bool = WHITESPACE;

    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        while let Some(token) = cursor.next() {
            let kind = match SmtSyntaxToken::from_token(token, self.version) {
                SmtSyntaxToken::Symbol(symbol) => LexedKind::Symbol(symbol.as_slice().to_vec()),
                SmtSyntaxToken::Reserved(reserved) => LexedKind::Reserved(reserved),
                SmtSyntaxToken::Keyword(keyword) => LexedKind::Keyword(keyword.as_slice().to_vec()),
                SmtSyntaxToken::EndOfFile => LexedKind::EndOfFile,
                _ => LexedKind::Other,
            };
            self.tokens.push(LexedToken {
                ty: token.category(),
                content: token.content().to_vec(),
                start: loc(token.span().start()),
                end: loc(token.span().end()),
                kind,
            });
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Runs a fresh Rust lexer over the feeds, whatever lexer the tests run
/// against.
pub fn rust_lex(version: SmtVersion, feeds: &[Feed<'_>]) -> Lexed {
    rust_lex_as::<false>(version, feeds)
}

fn rust_lex_as<const WHITESPACE: bool>(version: SmtVersion, feeds: &[Feed<'_>]) -> Lexed {
    let mut tokens = Vec::new();
    let mut locations = Vec::new();
    let mut error = None;
    {
        let mut lexer = SmtLexer::new(
            Collect::<WHITESPACE> {
                version,
                tokens: &mut tokens,
            },
            version,
        );
        for feed in feeds {
            let result = match feed {
                Feed::Slice(slice) => lexer.lex_slice(slice),
                Feed::Eof => lexer.lex_eof(),
            };
            match result {
                Ok(_) => locations.push(loc(lexer.current_location())),
                Err(err) => match err.into_cause() {
                    SmtLexErrorCause::Lexical(err) => {
                        error = Some(LexedError {
                            kind: *err.kind(),
                            start: loc(err.span().start()),
                            end: loc(err.span().end()),
                        });
                        break;
                    }
                    SmtLexErrorCause::Consumer(never) => match never {},
                },
            }
        }
    }
    Lexed {
        tokens,
        locations,
        error,
    }
}

/// Runs a fresh Rust lexer over the whole input through its `lex_all`.
pub fn rust_lex_all(version: SmtVersion, input: &[u8]) -> Lexed {
    let mut tokens = Vec::new();
    let mut locations = Vec::new();
    let mut error = None;
    {
        let mut lexer = SmtLexer::new(
            Collect::<false> {
                version,
                tokens: &mut tokens,
            },
            version,
        );
        match lexer.lex_all(input) {
            Ok(_) => locations.push(loc(lexer.current_location())),
            Err(err) => match err.into_cause() {
                SmtLexErrorCause::Lexical(err) => {
                    error = Some(LexedError {
                        kind: *err.kind(),
                        start: loc(err.span().start()),
                        end: loc(err.span().end()),
                    });
                }
                SmtLexErrorCause::Consumer(never) => match never {},
            },
        }
    }
    Lexed {
        tokens,
        locations,
        error,
    }
}

// --- The Lean driver ---

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

const TOKEN_TYPES: [SmtTokenCategory; 13] = [
    SmtTokenCategory::ParenOpen,
    SmtTokenCategory::ParenClose,
    SmtTokenCategory::Numeral,
    SmtTokenCategory::Decimal,
    SmtTokenCategory::Hexadecimal,
    SmtTokenCategory::Binary,
    SmtTokenCategory::String,
    SmtTokenCategory::Keyword,
    SmtTokenCategory::UnquotedSymbol,
    SmtTokenCategory::QuotedSymbol,
    SmtTokenCategory::Whitespace,
    SmtTokenCategory::Comment,
    SmtTokenCategory::EndOfFile,
];

const ERROR_KINDS: [SmtLexicalErrorKind; 13] = [
    SmtLexicalErrorKind::UnexpectedCharacter,
    SmtLexicalErrorKind::FractionDigitExpected,
    SmtLexicalErrorKind::HexadecimalDigitExpected,
    SmtLexicalErrorKind::BinaryDigitExpected,
    SmtLexicalErrorKind::BaseSelectionExpected,
    SmtLexicalErrorKind::UnclosedStringLiteral,
    SmtLexicalErrorKind::ForbiddenCharInString,
    SmtLexicalErrorKind::ForbiddenKeywordName,
    SmtLexicalErrorKind::BackslashInQuotedSymbol,
    SmtLexicalErrorKind::ForbiddenCharInQuotedSymbol,
    SmtLexicalErrorKind::UnclosedQuotedSymbol,
    SmtLexicalErrorKind::NumeralLeadingZero,
    SmtLexicalErrorKind::MissingDelimiter,
];

fn version_name(version: SmtVersion) -> &'static str {
    match version {
        SmtVersion::V2_0 => "2.0",
        SmtVersion::V2_5 => "2.5",
        SmtVersion::V2_6 => "2.6",
        SmtVersion::V2_7 => "2.7",
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn unhex(digits: &str, line: &str) -> Vec<u8> {
    assert!(
        digits.len().is_multiple_of(2),
        "the Lean driver sent an odd number of hexadecimal digits: {line:?}"
    );
    (0..digits.len())
        .step_by(2)
        .map(|at| {
            digits
                .get(at..at + 2)
                .and_then(|pair| u8::from_str_radix(pair, 16).ok())
                .unwrap_or_else(|| panic!("the Lean driver sent bad hexadecimal digits: {line:?}"))
        })
        .collect()
}

/// Parses a location written as `offset:line:column`.
fn parse_loc(field: &str, line: &str) -> Loc {
    let mut numbers = field.split(':').map(|number| {
        number
            .parse::<u64>()
            .unwrap_or_else(|_| panic!("the Lean driver sent a bad location: {line:?}"))
    });
    match (
        numbers.next(),
        numbers.next(),
        numbers.next(),
        numbers.next(),
    ) {
        (Some(offset), Some(line_number), Some(column), None) => (offset, line_number, column),
        _ => panic!("the Lean driver sent a bad location: {line:?}"),
    }
}

/// Finds the value whose debug spelling is the name.
fn by_name<T: Copy + std::fmt::Debug>(values: &[T], name: &str, line: &str) -> T {
    values
        .iter()
        .copied()
        .find(|value| format!("{value:?}") == name)
        .unwrap_or_else(|| panic!("the Lean driver sent an unknown name {name:?}: {line:?}"))
}

/// What a token is, from its type, its content and the reserved word the
/// driver reported it to be.
fn kind_of(ty: SmtTokenCategory, content: &[u8], reserved: Option<SmtReserved>) -> LexedKind {
    match (reserved, ty) {
        (Some(reserved), _) => LexedKind::Reserved(reserved),
        (None, SmtTokenCategory::UnquotedSymbol | SmtTokenCategory::QuotedSymbol) => {
            LexedKind::Symbol(content.to_vec())
        }
        (None, SmtTokenCategory::Keyword) => LexedKind::Keyword(content.to_vec()),
        (None, SmtTokenCategory::EndOfFile) => LexedKind::EndOfFile,
        (None, _) => LexedKind::Other,
    }
}

/// The reserved word a token is, from the class the driver reported.
fn parse_reserved(
    class: &str,
    content: &[u8],
    version: SmtVersion,
    line: &str,
) -> Option<SmtReserved> {
    let is_command_name = match class {
        "-" => return None,
        "general" => false,
        "command" => true,
        _ => panic!("the Lean driver sent an unknown reserved class: {line:?}"),
    };
    let reserved = SmtReserved::from_bytes_opt(content, version).unwrap_or_else(|| {
        panic!("the Lean driver reported a reserved word that is none in {version:?}: {line:?}")
    });
    assert_eq!(
        reserved.is_command_name(),
        is_command_name,
        "the Lean driver reported the wrong reserved class: {line:?}"
    );
    Some(reserved)
}

fn lex_with_driver(path: &OsString, version: SmtVersion, feeds: &[Feed<'_>]) -> Lexed {
    let mut request = format!("lex {}", version_name(version));
    for feed in feeds {
        match feed {
            Feed::Slice(slice) => {
                request.push_str(" s");
                request.push_str(&hex(slice));
            }
            Feed::Eof => request.push_str(" e"),
        }
    }
    request.push('\n');

    DRIVER.with(|driver| {
        let mut driver = driver.borrow_mut();
        let driver = driver.get_or_insert_with(|| start_driver(path));
        let requests = driver
            .requests
            .as_mut()
            .expect("a running driver has its input open");
        requests
            .write_all(request.as_bytes())
            .and_then(|()| requests.flush())
            .unwrap_or_else(|err| panic!("cannot send a request to the Lean driver: {err}"));

        let mut lexed = Lexed {
            tokens: Vec::new(),
            locations: Vec::new(),
            error: None,
        };
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
            let line = line.trim_end_matches('\n');
            let fields: Vec<&str> = line.split(' ').collect();
            match fields.as_slice() {
                ["t", ty, start, end, reserved, content] => {
                    let content = content.strip_prefix('x').unwrap_or_else(|| {
                        panic!("the Lean driver sent content without its prefix: {line:?}")
                    });
                    let content = unhex(content, line);
                    let ty = by_name(&TOKEN_TYPES, ty, line);
                    let reserved = parse_reserved(reserved, &content, version, line);
                    lexed.tokens.push(LexedToken {
                        ty,
                        start: parse_loc(start, line),
                        end: parse_loc(end, line),
                        kind: kind_of(ty, &content, reserved),
                        content,
                    });
                }
                ["at", location] => lexed.locations.push(parse_loc(location, line)),
                ["ok"] => return lexed,
                ["err", kind, start, end] => {
                    lexed.error = Some(LexedError {
                        kind: by_name(&ERROR_KINDS, kind, line),
                        start: parse_loc(start, line),
                        end: parse_loc(end, line),
                    });
                    return lexed;
                }
                ["fail", ..] => panic!("the Lean driver refused {request:?}: {line:?}"),
                _ => panic!("the Lean driver sent a line that is not understood: {line:?}"),
            }
        }
    })
}

// --- Requests with options: scripted consumers, whitespace, recovery ---

/// The options of a request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Options {
    /// The consumer takes whitespace and comments.
    pub whitespace: bool,
    /// The lexer recovers from errors.
    pub recover: bool,
    /// What the consumer does.
    pub behaviour: driver::Behaviour,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            whitespace: false,
            recover: false,
            behaviour: driver::Behaviour::TakeAll,
        }
    }
}

/// One line of a response, in order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Line {
    /// A hand-over starts: the version its tokens were lexed under and
    /// their number. Only reported for a consumer with a plan.
    Handover { version: SmtVersion, count: usize },
    /// A token: of a hand-over for a consumer with a plan, a consumed one
    /// otherwise.
    Token(LexedToken),
    /// The consumer was made to abandon its unfinished work.
    Abandon(Loc),
    /// The consumer was told where the skipped input ends.
    Recover(Loc),
    /// The consumer finished at the location.
    Finish(Loc),
    /// A lexical error. With recovery it says where the input continues from.
    LexicalError {
        error: LexedError,
        continues: Option<Option<Loc>>,
    },
    /// An error of the consumer, by its name. With recovery it says where
    /// the input continues from.
    ConsumerError {
        name: String,
        continues: Option<Option<Loc>>,
    },
    /// A feed was applied: the lexer's location afterwards.
    At(Loc),
    /// The lexer's version after a feed. Only reported for a scripted consumer.
    Version(SmtVersion),
}

fn reply_word(reply: driver::Reply) -> String {
    match reply {
        driver::Reply::TakeAll => "t".into(),
        driver::Reply::Leave(taken) => format!("l{taken}"),
        driver::Reply::Finish(taken) => format!("f{taken}"),
        driver::Reply::Fail(taken) => format!("x{taken}"),
        driver::Reply::Switch(taken, version) => format!("v{taken}:{}", version_name(version)),
        driver::Reply::SwitchAndFinish(taken, version) => {
            format!("w{taken}:{}", version_name(version))
        }
    }
}

fn request_line(version: SmtVersion, options: &Options, feeds: &[Feed<'_>]) -> String {
    let mut request = format!("lex {}", version_name(version));
    if options.whitespace {
        request.push_str(" ws");
    }
    if options.recover {
        request.push_str(" recover");
    }
    match &options.behaviour {
        driver::Behaviour::TakeAll => {}
        driver::Behaviour::Plan(replies) => {
            let words: Vec<String> = replies.iter().copied().map(reply_word).collect();
            request.push_str(&format!(" plan={}", words.join(",")));
        }
        driver::Behaviour::Rules { refuse_end: false } => request.push_str(" rules"),
        driver::Behaviour::Rules { refuse_end: true } => request.push_str(" rules=refuse-end"),
    }
    for feed in feeds {
        match feed {
            Feed::Slice(slice) => {
                request.push_str(" s");
                request.push_str(&hex(slice));
            }
            Feed::Eof => request.push_str(" e"),
        }
    }
    request
}

/// Whether the line is the last one of a response.
fn ends_response(line: &str, recover: bool) -> bool {
    line == "ok"
        || line.starts_with("fail ")
        || (!recover && (line.starts_with("err ") || line.starts_with("cerr ")))
}

/// The lines of the response to the request, from the Lean driver if the
/// tests run against it and from the Rust lexer otherwise.
fn respond(request: &str, recover: bool) -> Vec<String> {
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
            let last = ends_response(&line, recover);
            lines.push(line);
            if last {
                return lines;
            }
        }
    })
}

/// Parses where the input continues from: a location, or `-` if it does not.
fn parse_continues(field: &str, line: &str) -> Option<Loc> {
    (field != "-").then(|| parse_loc(field, line))
}

fn parse_version(field: &str, line: &str) -> SmtVersion {
    SmtVersion::from_decimal_opt(field.as_bytes())
        .unwrap_or_else(|| panic!("the driver sent an unknown version: {line:?}"))
}

/// Runs a fresh lexer of the version over the feeds, with a consumer and a
/// kind of lexer as the options say, and returns everything it reported.
///
/// After an error of a recovering lexer, the rest of the failed feed is
/// applied again from where the input continues, until the feed is done.
pub fn run(version: SmtVersion, options: &Options, feeds: &[Feed<'_>]) -> Vec<Line> {
    let request = request_line(version, options, feeds);
    // the version in force, as far as the response tells
    let mut current = version;
    let mut lines = Vec::new();
    for line in respond(&request, options.recover) {
        let line = line.as_str();
        let fields: Vec<&str> = line.split(' ').collect();
        match fields.as_slice() {
            ["ok"] => break,
            ["h", version, count] => {
                current = parse_version(version, line);
                lines.push(Line::Handover {
                    version: current,
                    count: count
                        .parse()
                        .unwrap_or_else(|_| panic!("the driver sent a bad count: {line:?}")),
                });
            }
            ["t", ty, start, end, class, content] => {
                let content = content.strip_prefix('x').unwrap_or_else(|| {
                    panic!("the driver sent content without its prefix: {line:?}")
                });
                let content = unhex(content, line);
                let ty = by_name(&TOKEN_TYPES, ty, line);
                // a scripted consumer may have set another version by now, and
                // only a plan reports it with the hand-over: the word is looked
                // up under the version known, then under any other one
                let reserved = (*class != "-").then(|| {
                    [
                        current,
                        SmtVersion::V2_7,
                        SmtVersion::V2_6,
                        SmtVersion::V2_5,
                        SmtVersion::V2_0,
                    ]
                    .into_iter()
                    .find_map(|version| SmtReserved::from_bytes_opt(&content, version))
                    .unwrap_or_else(|| {
                        panic!("the driver reported a reserved word that is none: {line:?}")
                    })
                });
                lines.push(Line::Token(LexedToken {
                    ty,
                    start: parse_loc(start, line),
                    end: parse_loc(end, line),
                    kind: kind_of(ty, &content, reserved),
                    content,
                }));
            }
            ["ab", location] => lines.push(Line::Abandon(parse_loc(location, line))),
            ["rc", location] => lines.push(Line::Recover(parse_loc(location, line))),
            ["fin", location] => lines.push(Line::Finish(parse_loc(location, line))),
            ["at", location] => lines.push(Line::At(parse_loc(location, line))),
            ["v", version] => {
                current = parse_version(version, line);
                lines.push(Line::Version(current));
            }
            ["err", kind, start, end, rest @ ..] => lines.push(Line::LexicalError {
                error: LexedError {
                    kind: by_name(&ERROR_KINDS, kind, line),
                    start: parse_loc(start, line),
                    end: parse_loc(end, line),
                },
                continues: rest.first().map(|field| parse_continues(field, line)),
            }),
            ["cerr", name, rest @ ..] => lines.push(Line::ConsumerError {
                name: name.to_string(),
                continues: rest.first().map(|field| parse_continues(field, line)),
            }),
            ["fail", ..] => panic!("the driver refused {request:?}: {line:?}"),
            _ => panic!("the driver sent a line that is not understood: {line:?}"),
        }
    }
    lines
}

/// Runs a fresh lexer of the version over the feeds, stopping at the first
/// error, with a consumer that takes whitespace and comments too.
pub fn lex_with_whitespace(version: SmtVersion, feeds: &[Feed<'_>]) -> Lexed {
    let options = Options {
        whitespace: true,
        ..Options::default()
    };
    let mut lexed = Lexed {
        tokens: Vec::new(),
        locations: Vec::new(),
        error: None,
    };
    for line in run(version, &options, feeds) {
        match line {
            Line::Token(token) => lexed.tokens.push(token),
            Line::At(location) => lexed.locations.push(location),
            Line::LexicalError { error, .. } => lexed.error = Some(error),
            other => panic!("a line that no option asked for: {other:?}"),
        }
    }
    lexed
}

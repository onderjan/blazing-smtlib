//! The lexer driver protocol, answered by the Rust lexer.
//!
//! The protocol is described in `lean/driver-protocol.md`. This module is
//! the reference answer to it: the tests call it in process, and the
//! executable in `tools/rust-lex-driver` prints what it returns.

use std::cell::RefCell;
use std::io::{self, BufRead, Read};
use std::ops::ControlFlow;
use std::rc::Rc;

use blazing_smtlib::{
    SmtVersion,
    lexer::{
        SmtLexer, SmtLexerCursor, SmtLexerErrorKind, SmtLexerReadErrorKind, SmtLexerRecovery,
        SmtLexerToken, SmtRecover,
    },
    lexicon::SmtDecimal,
    span::SmtLocation,
    token::{
        SmtConsume, SmtConsumeFrom, SmtCursor, SmtLookahead, SmtReserved, SmtToken,
        SmtTokenCategory,
    },
};

/// What the consumer of a request does with one hand-over, by its plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reply {
    /// Take every token and continue.
    TakeAll,
    /// Take this many tokens and continue: the rest is handed over again.
    Leave(usize),
    /// Take this many tokens and finish.
    Finish(usize),
    /// Take this many tokens and fail.
    Fail(usize),
    /// Take this many tokens, set the version and continue.
    Switch(usize, SmtVersion),
    /// Take this many tokens, set the version and finish.
    SwitchAndFinish(usize, SmtVersion),
}

/// How the consumer of a request behaves. Whatever the behaviour, where it
/// would continue at the end-of-file token, the consumer breaks instead.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Behaviour {
    /// It takes every token and continues, except at the end of the input.
    TakeAll,
    /// It answers the hand-overs in order by the replies, and takes every
    /// token once they have run out.
    Plan(Vec<Reply>),
    /// It takes every token and fails by what the tokens are: on the symbol
    /// `bad`, on a closing parenthesis that closes nothing, and on the
    /// end-of-file token inside a parenthesis, or on every end-of-file token
    /// if `refuse_end` is set. The symbol `to-2.0` makes it set the version.
    Rules { refuse_end: bool },
    /// It takes every token and continues, and has the cursor discard the
    /// rest of the input once it has taken this many tokens, the end-of-file
    /// token not counted.
    Discard(usize),
}

/// The consumer of a request: writes what it is called with as response
/// lines. `WHITESPACE` says whether it takes whitespace and comments.
pub struct Scripted<const WHITESPACE: bool> {
    behaviour: Behaviour,
    /// The number of hand-overs answered by the plan.
    handed: usize,
    /// The number of tokens taken, the end-of-file token not counted, for
    /// the consumer that discards.
    taken: usize,
    /// The number of parentheses left open by the tokens taken by the rules.
    open: u64,
    out: Rc<RefCell<String>>,
}

impl<const WHITESPACE: bool> Scripted<WHITESPACE> {
    /// A consumer that writes its lines into `out`.
    pub fn new(behaviour: Behaviour, out: Rc<RefCell<String>>) -> Self {
        Self {
            behaviour,
            handed: 0,
            taken: 0,
            open: 0,
            out,
        }
    }
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

fn version_name(version: SmtVersion) -> &'static str {
    std::str::from_utf8(version.as_decimal().as_slice()).expect("a version decimal is ASCII")
}

fn token_line(token: SmtLexerToken<'_>, version: SmtVersion) -> String {
    let reserved = match SmtToken::from_lexer_token(token, version) {
        SmtToken::Reserved(SmtReserved::General(_)) => "general",
        SmtToken::Reserved(SmtReserved::CommandName(_)) => "command",
        _ => "-",
    };
    format!(
        "t {:?} {} {} {} x{}\n",
        token.category(),
        location(token.span().start()),
        location(token.span().end()),
        reserved,
        hex(token.content()),
    )
}

impl<const WHITESPACE: bool> SmtConsume for Scripted<WHITESPACE> {
    /// Whether the consumer finished by its behaviour, rather than only
    /// because it was handed the end of the input: every consumer breaks
    /// there at the latest, and that break is not reported.
    type Result = bool;
    /// The name of what made the consumer fail.
    type Error = &'static str;
    const IS_CONCRETE: bool = WHITESPACE;
}

impl<'a, const WHITESPACE: bool> SmtConsumeFrom<SmtLexerCursor<'a>> for Scripted<WHITESPACE> {
    fn consume(
        &mut self,
        cursor: &mut SmtLexerCursor<'a>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        // the end-of-file token is handed over alone
        let at_end = cursor
            .peek()
            .is_some_and(|token| token.category() == SmtTokenCategory::EndOfFile);
        match self.take(cursor)? {
            ControlFlow::Continue(()) if at_end => Ok(ControlFlow::Break(false)),
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(()) => Ok(ControlFlow::Break(true)),
        }
    }
}

impl<const WHITESPACE: bool> Scripted<WHITESPACE> {
    /// Takes the tokens of a hand-over as the behaviour says, and answers as
    /// it says.
    fn take(&mut self, cursor: &mut SmtLexerCursor<'_>) -> Result<ControlFlow<()>, &'static str> {
        // the version the tokens of this hand-over were lexed under
        let version = cursor.version();
        match &self.behaviour {
            Behaviour::TakeAll => {
                while let Some(token) = cursor.next() {
                    self.out.borrow_mut().push_str(&token_line(token, version));
                }
                Ok(ControlFlow::Continue(()))
            }
            Behaviour::Plan(replies) => {
                let reply = replies.get(self.handed).copied().unwrap_or(Reply::TakeAll);
                self.handed += 1;

                // Report every token of the hand-over, also those the reply
                // will not take. A consumer cannot look at tokens without
                // consuming them, so this goes through an attempt that takes
                // every token and then fails, which consumes nothing.
                let lines = RefCell::new(String::new());
                let count = RefCell::new(0usize);
                let failed: Option<()> = cursor.attempt(|window| {
                    while let Some(token) = window.next() {
                        lines.borrow_mut().push_str(&token_line(token, version));
                        *count.borrow_mut() += 1;
                    }
                    None
                });
                assert!(failed.is_none(), "the reporting attempt takes nothing");
                let count = count.into_inner();
                {
                    let mut out = self.out.borrow_mut();
                    out.push_str(&format!("h {} {count}\n", version_name(version)));
                    out.push_str(&lines.into_inner());
                }

                let taken = match reply {
                    Reply::TakeAll => count,
                    Reply::Leave(taken)
                    | Reply::Finish(taken)
                    | Reply::Fail(taken)
                    | Reply::Switch(taken, _)
                    | Reply::SwitchAndFinish(taken, _) => taken.min(count),
                };
                for _ in 0..taken {
                    cursor.next();
                }
                match reply {
                    Reply::TakeAll | Reply::Leave(_) => Ok(ControlFlow::Continue(())),
                    Reply::Finish(_) => Ok(ControlFlow::Break(())),
                    Reply::Fail(_) => Err("plan"),
                    Reply::Switch(_, version) => {
                        cursor
                            .set_version(version)
                            .expect("lexer should switch version");
                        Ok(ControlFlow::Continue(()))
                    }
                    Reply::SwitchAndFinish(_, version) => {
                        cursor
                            .set_version(version)
                            .expect("lexer should switch version");
                        Ok(ControlFlow::Break(()))
                    }
                }
            }
            Behaviour::Rules { refuse_end } => {
                while let Some(token) = cursor.next() {
                    self.out.borrow_mut().push_str(&token_line(token, version));
                    match token.category() {
                        SmtTokenCategory::ParenOpen => self.open += 1,
                        SmtTokenCategory::ParenClose => {
                            if self.open == 0 {
                                return Err("unmatched");
                            }
                            self.open -= 1;
                        }
                        SmtTokenCategory::EndOfFile => {
                            if *refuse_end || self.open > 0 {
                                return Err("unexpected-end");
                            }
                        }
                        SmtTokenCategory::UnquotedSymbol if token.content() == b"bad" => {
                            return Err("bad");
                        }
                        SmtTokenCategory::UnquotedSymbol if token.content() == b"to-2.0" => {
                            cursor
                                .set_version(SmtVersion::V2_0)
                                .expect("lexer should switch version");
                        }
                        _ => {}
                    }
                }
                Ok(ControlFlow::Continue(()))
            }
            Behaviour::Discard(after) => {
                let after = *after;
                while let Some(token) = cursor.next() {
                    self.out.borrow_mut().push_str(&token_line(token, version));
                    if token.category() != SmtTokenCategory::EndOfFile {
                        self.taken += 1;
                        if self.taken == after {
                            cursor.discard_rest();
                        }
                    }
                }
                Ok(ControlFlow::Continue(()))
            }
        }
    }
}

impl<const WHITESPACE: bool> SmtRecover for Scripted<WHITESPACE> {
    fn abandon(&mut self, at: SmtLocation) {
        self.out
            .borrow_mut()
            .push_str(&format!("ab {}\n", location(at)));
        // nothing is open any more
        self.open = 0;
    }

    fn recover(&mut self, at: SmtLocation) {
        self.out
            .borrow_mut()
            .push_str(&format!("rc {}\n", location(at)));
    }
}

/// One thing fed to the lexer: a slice, or the end of the input.
type Feed = Option<Vec<u8>>;

/// The message of the failure of the buffered reader of a `lex-from`
/// request that fails after its bytes.
pub const READER_FAILURE: &str = "the test reader fails after its input";

/// What a request lexes.
enum Input {
    /// `lex`: the feeds, applied in order.
    Feeds(Vec<Feed>),
    /// `lex-from`: a buffered reader that hands out the bytes `size` at a
    /// time, and then ends or, if `fails`, fails.
    Reader {
        size: usize,
        bytes: Vec<u8>,
        fails: bool,
    },
    /// `lex-file`: the file at the path.
    File(std::path::PathBuf),
}

/// A request, read from its line.
struct Request {
    version: SmtVersion,
    whitespace: bool,
    recover: bool,
    behaviour: Behaviour,
    input: Input,
}

/// Decodes the hexadecimal digits of a slice operand.
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

fn read_reply(word: &str) -> Result<Reply, String> {
    let bad = || format!("unknown reply {word:?}");
    if word == "t" {
        return Ok(Reply::TakeAll);
    }
    let (letter, rest) = word.split_at_checked(1).ok_or_else(bad)?;
    let (count, version) = match rest.split_once(':') {
        Some((count, version)) => (count, Some(read_version(version)?)),
        None => (rest, None),
    };
    let count: usize = count.parse().map_err(|_| bad())?;
    if count == 0 {
        return Err(format!("a reply must take a token: {word:?}"));
    }
    match (letter, version) {
        ("l", None) => Ok(Reply::Leave(count)),
        ("f", None) => Ok(Reply::Finish(count)),
        ("x", None) => Ok(Reply::Fail(count)),
        ("v", Some(version)) => Ok(Reply::Switch(count, version)),
        ("w", Some(version)) => Ok(Reply::SwitchAndFinish(count, version)),
        _ => Err(bad()),
    }
}

/// Reads the word as an option into the request. Returns whether it is one.
fn read_option(word: &str, request: &mut Request) -> Result<bool, String> {
    // at most one of the options that script the consumer
    let scripted = request.behaviour != Behaviour::TakeAll;
    match word {
        "ws" => request.whitespace = true,
        "recover" => request.recover = true,
        "rules" if !scripted => request.behaviour = Behaviour::Rules { refuse_end: false },
        "rules=refuse-end" if !scripted => {
            request.behaviour = Behaviour::Rules { refuse_end: true };
        }
        _ => {
            if let Some(replies) = word.strip_prefix("plan=").filter(|_| !scripted) {
                // no replies at all are a plan too: every token is taken,
                // and the hand-overs are reported
                let replies: Result<Vec<Reply>, String> = replies
                    .split(',')
                    .filter(|_| !replies.is_empty())
                    .map(read_reply)
                    .collect();
                request.behaviour = Behaviour::Plan(replies?);
            } else if let Some(after) = word.strip_prefix("discard=").filter(|_| !scripted) {
                let after: usize = after
                    .parse()
                    .map_err(|_| format!("unknown option {word:?}"))?;
                if after == 0 {
                    return Err(format!("the consumer must take a token first: {word:?}"));
                }
                request.behaviour = Behaviour::Discard(after);
            } else {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

/// Reads the operands of a `lex-from` request: the buffer size, the bytes
/// and how the reader ends.
fn read_reader(operands: &[&str]) -> Result<Input, String> {
    let [size, bytes, ending] = operands else {
        return Err("lex-from takes a size, bytes and an ending".into());
    };
    let size: usize = size
        .parse()
        .ok()
        .filter(|&size| size > 0)
        .ok_or_else(|| format!("bad buffer size {size:?}"))?;
    let bytes = match bytes.strip_prefix('s') {
        Some(digits) => unhex(digits)?,
        None => return Err(format!("bad bytes {bytes:?}")),
    };
    let fails = match *ending {
        "end" => false,
        "fail" => true,
        _ => return Err(format!("unknown ending {ending:?}")),
    };
    Ok(Input::Reader { size, bytes, fails })
}

fn read_request(line: &str) -> Result<Request, String> {
    let mut words = line.split(' ');
    let kind = words.next();
    if !matches!(kind, Some("lex" | "lex-from" | "lex-file")) {
        return Err("unknown request".into());
    }
    let mut request = Request {
        version: read_version(words.next().ok_or("no version")?)?,
        whitespace: false,
        recover: false,
        behaviour: Behaviour::TakeAll,
        input: Input::Feeds(Vec::new()),
    };
    // the options come before the other operands
    let mut operands = Vec::new();
    for word in words {
        if operands.is_empty() && read_option(word, &mut request)? {
            continue;
        }
        operands.push(word);
    }
    request.input = match kind {
        Some("lex") => Input::Feeds(
            operands
                .into_iter()
                .map(|word| match word {
                    "e" => Ok(None),
                    _ => match word.strip_prefix('s') {
                        Some(digits) => Ok(Some(unhex(digits)?)),
                        None => Err(format!("unknown operation {word:?}")),
                    },
                })
                .collect::<Result<_, String>>()?,
        ),
        Some("lex-from") => read_reader(&operands)?,
        _ => match operands.as_slice() {
            [digits] => {
                let path = String::from_utf8(unhex(digits)?)
                    .map_err(|_| format!("the path {digits} is not UTF-8"))?;
                Input::File(path.into())
            }
            _ => return Err("lex-file takes a path".into()),
        },
    };
    if request.recover && !matches!(request.input, Input::Feeds(_)) {
        return Err("only lex takes recover".into());
    }
    Ok(request)
}

/// Applies the feeds of the request to the lexer and writes the lines of
/// the feeds themselves. Returns whether every feed was applied.
fn drive<const WHITESPACE: bool, R: SmtLexerRecovery<Scripted<WHITESPACE>>>(
    request: &Request,
    feeds: &[Feed],
    out: &RefCell<String>,
    lexer: &mut SmtLexer<Scripted<WHITESPACE>, R>,
) -> bool {
    let scripted = request.behaviour != Behaviour::TakeAll;
    for feed in feeds {
        // the part of a slice that the lexer has not taken yet
        let mut from = 0;
        loop {
            let before = lexer.current_location().offset();
            // a slice holds the result back, the end of the input returns it
            let result = match feed {
                Some(slice) => lexer.lex_slice(&slice[from..]).map(|()| None),
                None => lexer.lex_eof().map(Some),
            };
            let err = match result {
                Ok(None) => break,
                Ok(Some(located)) => {
                    // only a finish by the behaviour is reported
                    if *located.value() {
                        out.borrow_mut()
                            .push_str(&format!("fin {}\n", location(located.location())));
                    }
                    break;
                }
                Err(err) => err,
            };

            let continues = err.continues_from();
            let mut line = match err.kind() {
                SmtLexerErrorKind::Lexical(kind) => format!(
                    "err {:?} {} {}",
                    kind,
                    location(err.span().start()),
                    location(err.span().end()),
                ),
                SmtLexerErrorKind::Consumer(name) => format!("cerr {name}"),
            };
            if request.recover {
                // where the input continues from, if it does
                line.push(' ');
                line.push_str(&continues.map_or("-".into(), location));
            }
            line.push('\n');
            out.borrow_mut().push_str(&line);

            match continues {
                // the rest of the feed is applied again from there
                Some(continues) => from += (continues.offset() - before) as usize,
                // the input has ended with the error, the feed is done
                None if request.recover => break,
                // the lexer has stopped for good, and the response with it
                None => return false,
            }
        }
        let mut out = out.borrow_mut();
        out.push_str(&format!("at {}\n", location(lexer.current_location())));
        if scripted {
            out.push_str(&format!("v {}\n", version_name(lexer.version())));
        }
    }
    true
}

/// The buffered reader of a `lex-from` request: hands out its bytes `size`
/// at a time, and then ends or, if `fails`, fails.
struct Chunks<'a> {
    bytes: &'a [u8],
    size: usize,
    fails: bool,
}

impl Read for Chunks<'_> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let chunk = self.fill_buf()?;
        let len = chunk.len().min(buf.len());
        buf[..len].copy_from_slice(&chunk[..len]);
        self.consume(len);
        Ok(len)
    }
}

impl BufRead for Chunks<'_> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        if self.bytes.is_empty() && self.fails {
            return Err(io::Error::other(READER_FAILURE));
        }
        Ok(&self.bytes[..self.size.min(self.bytes.len())])
    }

    fn consume(&mut self, amount: usize) {
        self.bytes = &self.bytes[amount..];
    }
}

/// Lexes the input of a `lex-from` or a `lex-file` request as a whole
/// input, and writes the line of the outcome.
fn read<const WHITESPACE: bool>(request: &Request, out: &Rc<RefCell<String>>) {
    let mut lexer = SmtLexer::new(
        Scripted::<WHITESPACE>::new(request.behaviour.clone(), out.clone()),
        request.version,
    );
    // the bytes of the buffered reader not consumed, for `lex-from`
    let mut rest = None;
    let result = match &request.input {
        Input::Reader { size, bytes, fails } => {
            let mut reader = Chunks {
                bytes,
                size: *size,
                fails: *fails,
            };
            let result = lexer.lex_from(&mut reader);
            rest = Some(reader.bytes.len());
            result
        }
        Input::File(path) => lexer.lex_file(path),
        Input::Feeds(_) => panic!("a request with feeds is driven, not read"),
    };
    let lines = match result {
        Ok(located) => {
            let mut lines = String::new();
            // only a finish by the behaviour is reported
            if *located.value() {
                lines.push_str(&format!("fin {}\n", location(located.location())));
            }
            lines.push_str(&format!("done {}", location(located.location())));
            if let Some(rest) = rest {
                lines.push_str(&format!(" {rest}"));
            }
            lines
        }
        Err(err) => match err.kind() {
            SmtLexerReadErrorKind::Lexical(kind) => format!(
                "err {:?} {} {}",
                kind,
                location(err.span().start()),
                location(err.span().end()),
            ),
            SmtLexerReadErrorKind::Consumer(name) => format!("cerr {name}"),
            SmtLexerReadErrorKind::Io(io) => format!(
                "ioerr {} {} x{}",
                location(err.span().start()),
                location(err.span().end()),
                hex(io.to_string().as_bytes()),
            ),
        },
    };
    let mut out = out.borrow_mut();
    out.push_str(&lines);
    out.push('\n');
}

/// Answers one request line with the lines of its response.
pub fn answer(line: &str) -> Result<String, String> {
    // decode the whole request first, so that a malformed one produces no lines
    let request = read_request(line)?;

    // the consumer writes into the response while the lexer owns it
    let out = Rc::new(RefCell::new(String::new()));
    let feeds = match &request.input {
        Input::Feeds(feeds) => feeds,
        Input::Reader { .. } | Input::File(_) => {
            // the line of the outcome ends the response
            if request.whitespace {
                read::<true>(&request, &out);
            } else {
                read::<false>(&request, &out);
            }
            return Ok(out.take());
        }
    };
    let behaviour = request.behaviour.clone();
    let version = request.version;
    let complete = match (request.whitespace, request.recover) {
        (false, false) => {
            let mut lexer = SmtLexer::new(Scripted::<false>::new(behaviour, out.clone()), version);
            drive(&request, feeds, &out, &mut lexer)
        }
        (true, false) => {
            let mut lexer = SmtLexer::new(Scripted::<true>::new(behaviour, out.clone()), version);
            drive(&request, feeds, &out, &mut lexer)
        }
        (false, true) => {
            let mut lexer =
                SmtLexer::new_recovering(Scripted::<false>::new(behaviour, out.clone()), version);
            drive(&request, feeds, &out, &mut lexer)
        }
        (true, true) => {
            let mut lexer =
                SmtLexer::new_recovering(Scripted::<true>::new(behaviour, out.clone()), version);
            drive(&request, feeds, &out, &mut lexer)
        }
    };

    let mut response = out.take();
    if complete {
        response.push_str("ok\n");
    }
    Ok(response)
}

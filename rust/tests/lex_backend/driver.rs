//! The lexer driver protocol, answered by the Rust lexer.
//!
//! The protocol is described in `lean/driver-protocol.md`. This module is
//! the reference answer to it: the tests call it in process, and the
//! executable in `tools/rust-lex-driver` prints what it returns.

use std::cell::RefCell;
use std::ops::ControlFlow;
use std::rc::Rc;

use blazing_smtlib::{
    SmtLocation,
    lexer::{SmtLexErrorCause, SmtLexRecovery, SmtLexer},
    token::{
        SmtBatchCursor, SmtConsume, SmtRecover, SmtReserved, SmtSyntaxToken, SmtToken,
        SmtTokenCategory, SmtVersion,
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

/// How the consumer of a request behaves.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Behaviour {
    /// It takes every token and always continues.
    TakeAll,
    /// It answers the hand-overs in order by the replies, and takes every
    /// token once they have run out.
    Plan(Vec<Reply>),
    /// It takes every token and fails by what the tokens are: on the symbol
    /// `bad`, on a closing parenthesis that closes nothing, and on the
    /// end-of-file token inside a parenthesis, or on every end-of-file token
    /// if `refuse_end` is set. The symbol `to-2.0` makes it set the version.
    Rules { refuse_end: bool },
}

/// The consumer of a request: writes what it is called with as response
/// lines. `WHITESPACE` says whether it takes whitespace and comments.
pub struct Scripted<const WHITESPACE: bool> {
    behaviour: Behaviour,
    /// The number of hand-overs answered by the plan.
    handed: usize,
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
    match version {
        SmtVersion::V2_0 => "2.0",
        SmtVersion::V2_5 => "2.5",
        SmtVersion::V2_6 => "2.6",
        SmtVersion::V2_7 => "2.7",
    }
}

fn token_line(token: SmtToken<'_>, version: SmtVersion) -> String {
    let reserved = match SmtSyntaxToken::from_token(token, version) {
        SmtSyntaxToken::Reserved(SmtReserved::General(_)) => "general",
        SmtSyntaxToken::Reserved(SmtReserved::CommandName(_)) => "command",
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
    type Result = ();
    /// The name of what made the consumer fail.
    type Error = &'static str;
    const CONSUMES_WHITESPACE_AND_COMMENTS: bool = WHITESPACE;

    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
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
                        cursor.set_version(version);
                        Ok(ControlFlow::Continue(()))
                    }
                    Reply::SwitchAndFinish(_, version) => {
                        cursor.set_version(version);
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
                            cursor.set_version(SmtVersion::V2_0);
                        }
                        _ => {}
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

/// A request, read from its line.
struct Request {
    version: SmtVersion,
    whitespace: bool,
    recover: bool,
    behaviour: Behaviour,
    feeds: Vec<Feed>,
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
    SmtVersion::from_decimal_opt(word.as_bytes()).ok_or_else(|| format!("unknown version {word:?}"))
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

fn read_request(line: &str) -> Result<Request, String> {
    let mut words = line.split(' ');
    if words.next() != Some("lex") {
        return Err("unknown request".into());
    }
    let mut request = Request {
        version: read_version(words.next().ok_or("no version")?)?,
        whitespace: false,
        recover: false,
        behaviour: Behaviour::TakeAll,
        feeds: Vec::new(),
    };
    for word in words {
        let scripted = request.behaviour != Behaviour::TakeAll;
        // the options come before the feeds
        let option = request.feeds.is_empty();
        match word {
            "e" => request.feeds.push(None),
            "ws" if option => request.whitespace = true,
            "recover" if option => request.recover = true,
            "rules" if option && !scripted => {
                request.behaviour = Behaviour::Rules { refuse_end: false };
            }
            "rules=refuse-end" if option && !scripted => {
                request.behaviour = Behaviour::Rules { refuse_end: true };
            }
            _ => {
                if let Some(replies) = word.strip_prefix("plan=").filter(|_| option && !scripted) {
                    // no replies at all are a plan too: every token is taken,
                    // and the hand-overs are reported
                    let replies: Result<Vec<Reply>, String> = replies
                        .split(',')
                        .filter(|_| !replies.is_empty())
                        .map(read_reply)
                        .collect();
                    request.behaviour = Behaviour::Plan(replies?);
                } else if let Some(digits) = word.strip_prefix('s') {
                    request.feeds.push(Some(unhex(digits)?));
                } else {
                    return Err(format!("unknown operation {word:?}"));
                }
            }
        }
    }
    Ok(request)
}

/// Applies the feeds of the request to the lexer and writes the lines of
/// the feeds themselves. Returns whether every feed was applied.
fn drive<const WHITESPACE: bool, R: SmtLexRecovery<Scripted<WHITESPACE>>>(
    request: &Request,
    out: &RefCell<String>,
    lexer: &mut SmtLexer<Scripted<WHITESPACE>, R>,
) -> bool {
    let scripted = request.behaviour != Behaviour::TakeAll;
    for feed in &request.feeds {
        // the part of a slice that the lexer has not taken yet
        let mut from = 0;
        loop {
            let before = lexer.current_location().offset();
            let result = match feed {
                Some(slice) => lexer.lex_slice(&slice[from..]),
                None => lexer.lex_eof(),
            };
            let err = match result {
                Ok(ControlFlow::Continue(())) => break,
                Ok(ControlFlow::Break(located)) => {
                    out.borrow_mut()
                        .push_str(&format!("fin {}\n", location(located.location())));
                    break;
                }
                Err(err) => err,
            };

            let continues = err.continues_from();
            let mut line = match err.cause() {
                SmtLexErrorCause::Lexical(err) => format!(
                    "err {:?} {} {}",
                    err.kind(),
                    location(err.span().start()),
                    location(err.span().end()),
                ),
                SmtLexErrorCause::Consumer(name) => format!("cerr {name}"),
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

/// Answers one request line with the lines of its response.
pub fn answer(line: &str) -> Result<String, String> {
    // decode the whole request first, so that a malformed one produces no lines
    let request = read_request(line)?;

    // the consumer writes into the response while the lexer owns it
    let out = Rc::new(RefCell::new(String::new()));
    let behaviour = request.behaviour.clone();
    let version = request.version;
    let complete = match (request.whitespace, request.recover) {
        (false, false) => {
            let mut lexer = SmtLexer::new(Scripted::<false>::new(behaviour, out.clone()), version);
            drive(&request, &out, &mut lexer)
        }
        (true, false) => {
            let mut lexer = SmtLexer::new(Scripted::<true>::new(behaviour, out.clone()), version);
            drive(&request, &out, &mut lexer)
        }
        (false, true) => {
            let mut lexer =
                SmtLexer::new_recovering(Scripted::<false>::new(behaviour, out.clone()), version);
            drive(&request, &out, &mut lexer)
        }
        (true, true) => {
            let mut lexer =
                SmtLexer::new_recovering(Scripted::<true>::new(behaviour, out.clone()), version);
            drive(&request, &out, &mut lexer)
        }
    };

    let mut response = out.take();
    if complete {
        response.push_str("ok\n");
    }
    Ok(response)
}

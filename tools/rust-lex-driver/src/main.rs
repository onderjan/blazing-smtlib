//! The lexer driver protocol, answered by the Rust lexer: the reference for
//! the Lean driver of the same protocol (`lean/driver-protocol.md`).
//!
//! Reads one request per line from the standard input and writes the response
//! to the standard output, until the input ends.

use std::cell::RefCell;
use std::convert::Infallible;
use std::io::{BufRead, Write};
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtLocation,
    lexer::{SmtLexError, SmtLexer},
    token::{SmtBatchCursor, SmtConsume, SmtReserved, SmtSyntaxToken, SmtVersion},
};

/// Writes every token handed over as a response line.
struct Report<'a> {
    version: SmtVersion,
    out: &'a RefCell<String>,
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

impl SmtConsume for Report<'_> {
    type Result = ();
    type Error = Infallible;
    const CONSUMES_WHITESPACE_AND_COMMENTS: bool = false;

    fn consume(
        &mut self,
        cursor: &mut SmtBatchCursor<'_>,
    ) -> Result<ControlFlow<Self::Result>, Self::Error> {
        while let Some(token) = cursor.next() {
            let reserved = match SmtSyntaxToken::from_token(token, self.version) {
                SmtSyntaxToken::Reserved(SmtReserved::General(_)) => "general",
                SmtSyntaxToken::Reserved(SmtReserved::CommandName(_)) => "command",
                _ => "-",
            };
            self.out.borrow_mut().push_str(&format!(
                "t {:?} {} {} {} x{}\n",
                token.category(),
                location(token.span().start()),
                location(token.span().end()),
                reserved,
                hex(token.content()),
            ));
        }
        Ok(ControlFlow::Continue(()))
    }
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

/// Answers one request line, appending the response lines to `out`.
fn answer(request: &str, out: &mut String) -> Result<(), String> {
    let mut words = request.split(' ');
    if words.next() != Some("lex") {
        return Err("unknown request".into());
    }
    let version = words
        .next()
        .and_then(|version| SmtVersion::from_decimal_opt(version.as_bytes()))
        .ok_or("unknown version")?;

    // decode every operation first, so that a malformed request produces
    // no token lines
    let mut operations = Vec::new();
    for word in words {
        operations.push(match word.strip_prefix('s') {
            Some(digits) => Some(unhex(digits)?),
            None if word == "e" => None,
            None => return Err(format!("unknown operation {word:?}")),
        });
    }

    let lines = RefCell::new(String::new());
    let mut lexer = SmtLexer::new(
        Report {
            version,
            out: &lines,
        },
        version,
    );
    let mut error = None;
    for operation in &operations {
        let result = match operation {
            Some(slice) => lexer.lex_slice(slice),
            None => lexer.lex_eof(),
        };
        match result {
            // the location the lexer is at after the operation
            Ok(_) => lines
                .borrow_mut()
                .push_str(&format!("at {}\n", location(lexer.current_location()))),
            Err(SmtLexError::Lexical(err)) => {
                error = Some(err);
                break;
            }
            Err(SmtLexError::Consumer(never)) => match never {},
        }
    }
    drop(lexer);

    out.push_str(&lines.into_inner());
    match error {
        None => out.push_str("ok\n"),
        Some(err) => out.push_str(&format!(
            "err {:?} {} {}\n",
            err.kind(),
            location(err.span().start()),
            location(err.span().end()),
        )),
    }
    Ok(())
}

fn main() {
    let stdin = std::io::stdin();
    let mut stdout = std::io::stdout().lock();
    for line in stdin.lock().lines() {
        let line = line.expect("the requests must be readable");
        let mut out = String::new();
        if let Err(message) = answer(&line, &mut out) {
            out = format!("fail {message}\n");
        }
        stdout
            .write_all(out.as_bytes())
            .and_then(|()| stdout.flush())
            .expect("the response must be writable");
    }
}

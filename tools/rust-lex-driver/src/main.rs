//! The lexer driver protocol, answered by the Rust lexer: the reference for
//! the Lean driver of the same protocol (`lean/driver-protocol.md`).
//!
//! Reads one request per line from the standard input and writes the response
//! to the standard output, until the input ends. The answers themselves come
//! from the module the Rust tests use in process.

use std::io::{BufRead, Write};

#[path = "../../../rust/tests/lex_backend/driver.rs"]
mod driver;

fn main() {
    let stdin = std::io::stdin();
    let mut stdout = std::io::stdout().lock();
    for line in stdin.lock().lines() {
        let line = line.expect("the requests must be readable");
        let out = match driver::answer(&line) {
            Ok(response) => response,
            Err(message) => format!("fail {message}\n"),
        };
        stdout
            .write_all(out.as_bytes())
            .and_then(|()| stdout.flush())
            .expect("the response must be writable");
    }
}

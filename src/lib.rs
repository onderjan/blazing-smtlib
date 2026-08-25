#![forbid(unsafe_code)]
use std::{
    fs::File,
    io::{BufReader, Read},
    path::Path,
};

mod plain;
mod string;

mod lexer;
mod token;

mod api;
mod parser;

pub use crate::api::*;
pub use crate::plain::*;
pub use crate::string::*;

use crate::{
    lexer::{Lexer, LexerError},
    parser::{Parser, ParserError, ParserOrHandlerError},
};

pub enum SmtProcessError<H: SmtHandler> {
    ReadError(std::io::Error),
    LexerError(LexerError),
    ParserError(ParserError),
    HandlerError(H::Error),
}

pub fn process_smt_file<H: CommandHandler>(
    handler: &mut H,
    path: &Path,
) -> Result<(), SmtProcessError<H>> {
    let file = File::open(path).map_err(SmtProcessError::ReadError)?;
    let reader = BufReader::new(file);
    process_smt_reader(handler, reader)
}

pub fn process_smt_reader<H: CommandHandler>(
    handler: &mut H,
    mut reader: impl Read,
) -> Result<(), SmtProcessError<H>> {
    let mut lexer = Lexer::new();
    let mut parser = Parser::new(handler);

    let mut parse_tokens = |tokens| -> Result<(), SmtProcessError<H>> {
        for token in tokens {
            match parser.parse_token(token) {
                Ok(()) => {}
                Err(ParserOrHandlerError::ParserError(err)) => {
                    return Err(SmtProcessError::ParserError(err));
                }
                Err(ParserOrHandlerError::HandlerError(err)) => {
                    return Err(SmtProcessError::HandlerError(err));
                }
            }
        }
        Ok(())
    };

    loop {
        let mut c = 0;
        match reader.read(std::slice::from_mut(&mut c)) {
            Ok(num_bytes) => {
                if num_bytes == 0 {
                    break;
                }
                assert_eq!(num_bytes, 1);
                match lexer.lex_next(c) {
                    Ok(tokens) => parse_tokens(tokens)?,
                    Err(err) => {
                        return Err(SmtProcessError::LexerError(err));
                    }
                }
            }
            Err(err) => {
                return Err(SmtProcessError::ReadError(err));
            }
        }
    }

    match lexer.lex_eof() {
        Ok(tokens) => parse_tokens(tokens),
        Err(err) => Err(SmtProcessError::LexerError(err)),
    }
}

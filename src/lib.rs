use std::{
    fmt::Debug,
    fs::File,
    io::{BufReader, Read},
    path::Path,
};

mod lexer;
mod string;
mod token;

mod api;
mod parser;

pub mod old;
pub use crate::string::*;

use crate::lexer::{Lexer, LexerError};

pub enum SmtProcessErrorOld<F: Debug> {
    LexerError(LexerError),
    ParserError(old::ParserError<F>),
    ReadError(std::io::Error),
}

pub fn process_smt_file_old<F: old::SmtFold>(
    folder: F,
    path: &Path,
) -> Result<F, SmtProcessErrorOld<<F as old::SmtFold>::Error>> {
    let file = File::open(path).map_err(SmtProcessErrorOld::ReadError)?;
    let reader = BufReader::new(file);
    process_smt_reader_old(folder, reader)
}

pub fn process_smt_reader_old<F: old::SmtFold>(
    folder: F,
    mut reader: impl Read,
) -> Result<F, SmtProcessErrorOld<<F as old::SmtFold>::Error>> {
    let mut lexer = Lexer::new();
    let mut parser = old::Parser::new(folder);

    loop {
        let mut c = 0;
        match reader.read(std::slice::from_mut(&mut c)) {
            Ok(num_bytes) => {
                if num_bytes == 0 {
                    break;
                }
                assert_eq!(num_bytes, 1);
                match lexer.lex_next(c) {
                    Ok(tokens) => {
                        for token in tokens {
                            match parser.parse_token(token) {
                                Ok(()) => {}
                                Err(err) => return Err(SmtProcessErrorOld::ParserError(err)),
                            }
                        }
                    }
                    Err(err) => {
                        return Err(SmtProcessErrorOld::LexerError(err));
                    }
                }
            }
            Err(err) => {
                return Err(SmtProcessErrorOld::ReadError(err));
            }
        }
    }
    if let Err(err) = lexer.lex_eof() {
        return Err(SmtProcessErrorOld::LexerError(err));
    }

    Ok(parser.into_folder())
}

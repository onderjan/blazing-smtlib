use std::{
    fmt::Debug,
    fs::File,
    io::{BufReader, Read},
    path::Path,
};

mod folders;
mod parser;
mod smt;

pub use folders::*;
pub use parser::*;
pub use smt::*;

use crate::parser::lexer::{Lexer, LexerError};

pub enum SmtProcessError<F: Debug> {
    LexerError(LexerError),
    ParserError(ParserError<F>),
    ReadError(std::io::Error),
}

pub fn process_smt_file<F: SmtFold>(
    folder: F,
    path: &Path,
) -> Result<F, SmtProcessError<<F as SmtFold>::Error>> {
    let file = File::open(path).map_err(SmtProcessError::ReadError)?;
    let reader = BufReader::new(file);
    process_smt_reader(folder, reader)
}

pub fn process_smt_reader<F: SmtFold>(
    folder: F,
    mut reader: impl Read,
) -> Result<F, SmtProcessError<<F as SmtFold>::Error>> {
    let mut lexer = Lexer::new();
    let mut parser = Parser::new(folder);

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
                                Err(err) => return Err(SmtProcessError::ParserError(err)),
                            }
                        }
                    }
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
    if let Err(err) = lexer.lex_eof() {
        return Err(SmtProcessError::LexerError(err));
    }

    Ok(parser.into_folder())
}

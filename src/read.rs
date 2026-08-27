use std::{
    fs::File,
    io::{BufReader, Read},
    path::Path,
};

use crate::{
    CommandHandler, SmtHandler,
    read::{
        lexer::{Lexer, LexerError},
        parser::{Parser, ParserError, ParserOrHandlerError},
    },
};

pub mod lexer;
pub mod parser;

pub enum SmtReadError<H: SmtHandler> {
    ReadError(std::io::Error),
    LexerError(LexerError),
    ParserError(ParserError),
    HandlerError(H::Error),
}

pub fn read_smt_file<H: CommandHandler>(
    handler: &mut H,
    path: &Path,
) -> Result<(), SmtReadError<H>> {
    let file = File::open(path).map_err(SmtReadError::ReadError)?;
    let reader = BufReader::new(file);
    read_smt(handler, reader)
}

pub fn read_smt<H: CommandHandler>(
    handler: &mut H,
    mut reader: impl Read,
) -> Result<(), SmtReadError<H>> {
    let mut lexer = Lexer::new();
    let mut parser = Parser::new(handler);

    let mut parse_tokens = |tokens| -> Result<(), SmtReadError<H>> {
        for token in tokens {
            match parser.parse_token(token) {
                Ok(()) => {}
                Err(ParserOrHandlerError::ParserError(err)) => {
                    return Err(SmtReadError::ParserError(err));
                }
                Err(ParserOrHandlerError::HandlerError(err)) => {
                    return Err(SmtReadError::HandlerError(err));
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
                        return Err(SmtReadError::LexerError(err));
                    }
                }
            }
            Err(err) => {
                return Err(SmtReadError::ReadError(err));
            }
        }
    }

    match lexer.lex_eof() {
        Ok(tokens) => parse_tokens(tokens),
        Err(err) => Err(SmtReadError::LexerError(err)),
    }
}

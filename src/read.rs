use std::{
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
};

use crate::{
    CommandHandler, SmtSpan,
    read::{
        lexer::{LexError, Lexer, LexerError, LexerErrorKind},
        parser::{CategoryErrorKind, Parser, ParserError, ParserErrorKind},
    },
};

pub mod lexer;
pub mod parser;

#[derive(Debug)]
pub enum SmtReadErrorKind<E> {
    /// The error occurred when reading.
    Io(std::io::Error),
    /// The error occurred when lexing.
    Lexer(LexerErrorKind),
    /// The error occurred when parsing.
    Parser(CategoryErrorKind),
    /// The error occurred in the user handler.
    Handler(E),
}

#[derive(Debug)]
pub struct SmtReadError<E> {
    kind: SmtReadErrorKind<E>,
    span: SmtSpan,
}

impl<E> SmtReadError<E> {
    pub(crate) fn new(kind: SmtReadErrorKind<E>, span: SmtSpan) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &SmtReadErrorKind<E> {
        &self.kind
    }

    /// Span where the error occurred.
    ///
    /// For I/O errors, the returned span is empty,
    /// indicating the position where the reading failed.
    pub fn span(&self) -> SmtSpan {
        self.span
    }

    pub fn into_kind(self) -> SmtReadErrorKind<E> {
        self.kind
    }
}

impl<E> From<LexError<ParserError<E>>> for SmtReadError<E> {
    fn from(err: LexError<ParserError<E>>) -> Self {
        match err {
            LexError::Lexer(err) => err.into(),
            LexError::Handler(err) => err.into(),
        }
    }
}

impl<E> From<LexerError> for SmtReadError<E> {
    fn from(err: LexerError) -> Self {
        let span = err.span();
        SmtReadError::new(SmtReadErrorKind::Lexer(err.into_kind()), span)
    }
}

impl<E> From<ParserError<E>> for SmtReadError<E> {
    fn from(err: ParserError<E>) -> Self {
        let span = err.span();
        let kind = match err.into_kind() {
            ParserErrorKind::Category(err) => SmtReadErrorKind::Parser(err),
            ParserErrorKind::Handler(err) => SmtReadErrorKind::Handler(err),
        };
        SmtReadError::new(kind, span)
    }
}

/// Reads an SMT-LIB file from a given path, processing commands with `handler`.
///
/// This is a simple convenience function for handlers where resources have
/// a default constructor and it does not matter that the allocated parser structures
/// are dropped and cannot be reused afterwards for increased performance.
///
/// Use `SmtReader` directly if more control is needed.
pub fn read_smt_file<H: CommandHandler<Resources: Default>>(
    handler: &mut H,
    path: &Path,
) -> Result<(), SmtReadError<H::Error>> {
    SmtReader::new(handler, &mut Default::default()).read_file(path)
}

/// Reads a buffered reader containing an SMT-LIB file fully, processing commands with `handler`.
///
/// This is a simple convenience function for handlers that do not keep any custom resources
/// when it does not matter that the allocated parser structures are dropped
/// and cannot be reused afterwards for increased performance.
///
/// Use `SmtReader` directly if more control is needed.
pub fn read_smt<H: CommandHandler<Resources: Default>>(
    handler: &mut H,
    buf_reader: impl BufRead,
) -> Result<(), SmtReadError<H::Error>> {
    SmtReader::new(handler, &mut Default::default()).read_all(buf_reader)
}

/// SMT-LIB reader that processes bytestream data and streams the processed content to `CommandHandler`.
///
/// For simple usage scenarios, consider using `read_smt_file` or `read_smt`.
struct SmtReader<'a, H: CommandHandler> {
    lexer: Lexer<Parser<'a, H>>,
}

impl<'a, H: CommandHandler> SmtReader<'a, H> {
    fn new(handler: &'a mut H, resources: &'a mut H::Resources) -> Self {
        let parser = Parser::new(handler, resources);
        let lexer = Lexer::new(parser);
        Self { lexer }
    }

    /// Opens and reads a file, treating the ending zero-byte read as End of File.
    pub fn read_file(&mut self, path: &Path) -> Result<(), SmtReadError<H::Error>> {
        let file = File::open(path)
            .map_err(|err| SmtReadError::new(SmtReadErrorKind::Io(err), SmtSpan::new_zero()))?;
        let buf_reader = BufReader::new(file);
        self.read_all(buf_reader)
    }

    /// Reads a buffered reader fully, treating the ending zero-byte read as End of File.
    pub fn read_all<R: BufRead>(
        &mut self,
        mut buf_reader: R,
    ) -> Result<(), SmtReadError<H::Error>> {
        loop {
            match buf_reader.fill_buf() {
                Ok(buffer) => {
                    if !buffer.is_empty() {
                        // process the buffer and mark it consumed
                        let num_consumed = buffer.len();
                        self.read_buf(buffer)?;
                        buf_reader.consume(num_consumed)
                    } else {
                        // end of stream, process End of File and return
                        return self.read_eof();
                    }
                }
                Err(err) => {
                    // return an empty span on the current lexer location
                    let location = self.lexer.current_location();
                    let span = SmtSpan::new_empty(location);
                    let kind = SmtReadErrorKind::Io(err);
                    return Err(SmtReadError::new(kind, span));
                }
            }
        }
    }

    /// Processes a single buffer.
    ///
    /// This function never triggers processing of the End of File condition.
    /// Call `SmtReader::read_eof()` to process the End of File when appropriate.
    pub fn read_buf(&mut self, buffer: &[u8]) -> Result<(), SmtReadError<H::Error>> {
        // parsing goes through lexing, so just call the lexer
        Ok(self.lexer.lex_slice(buffer)?)
    }

    /// Processes an End of File condition.
    ///
    /// If using `SmtReader::read_buf` to read, this must be called
    /// after the logical SMT-LIB command file ends to prevent
    /// leaving the ending unprocessed.
    fn read_eof(&mut self) -> Result<(), SmtReadError<H::Error>> {
        Ok(self.lexer.lex_eof()?)
    }
}

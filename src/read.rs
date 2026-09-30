//! Reading SMT-LIB input: lexing and parsing.
//!
//! Reading turns bytes into tokens (the [`lexer`] module) and tokens into
//! the syntactic categories and commands of SMT-LIB (the [`parser`] module),
//! which are delivered to a [`CommandHandler`] in streaming fashion:
//! the input is processed piece by piece and every category or command
//! to be handled reaches the handler before the next one is read.
//!
//! For simple usage, use [`read_smt`] and [`read_smt_file`].
//!
//! [`SmtReader`] reads the same way from any sequence of buffers and keeps
//! the parser's resources under the caller's control, so it is the entry
//! point when the input does not arrive as one buffered reader or when the
//! resources should serve several reads. The [`lexer`] and [`parser`]
//! modules can also be used on their own.

use std::{
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
};

use crate::{
    CommandHandler, SmtSpan,
    read::{
        lexer::{LexError, Lexer, LexerError, LexerErrorKind},
        parser::{CategoryErrorKind, ParserError, ParserErrorKind, ScriptParser},
    },
};

pub mod lexer;
pub mod parser;

/// Determines why reading has failed.
#[derive(Debug)]
pub enum SmtReadErrorKind<E> {
    /// Reading from a file or a buffered reader failed.
    Io(std::io::Error),
    /// The input is not a valid sequence of SMT-LIB tokens.
    Lexer(LexerErrorKind),
    /// The tokens do not form valid SMT-LIB syntactic categories or commands.
    ///
    /// Commands with non-standard names are routed to the handler for
    /// processing, so they are rejected with a [`SmtReadErrorKind::Handler`]
    /// error kind instead.
    Parser(CategoryErrorKind),
    /// The handler rejected a command or a syntactic category.
    Handler(E),
}

/// An error that ended reading, including its span.
#[derive(Debug)]
pub struct SmtReadError<E> {
    kind: SmtReadErrorKind<E>,
    span: SmtSpan,
}

impl<E> SmtReadError<E> {
    pub(crate) fn new(kind: SmtReadErrorKind<E>, span: SmtSpan) -> Self {
        Self { kind, span }
    }

    /// Determines why reading has failed.
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

    /// Convert into the enumeration that determines why reading has failed.
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

/// Reads the SMT-LIB file at `path`, delivering its content to `handler`.
///
/// This is a convenience function over [`SmtReader`]: the parser
/// is dropped after reading, so its resources cannot be preserved
/// for future use. Use [`SmtReader`] directly to keep the
/// resources across reads or to feed the input in pieces.
///
/// A failure to open the file is reported as an I/O error with an empty
/// span at the start of the input.
pub fn read_smt_file<H: CommandHandler>(
    handler: &mut H,
    path: &Path,
) -> Result<(), SmtReadError<H::Error>> {
    SmtReader::new(handler).read_file(path)
}

/// Reads SMT-LIB input from `buf_reader` to its end, delivering its content
/// to `handler`.
///
/// The input is considered to end when the buffered reader returns
/// a zero-length buffer.
///
/// This is a convenience function over [`SmtReader`]: the parser
/// is dropped after reading, so its resources cannot be preserved
/// for future use. Use [`SmtReader`] directly to keep the
/// resources across reads or to feed the input in pieces.
pub fn read_smt<H: CommandHandler>(
    handler: &mut H,
    buf_reader: impl BufRead,
) -> Result<(), SmtReadError<H::Error>> {
    SmtReader::new(handler).read_all(buf_reader)
}

/// Streams SMT-LIB input from bytes to a [`CommandHandler`].
///
/// A reader owns its lexer and parser and borrows the handler and its resources.
///
/// The input is read either whole, through [`read_file`](Self::read_file)
/// or [`read_all`](Self::read_all), or in pieces, using
/// [`read_slice`](Self::read_slice) sequentially, followed by [`read_eof`](Self::read_eof)
/// once the input has ended. A piece may end anywhere, even inside a token.
///
/// For whole inputs, consider [`read_smt_file`] and [`read_smt`].
pub struct SmtReader<'a, H: CommandHandler> {
    lexer: Lexer<ScriptParser<'a, H>>,
}

impl<'a, H: CommandHandler> SmtReader<'a, H> {
    /// Creates a reader that calls `handler` sequentially when reading.
    pub fn new(handler: &'a mut H) -> Self {
        let parser = ScriptParser::new(handler);
        let lexer = Lexer::new(parser);
        Self { lexer }
    }

    /// Opens the file at `path` and reads it to its end, including the end
    /// of the input.
    ///
    /// A failure to open the file is reported as an I/O error with an empty
    /// span at the start of the input. An I/O read error is reported as
    /// an empty span at the respective position.
    ///
    /// Panics if a previous call on this reader returned an error.
    pub fn read_file(&mut self, path: &Path) -> Result<(), SmtReadError<H::Error>> {
        let file = File::open(path)
            .map_err(|err| SmtReadError::new(SmtReadErrorKind::Io(err), SmtSpan::new_zero()))?;

        // make the bufreader use 1 MiB buffer so that we can
        // lex/parse more efficiently with larger batches
        const BUF_READER_CAPACITY: usize = 1024 * 1024;
        let buf_reader = BufReader::with_capacity(BUF_READER_CAPACITY, file);
        self.read_all(buf_reader)
    }

    /// Reads `buf_reader` to its end, including the end of the input.
    ///
    /// The input is considered to end when the buffered reader returns
    /// a zero-length buffer. A failure while reading is reported as
    /// an I/O error with an empty span at the position reached.
    ///
    /// Panics if a previous call on this reader returned an error.
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
                        self.read_slice(buffer)?;
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

    /// Processes a byte slice as one piece of the input.
    ///
    /// The piece may end anywhere, even inside a token: whatever is
    /// unfinished carries over to the next call.
    ///
    /// After processing the whole input using this function,
    /// call [`read_eof`](Self::read_eof) so the whole input
    /// is fully processed.
    ///
    /// Panics if a previous call on this reader returned an error.
    pub fn read_slice(&mut self, slice: &[u8]) -> Result<(), SmtReadError<H::Error>> {
        // parsing goes through lexing, so just call the lexer
        Ok(self.lexer.lex_slice(slice)?)
    }

    /// Processes the end of the input.
    ///
    /// Call this once after the last [`read_slice`](Self::read_slice);
    /// [`read_file`](Self::read_file) and [`read_all`](Self::read_all) call
    /// it themselves.
    ///
    /// Panics if a previous call on this reader returned an error.
    pub fn read_eof(&mut self) -> Result<(), SmtReadError<H::Error>> {
        Ok(self.lexer.lex_eof()?)
    }
}

//! Reading SMT-LIB input: lexing and parsing.
//!
//! Reading turns bytes into tokens (the [`lexer`](crate::lexer) module) and tokens into
//! the syntactic categories and commands of SMT-LIB (the [`parser`](crate::parser) module),
//! which are delivered to a [`SmtCommandHandler`] in streaming fashion:
//! the input is processed piece by piece and every category or command
//! to be handled reaches the handler before the next one is read.
//!
//! For simple usage, use [`read_smt`] and [`read_smt_file`].
//!
//! [`SmtReader`] reads the same way from any sequence of buffers and keeps
//! the parser's resources under the caller's control, so it is the entry
//! point when the input does not arrive as one buffered reader or when the
//! resources should serve several reads. The [`lexer`](crate::lexer) and [`parser`](crate::parser)
//! modules can also be used on their own.

use std::{
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
};

use crate::token::{SmtVersion, SmtVersionPosture};
use crate::{
    SmtCommandHandler, SmtHandler, SmtLocated, SmtSpan,
    lexer::{SmtLexError, SmtLexErrorCause, SmtLexer, SmtLexicalErrorKind},
    parser::{
        SmtParse, SmtParseAdapter, SmtParseError, SmtParseErrorCause, SmtScriptParser,
        SmtSyntaxErrorKind,
    },
};

/// Determines why reading has failed.
#[derive(Debug)]
pub enum SmtReadErrorCause<E> {
    /// Reading from a file or a buffered reader failed.
    Io(std::io::Error),
    /// The input is not a valid sequence of SMT-LIB tokens.
    Lexical(SmtLexicalErrorKind),
    /// The tokens do not form valid SMT-LIB syntactic categories or commands.
    ///
    /// Commands with non-standard names are routed to the handler for
    /// processing, so they are rejected with a [`SmtReadErrorCause::Handler`]
    /// error cause instead.
    Syntax(SmtSyntaxErrorKind),
    /// The handler rejected a command or a syntactic category.
    Handler(E),
}

/// An error that ended reading, including its span.
#[derive(Debug)]
pub struct SmtReadError<E> {
    cause: SmtReadErrorCause<E>,
    span: SmtSpan,
}

impl<E> SmtReadError<E> {
    pub(crate) fn new(cause: SmtReadErrorCause<E>, span: SmtSpan) -> Self {
        Self { cause, span }
    }

    /// Determines why reading has failed.
    pub fn cause(&self) -> &SmtReadErrorCause<E> {
        &self.cause
    }

    /// Span where the error occurred.
    ///
    /// For I/O errors, the returned span is empty,
    /// indicating the position where the reading failed.
    pub fn span(&self) -> SmtSpan {
        self.span
    }

    /// Convert into the enumeration that determines why reading has failed.
    pub fn into_cause(self) -> SmtReadErrorCause<E> {
        self.cause
    }

    fn from_parse(err: SmtParseError<E>, span: SmtSpan) -> Self {
        let cause = match err.into_cause() {
            SmtParseErrorCause::Syntax(err) => SmtReadErrorCause::Syntax(err),
            SmtParseErrorCause::Handler(err) => SmtReadErrorCause::Handler(err),
        };
        SmtReadError::new(cause, span)
    }
}

impl<E> From<SmtLexError<SmtParseError<E>>> for SmtReadError<E> {
    fn from(err: SmtLexError<SmtParseError<E>>) -> Self {
        let span = err.span();
        match err.into_cause() {
            SmtLexErrorCause::Lexical(err) => Self::new(SmtReadErrorCause::Lexical(err), span),
            SmtLexErrorCause::Consumer(err) => Self::from_parse(err, span),
        }
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
pub fn read_smt_file<H: SmtCommandHandler>(
    handler: &mut H,
    path: &Path,
) -> Result<(), SmtReadError<H::Error>> {
    SmtReader::script(handler, SmtVersion::default(), SmtVersionPosture::default())
        .read_file(path)
        .map(|_| ())
}

/// Reads SMT-LIB input from `buf_reader`, delivering its content
/// to `handler`.
///
/// The input is considered to end when the buffered reader returns
/// a zero-length buffer.
///
/// No guarantees are made on how the buffered reader is read,
/// including how many bytes are read.
///
/// This is a convenience function over [`SmtReader`]: the parser
/// is dropped after reading, so its resources cannot be preserved
/// for future use. Use [`SmtReader`] directly to keep the
/// resources across reads or to feed the input in pieces.
pub fn read_smt<H: SmtCommandHandler>(
    handler: &mut H,
    buf_reader: impl BufRead,
) -> Result<(), SmtReadError<H::Error>> {
    SmtReader::script(handler, SmtVersion::default(), SmtVersionPosture::default())
        .read_all(buf_reader)
        .map(|_| ())
}

/// Streams SMT-LIB input from bytes to a [`SmtCommandHandler`].
///
/// A reader owns its lexer, its parser, and the parser resources, and borrows
/// the handler. By default it parses a script with a [`SmtScriptParser`]; a reader
/// created with [`with_parser`](Self::with_parser) adapts another top-level
/// parser, for other SMT-LIB input such as solver responses.
///
/// The input is read either whole, through [`read_file`](Self::read_file)
/// or [`read_all`](Self::read_all), or in pieces, using
/// [`read_slice`](Self::read_slice) sequentially, followed by [`read_eof`](Self::read_eof)
/// once the input has ended. A piece may end anywhere, even inside a token.
///
/// After a call of [`read_all`](Self::read_all) or [`read_eof`](Self::read_eof)
/// that does not return an error, the reader is reset and can be reused.
///
/// For whole inputs, consider [`read_smt_file`] and [`read_smt`].
pub struct SmtReader<'a, H: SmtHandler + ?Sized, P: SmtParse<H> = SmtScriptParser<H>> {
    lexer: SmtLexer<SmtParseAdapter<'a, H, P>>,
}

impl<'a, H: SmtCommandHandler> SmtReader<'a, H> {
    /// Creates a reader of an SMT-LIB script, whose commands are delivered to `handler`.
    pub fn script(
        handler: &'a mut H,
        initial_version: SmtVersion,
        posture: SmtVersionPosture,
    ) -> Self {
        Self::with_parser(handler, SmtScriptParser::new(posture), initial_version)
    }
}

impl<'a, H: SmtHandler + ?Sized, P: SmtParse<H>> SmtReader<'a, H, P> {
    /// Creates a reader of the input `parser` accepts, over `handler`.
    pub fn with_parser(handler: &'a mut H, parser: P, initial_version: SmtVersion) -> Self {
        let lexer = SmtLexer::new(SmtParseAdapter::new(handler, parser), initial_version);
        Self { lexer }
    }

    /// The SMT-LIB version currently in force.
    ///
    /// The version can change if the token consumer asks for it from the
    /// cursor. The end of the input resets the version to the initial one.
    pub fn version(&self) -> SmtVersion {
        self.lexer.version()
    }

    /// Opens the file at `path` and reads it.
    ///
    /// Returns the parser result if successful.
    ///
    /// A failure to open the file is reported as an I/O error with an empty
    /// span at the start of the input. An I/O read error is reported as
    /// an empty span at the respective position.
    ///
    /// May panic if a previous call on this reader returned an error
    /// or if the parser breaks its contract.
    pub fn read_file(&mut self, path: &Path) -> Result<P::Result, SmtReadError<H::Error>> {
        let file = File::open(path)
            .map_err(|err| SmtReadError::new(SmtReadErrorCause::Io(err), SmtSpan::new_zero()))?;

        // make the bufreader use 1 MiB buffer so that we can
        // lex/parse more efficiently with larger batches
        const BUF_READER_CAPACITY: usize = 1024 * 1024;
        let buf_reader = BufReader::with_capacity(BUF_READER_CAPACITY, file);
        self.read_all(buf_reader)
    }

    /// Reads the content of the buffered reader.
    ///
    /// Returns the parser result if successful.
    ///
    /// The input is considered to end when the buffered reader returns
    /// a zero-length buffer. A failure while reading is reported as
    /// an I/O error with an empty span at the position reached.
    ///
    /// No guarantees are made on how the buffered reader is read,
    /// including how many bytes are read.
    ///
    /// May panic if a previous call on this reader returned an error
    /// or if the parser breaks its contract.
    pub fn read_all<R: BufRead>(
        &mut self,
        mut buf_reader: R,
    ) -> Result<P::Result, SmtReadError<H::Error>> {
        loop {
            if self.lexer.discarded_from().is_some() {
                // the lexer does not care about any subsequent bytes, break
                // this will make the EOF location unreliable
                break;
            }

            let buffer = match buf_reader.fill_buf() {
                Ok(buffer) => buffer,
                Err(err) => {
                    // I/O error
                    // return an empty span on the current lexer location
                    let location = self.lexer.current_location();
                    let span = SmtSpan::new_empty(location);
                    let cause = SmtReadErrorCause::Io(err);
                    return Err(SmtReadError::new(cause, span));
                }
            };

            if buffer.is_empty() {
                // end of file reached
                break;
            }

            // process the buffer
            self.read_slice(buffer)?;

            // all bytes were read, consume them
            let len = buffer.len();
            buf_reader.consume(len);
        }

        // end of stream, process EOF
        // this will reset the lexer and return the break value
        let result = self.read_eof()?;

        // the result location is unreliable due to our choice where to discard
        // do not return the result location
        Ok(result.into_value())
    }

    /// Processes a byte slice as one piece of the input.
    ///
    /// The piece may end anywhere, even inside a token: whatever is
    /// unfinished carries over to the next call.
    ///
    /// May panic if a previous call on this reader returned an error
    /// or if the parser breaks its contract.
    pub fn read_slice(&mut self, slice: &[u8]) -> Result<(), SmtReadError<H::Error>> {
        // parsing goes through lexing, so just call the lexer
        self.lexer.lex_slice(slice).map_err(|err| err.into())
    }

    /// Processes the end of the input.
    ///
    /// Returns the located parser result if successful.
    ///
    /// Call this once after the last [`read_slice`](Self::read_slice);
    /// [`read_file`](Self::read_file) and [`read_all`](Self::read_all) call
    /// it themselves.
    ///
    /// May panic if a previous call on this reader returned an error
    /// or if the parser breaks its contract.
    pub fn read_eof(&mut self) -> Result<SmtLocated<P::Result>, SmtReadError<H::Error>> {
        // parsing goes through lexing, so just call the lexer
        self.lexer.lex_eof().map_err(|err| err.into())
    }
}

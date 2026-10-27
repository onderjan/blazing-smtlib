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
    error::Error,
    fmt,
    fs::File,
    io::{BufRead, BufReader},
    path::Path,
};

use crate::{
    SmtCommandHandler, SmtHandler,
    lexer::{SmtLexer, SmtLexerError, SmtLexerErrorKind, SmtLexicalErrorKind},
    parser::{
        SmtParse, SmtParseAdapter, SmtParseError, SmtParseErrorKind, SmtScriptParser,
        SmtSyntaxErrorKind, SmtVersionErrorKind,
    },
    span::{SmtLocated, SmtSpan},
};
use crate::{SmtVersion, SmtVersionPosture, span::SmtLocation};

/// Why reading has failed (I/O, lexical, syntax, version, or handler error).
#[derive(Debug)]
pub enum SmtReadErrorKind<E> {
    /// Reading from a file or a buffered reader failed.
    Io(std::io::Error),
    /// The input is not a valid sequence of SMT-LIB tokens.
    Lexical(SmtLexicalErrorKind),
    /// The tokens do not form valid SMT-LIB syntactic categories or commands.
    ///
    /// Commands with non-standard names are routed to the handler for
    /// processing, so they are rejected with a [`SmtReadErrorKind::Handler`]
    /// error cause instead.
    Syntax(SmtSyntaxErrorKind),
    /// The script declares a version that cannot be used.
    Version(SmtVersionErrorKind),
    /// The handler rejected a command or a syntactic category.
    Handler(E),
}

/// Error that forced reading to stop.
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

    /// The most useful location for deciphering the error.
    ///
    /// Guaranteed to be within the span.
    pub fn location(&self) -> SmtLocation {
        match &self.kind {
            SmtReadErrorKind::Lexical(kind) => kind.location_in(self.span),
            _ => self.span.start(),
        }
    }

    /// Convert into the enumeration that determines why reading has failed.
    pub fn into_kind(self) -> SmtReadErrorKind<E> {
        self.kind
    }

    fn from_parse(err: SmtParseError<E>, span: SmtSpan) -> Self {
        let kind = match err.into_kind() {
            SmtParseErrorKind::Syntax(err) => SmtReadErrorKind::Syntax(err),
            SmtParseErrorKind::Version(err) => SmtReadErrorKind::Version(err),
            SmtParseErrorKind::Handler(err) => SmtReadErrorKind::Handler(err),
        };
        SmtReadError::new(kind, span)
    }
}

impl<E: fmt::Display> fmt::Display for SmtReadErrorKind<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(err) => write!(f, "I/O: {err}"),
            Self::Lexical(kind) => kind.fmt(f),
            Self::Syntax(kind) => kind.fmt(f),
            Self::Version(kind) => kind.fmt(f),
            Self::Handler(err) => err.fmt(f),
        }
    }
}

impl<E: fmt::Display> fmt::Display for SmtReadError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let location = self.location();
        write!(
            f,
            "{} at line {}, column {}",
            self.kind,
            location.line() + 1,
            location.column() + 1
        )
    }
}

impl<E: Error + 'static> Error for SmtReadError<E> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match &self.kind {
            SmtReadErrorKind::Io(err) => err.source(),
            SmtReadErrorKind::Handler(err) => err.source(),
            SmtReadErrorKind::Lexical(_)
            | SmtReadErrorKind::Syntax(_)
            | SmtReadErrorKind::Version(_) => None,
        }
    }
}

impl<E> From<SmtLexerError<SmtParseError<E>>> for SmtReadError<E> {
    fn from(err: SmtLexerError<SmtParseError<E>>) -> Self {
        let span = err.span();
        match err.into_kind() {
            SmtLexerErrorKind::Lexical(err) => Self::new(SmtReadErrorKind::Lexical(err), span),
            SmtLexerErrorKind::Consumer(err) => Self::from_parse(err, span),
        }
    }
}

/// Reads an SMT-LIB script from a file, delivering it to a handler.
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
    path: impl AsRef<Path>,
) -> Result<(), SmtReadError<H::Error>> {
    SmtReader::script(handler, SmtVersionPosture::default(), SmtVersion::default())
        .read_file(path)
        .map(|_| ())
}

/// Reads an SMT-LIB script from a buffered reader, delivering it to a handler.
///
/// The input is considered to end when the buffered reader returns
/// a zero-length buffer.
///
/// The buffer content is consumed up to where the parser requests
/// discarding the rest or fully if no such request was made.
///
/// This is a convenience function over [`SmtReader`]: the parser
/// is dropped after reading, so its resources cannot be preserved
/// for future use. Use [`SmtReader`] directly to keep the
/// resources across reads or to feed the input in pieces.
pub fn read_smt<H: SmtCommandHandler>(
    handler: &mut H,
    buf_reader: impl BufRead,
) -> Result<(), SmtReadError<H::Error>> {
    SmtReader::script(handler, SmtVersionPosture::default(), SmtVersion::default())
        .read_from(buf_reader)
        .map(|_| ())
}

/// Reads SMT-LIB input, delivering it to a handler.
///
/// A reader owns its lexer, its parser, and the parser resources, and borrows
/// the handler. Any parser can be used, and a convenience method
/// [`Self::script`] is provided for the common case of reading SMT-LIB scripts.
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

impl<H: SmtHandler + ?Sized, P: SmtParse<H>> fmt::Debug for SmtReader<'_, H, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SmtReader")
            .field("version", &self.version())
            .finish_non_exhaustive()
    }
}

impl<'a, H: SmtCommandHandler> SmtReader<'a, H> {
    /// Creates a reader of an SMT-LIB script, whose commands are delivered to `handler`.
    ///
    /// The version under which the script is read can be changed
    /// by `set-info` commands. Therefore, the version-change posture
    /// and the initial version used before any commands are read
    /// must be provided.
    pub fn script(
        handler: &'a mut H,
        posture: SmtVersionPosture,
        initial_version: SmtVersion,
    ) -> Self {
        Self::new(handler, SmtScriptParser::new(posture), initial_version)
    }
}

impl<'a, H: SmtHandler + ?Sized, P: SmtParse<H>> SmtReader<'a, H, P> {
    /// Creates a reader of the input `parser` accepts, over `handler`.
    ///
    /// The version passed is the initial one.
    /// Parsers may request the lexer to change versions,
    /// and the lexer will always comply.
    /// No standard parser changes versions except for [`SmtScriptParser`].
    pub fn new(handler: &'a mut H, parser: P, version: SmtVersion) -> Self {
        let lexer = SmtLexer::new(SmtParseAdapter::new(handler, parser), version);
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
    /// Returns the located parser result if successful.
    ///
    /// A failure to open the file is reported as an I/O error with an empty
    /// span at the start of the input. An I/O read error is reported as
    /// an empty span at the respective position.
    ///
    /// May panic if a previous call on this reader returned an error
    /// or if the parser breaks its contract.
    pub fn read_file(
        &mut self,
        path: impl AsRef<Path>,
    ) -> Result<SmtLocated<P::Result>, SmtReadError<H::Error>> {
        let file = File::open(path)
            .map_err(|err| SmtReadError::new(SmtReadErrorKind::Io(err), SmtSpan::new_zero()))?;

        // make the bufreader use 1 MiB buffer so that we can
        // lex/parse more efficiently with larger batches
        const BUF_READER_CAPACITY: usize = 1024 * 1024;
        let buf_reader = BufReader::with_capacity(BUF_READER_CAPACITY, file);
        self.read_from(buf_reader)
    }

    /// Reads the slice as the whole input.
    ///
    /// Returns the located parser result if successful.
    ///
    /// May panic if a previous call on this reader returned an error
    /// or if the parser breaks its contract.
    pub fn read_all(
        &mut self,
        input: &[u8],
    ) -> Result<SmtLocated<P::Result>, SmtReadError<H::Error>> {
        self.read_slice(input)?;
        self.read_eof()
    }

    /// Reads the content of the buffered reader.
    ///
    /// Returns the located parser result if successful.
    ///
    /// The input is considered to end when the buffered reader returns
    /// a zero-length buffer. A failure while reading is reported as
    /// an I/O error with an empty span at the position reached.
    ///
    /// The buffer content is consumed up to where the parser requests
    /// discarding the rest or fully if no such request was made.
    ///
    /// May panic if a previous call on this reader returned an error
    /// or if the parser breaks its contract.
    pub fn read_from<R: BufRead>(
        &mut self,
        mut buf_reader: R,
    ) -> Result<SmtLocated<P::Result>, SmtReadError<H::Error>> {
        loop {
            if self.lexer.discarded_from().is_some() {
                // the lexer does not care about any subsequent bytes, break
                break;
            }

            let buffer = match buf_reader.fill_buf() {
                Ok(buffer) => buffer,
                Err(err) => {
                    // I/O error
                    // return an empty span on the current lexer location
                    let location = self.lexer.current_location();
                    let span = SmtSpan::new_empty(location);
                    let kind = SmtReadErrorKind::Io(err);
                    return Err(SmtReadError::new(kind, span));
                }
            };

            if buffer.is_empty() {
                // end of file reached
                break;
            }

            // remember the current offset and process the buffer
            let start_offset = self.lexer.current_location().offset();
            self.read_slice(buffer)?;
            // we need to consume the bytes read
            // this might not be all bytes when discarding is set
            // use the current lexer location offset minus our start offset
            let len = self
                .lexer
                .current_location()
                .offset()
                .saturating_sub(start_offset) as usize;
            buf_reader.consume(len);
        }

        // end of stream, process EOF
        // this will reset the lexer and return the break value
        self.read_eof()
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

    /// The location from which the input has been discarded, if set.
    ///
    /// [`SmtScriptParser`] discards input after the `(exit)` command.
    /// No other standard parsers discard.
    pub fn discarded_from(&self) -> Option<SmtLocation> {
        self.lexer.discarded_from()
    }

    /// Returns a reference to the handler.
    pub fn handler(&self) -> &H {
        self.lexer.consumer().handler()
    }

    /// Returns a mutable reference to the handler.
    pub fn handler_mut(&mut self) -> &mut H {
        self.lexer.consumer_mut().handler_mut()
    }
}

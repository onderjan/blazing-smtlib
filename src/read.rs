use std::{
    fs::File,
    io::{BufRead, BufReader},
    ops::ControlFlow,
    path::Path,
};

use crate::{
    CommandHandler, SmtHandler, SmtSpan,
    read::{
        lexer::{LexError, Lexer, LexerError, LexerErrorKind},
        parser::{CategoryParserErrorKind, Parser, ParserError, ParserErrorKind},
    },
};

pub mod lexer;
pub mod parser;

pub enum SmtReadErrorKind<H: SmtHandler> {
    /// The error occurred when reading.
    Io(std::io::Error),
    /// The error occurred when lexing.
    Lexer(LexerErrorKind),
    /// The error occurred when parsing.
    Parser(CategoryParserErrorKind),
    /// The error occurred in the user handler.
    Handler(H::Error),
}

pub struct SmtReadError<H: SmtHandler> {
    kind: SmtReadErrorKind<H>,
    span: SmtSpan,
}

impl<H: SmtHandler> SmtReadError<H> {
    pub(crate) fn new(kind: SmtReadErrorKind<H>, span: SmtSpan) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &SmtReadErrorKind<H> {
        &self.kind
    }

    /// Span where the error occurred.
    ///
    /// For I/O errors, the returned span is empty,
    /// indicating the position where the reading failed.
    pub fn span(&self) -> SmtSpan {
        self.span
    }

    pub fn into_kind(self) -> SmtReadErrorKind<H> {
        self.kind
    }
}

impl<H: SmtHandler> From<LexError<ParserError<H>>> for SmtReadError<H> {
    fn from(err: LexError<ParserError<H>>) -> Self {
        match err {
            LexError::Lexer(err) => err.into(),
            LexError::Handler(err) => err.into(),
        }
    }
}

impl<H: SmtHandler> From<LexerError> for SmtReadError<H> {
    fn from(err: LexerError) -> Self {
        let span = err.span();
        SmtReadError::new(SmtReadErrorKind::Lexer(err.into_kind()), span)
    }
}

impl<H: SmtHandler> From<ParserError<H>> for SmtReadError<H> {
    fn from(err: ParserError<H>) -> Self {
        let span = err.span();
        let kind: SmtReadErrorKind<H> = match err.into_kind() {
            ParserErrorKind::Category(err) => SmtReadErrorKind::Parser(err),
            ParserErrorKind::Handler(err) => SmtReadErrorKind::Handler(err),
        };
        SmtReadError::new(kind, span)
    }
}

pub fn read_smt_file<H: CommandHandler>(
    handler: &mut H,
    path: &Path,
) -> Result<(), SmtReadError<H>> {
    let file = File::open(path)
        .map_err(|err| SmtReadError::new(SmtReadErrorKind::Io(err), SmtSpan::new_zero()))?;
    let reader = BufReader::new(file);
    read_smt(handler, reader)
}

pub fn read_smt<H: CommandHandler>(
    handler: &mut H,
    buf_reader: impl BufRead,
) -> Result<(), SmtReadError<H>> {
    let mut parser = Parser::new(handler);
    SmtReader::new(&mut parser, buf_reader).run()
}

struct SmtReader<'a, H: CommandHandler, R: BufRead> {
    buf_reader: R,
    lexer: Lexer<&'a mut Parser<'a, H>>,
}

impl<'a, H: CommandHandler, R: BufRead> SmtReader<'a, H, R> {
    fn new(parser: &'a mut Parser<'a, H>, buf_reader: R) -> Self {
        let lexer = Lexer::new(parser);
        Self { buf_reader, lexer }
    }

    fn run(mut self) -> Result<(), SmtReadError<H>> {
        while let ControlFlow::Continue(()) = self.read_buf()? {}
        self.finish_eof()
    }

    fn read_buf(&mut self) -> Result<ControlFlow<()>, SmtReadError<H>> {
        match self.buf_reader.fill_buf() {
            Ok(buffer) => {
                if buffer.is_empty() {
                    // end of stream
                    return Ok(ControlFlow::Break(()));
                }
                for c in buffer.iter().copied() {
                    self.lexer.lex_next(c)?;
                }
                let num_consumed = buffer.len();
                self.buf_reader.consume(num_consumed);
                Ok(ControlFlow::Continue(()))
            }
            Err(err) => {
                // return an empty span on the current lexer location
                let location = self.lexer.current_location();
                let span = SmtSpan::new_empty(location);
                let kind = SmtReadErrorKind::Io(err);
                Err(SmtReadError::new(kind, span))
            }
        }
    }

    fn finish_eof(mut self) -> Result<(), SmtReadError<H>> {
        self.lexer.lex_eof().map_err(|err| err.into())
    }
}

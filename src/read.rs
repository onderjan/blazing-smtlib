use std::{
    fs::File,
    io::{BufReader, Read},
    ops::ControlFlow,
    path::Path,
};

use crate::{
    CommandHandler, SmtHandler, SmtSpan,
    lexer::{LexerError, LexerErrorKind},
    read::{
        lexer::Lexer,
        parser::{Parser, ParserError, ParserOrHandlerError},
    },
    token::Token,
};

pub mod lexer;
pub mod parser;

pub enum SmtReadErrorKind<H: SmtHandler> {
    /// The error occurred when reading.
    ///
    /// The returned span is empty,
    /// indicating the position where the reading failed.
    Io(std::io::Error),
    /// The error occured when lexing.
    Lexer(LexerErrorKind),
    /// The error occured when parsing.
    Parser(ParserError),

    // TODO: proper span of user-handler error
    /// The error occured in the user handler.
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

    pub fn span(&self) -> SmtSpan {
        self.span
    }

    pub fn into_kind(self) -> SmtReadErrorKind<H> {
        self.kind
    }
}

impl<H: SmtHandler> From<LexerError> for SmtReadError<H> {
    fn from(err: LexerError) -> Self {
        let span = err.span();
        SmtReadError::new(SmtReadErrorKind::Lexer(err.into_kind()), span)
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

struct SmtReader<'a, H: CommandHandler, R: Read> {
    reader: R,
    lexer: Lexer,
    parser: Parser<'a, H>,
}

impl<'a, H: CommandHandler, R: Read> SmtReader<'a, H, R> {
    fn new(handler: &'a mut H, reader: R) -> Self {
        let lexer = Lexer::new();
        let parser = Parser::new(handler);
        Self {
            reader,
            lexer,
            parser,
        }
    }

    fn read_next(&mut self) -> Result<ControlFlow<()>, SmtReadError<H>> {
        let mut c = 0;
        match self.reader.read(std::slice::from_mut(&mut c)) {
            Ok(num_bytes) => {
                if num_bytes == 0 {
                    // end of stream
                    return Ok(ControlFlow::Break(()));
                }
                assert_eq!(num_bytes, 1);
                let tokens = self.lexer.lex_next(c)?;
                self.parse_tokens(tokens)
                    .map(|()| ControlFlow::Continue(()))
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
        let tokens = self.lexer.lex_eof()?;
        self.parse_tokens(tokens)
    }

    fn parse_tokens(&mut self, tokens: Vec<Token>) -> Result<(), SmtReadError<H>> {
        for token in tokens {
            let span = token.span();
            match self.parser.parse_token(token) {
                Ok(()) => {}
                Err(err) => {
                    let span = self.lexer.resolve_span(span);
                    let kind = match err {
                        ParserOrHandlerError::ParserError(err) => SmtReadErrorKind::Parser(err),
                        ParserOrHandlerError::HandlerError(err) => SmtReadErrorKind::Handler(err),
                    };
                    return Err(SmtReadError::new(kind, span));
                }
            }
        }
        Ok(())
    }
}

pub fn read_smt<H: CommandHandler>(
    handler: &mut H,
    reader: impl Read,
) -> Result<(), SmtReadError<H>> {
    let mut reader = SmtReader::new(handler, reader);

    while let ControlFlow::Continue(()) = reader.read_next()? {}

    reader.finish_eof()
}

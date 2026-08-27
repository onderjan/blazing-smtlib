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

#[cfg(test)]
mod tests {
    use std::io::Read;

    use super::*;
    use crate::{CheckStandardSyntax, SmtLocation};

    /// Expected location as `(offset, line, column)`.
    type Loc = (u64, u64, u64);

    fn loc(location: SmtLocation) -> Loc {
        (location.offset(), location.line(), location.column())
    }

    fn read(input: &[u8]) -> Result<(), SmtReadError<CheckStandardSyntax>> {
        read_smt(&mut CheckStandardSyntax, input)
    }

    #[track_caller]
    fn assert_span(err: &SmtReadError<CheckStandardSyntax>, start: Loc, end: Loc) {
        let span = err.span();
        assert_eq!(
            (loc(span.start()), loc(span.end())),
            (start, end),
            "span mismatch (start, end) as (offset, line, column)"
        );
    }

    #[test]
    fn valid_input_has_no_error() {
        assert!(read(b"").is_ok());
        assert!(read(b"(set-logic QF_UF)\n(check-sat)\n").is_ok());
        assert!(read(b"; comment only").is_ok());
    }

    #[test]
    fn lexer_error_kind_and_span_are_passed_through() {
        // the string literal starts on line 3, column 3 (offset 15) and is unclosed at EOF
        let err = read(b"(check-sat)\n\n  \"abc").expect_err("expected a lexer error, got Ok");
        assert!(matches!(
            err.kind(),
            SmtReadErrorKind::Lexer(LexerErrorKind::UnclosedStringLiteral)
        ));
        assert_span(&err, (15, 3, 3), (19, 3, 7));
    }

    #[test]
    fn parser_error_span_is_resolved_to_lines() {
        // `(assert )` is missing a term; the offending token is the `)` on line 2
        let err = read(b"(check-sat)\n(assert )").expect_err("expected a parser error, got Ok");
        assert!(matches!(
            err.kind(),
            SmtReadErrorKind::Parser(ParserError::ExpectedTerm)
        ));
        assert_span(&err, (20, 2, 9), (21, 2, 10));
    }

    #[test]
    fn parser_error_at_eof_is_empty_span() {
        // unclosed command: the error is on the zero-width EOF token after a newline
        let err = read(b"(check-sat\n").expect_err("expected a parser error, got Ok");
        assert!(matches!(err.kind(), SmtReadErrorKind::Parser(_)));
        assert_span(&err, (11, 2, 1), (11, 2, 1));
    }

    /// Reader that yields the given bytes and then fails.
    struct FailingReader<'a> {
        data: &'a [u8],
    }

    impl Read for FailingReader<'_> {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            if self.data.is_empty() {
                return Err(std::io::Error::other("simulated failure"));
            }
            self.data.read(buf)
        }
    }

    #[test]
    fn io_error_has_empty_span_at_current_location() {
        let reader = FailingReader {
            data: b"(check-sat)\n(",
        };
        let err =
            read_smt(&mut CheckStandardSyntax, reader).expect_err("expected an I/O error, got Ok");
        assert!(matches!(err.kind(), SmtReadErrorKind::Io(_)));
        // 13 bytes were consumed, so the location is line 2, column 2
        assert_span(&err, (13, 2, 2), (13, 2, 2));
    }

    #[test]
    fn file_open_error_has_zero_span() {
        let path = std::path::Path::new("/nonexistent/smt-parser-test/does-not-exist.smt2");
        let err = read_smt_file(&mut CheckStandardSyntax, path)
            .expect_err("expected an I/O error, got Ok");
        assert!(matches!(err.kind(), SmtReadErrorKind::Io(_)));
        assert_span(&err, (0, 1, 1), (0, 1, 1));
    }
}

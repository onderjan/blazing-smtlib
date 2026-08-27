use std::ops::ControlFlow;

use crate::{
    CommandHandler,
    api::SmtHandler,
    token::{Token, TokenKind},
};

mod category;
mod command;

pub use command::{CommandResult, DynamicCommandParser, ParseCommand};

#[derive(Debug)]
pub enum ParserError {
    ExpectedToken(TokenKind),
    ExpectedUnderscore,
    ExpectedSymbol,
    ExpectedKeyword,
    ExpectedOpenOrCloseParen,
    EmptyIdentIndices,
    InvalidIdent,
    InvalidAttributeValue,
    EmptyApplication,
    EmptyLetBindings,
    ExpectedIndexOrCloseParen,
    ExpectedOperator,
    ExpectedSExpr,
    ExpectedIdent,
    ExpectedSort,
    ExpectedSortInner,
    ExpectedTerm,
    ExpectedAttribute,
    ExpectedCommand,
    ExpectedCommandName,
    UnsupportedCommand,
    SortApplicationNotSupported,
    ExpectedLetBinding,
    RequiredIndices,
}

#[derive(Debug)]
pub enum ParserOrHandlerError<H: SmtHandler> {
    ParserError(ParserError),
    HandlerError(H::Error),
}

impl<H: SmtHandler> From<ParserError> for ParserOrHandlerError<H> {
    fn from(value: ParserError) -> Self {
        ParserOrHandlerError::ParserError(value)
    }
}

pub struct Parser<'a, H: CommandHandler> {
    handler: &'a mut H,
    state: ParserState<H>,
}

pub(crate) enum ParserState<H: CommandHandler> {
    AwaitingCommand,
    CommandOpen,
    StandardCommand(DynamicCommandParser<H>),
    Exit,
}

impl<'a, H: CommandHandler> Parser<'a, H> {
    pub fn new(handler: &'a mut H) -> Self {
        Self {
            handler,
            state: ParserState::AwaitingCommand,
        }
    }

    pub fn parse_token(&mut self, token: Token) -> Result<(), ParserOrHandlerError<H>> {
        //eprintln!("Token: {:?}", token);
        let state = std::mem::replace(&mut self.state, ParserState::AwaitingCommand);
        let state = match state {
            ParserState::AwaitingCommand => {
                match token.kind() {
                    TokenKind::ParenOpen => {
                        // open the command
                        ParserState::CommandOpen
                    }
                    TokenKind::EndOfFile => {
                        // end of file here is fine, do not change the state
                        ParserState::AwaitingCommand
                    }
                    _ => {
                        return Err(ParserOrHandlerError::ParserError(
                            ParserError::ExpectedCommand,
                        ));
                    }
                }
            }
            ParserState::CommandOpen => {
                // expect a symbol identifying the command
                let TokenKind::Symbol(command_name) = token.into_kind() else {
                    return Err(ParserError::ExpectedCommand.into());
                };
                ParserState::StandardCommand(self.start_command(command_name.as_view())?)
            }
            ParserState::StandardCommand(mut stage) => match stage.progress(self.handler, token)? {
                ControlFlow::Continue(()) => ParserState::StandardCommand(stage),
                ControlFlow::Break(CommandResult::EndCommand) => ParserState::AwaitingCommand,
                ControlFlow::Break(CommandResult::Exit) => ParserState::Exit,
            },
            ParserState::Exit => {
                // no operation on fed tokens
                ParserState::Exit
            }
        };
        self.state = state;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{OnlyCheckSyntax, TokenSpan, read::lexer::Lexer};

    /// Lexes the input and feeds the tokens to a fresh parser.
    ///
    /// On a parser error, returns it together with the span of the offending token.
    fn parse(input: &[u8]) -> Result<(), (ParserError, TokenSpan)> {
        let mut lexer = Lexer::new();
        let mut handler = OnlyCheckSyntax;
        let mut parser = Parser::new(&mut handler);

        let mut tokens = Vec::new();
        for &c in input {
            tokens.extend(lexer.lex_next(c).expect("test input must lex"));
        }
        tokens.extend(lexer.lex_eof().expect("test input must lex"));

        for token in tokens {
            let span = token.span();
            match parser.parse_token(token) {
                Ok(()) => {}
                Err(ParserOrHandlerError::ParserError(err)) => return Err((err, span)),
                Err(ParserOrHandlerError::HandlerError(err)) => match err {},
            }
        }
        Ok(())
    }

    /// Parses the input, requires a parser error, checks the byte span of the offending token,
    /// and returns the error so that the caller can inspect the variant.
    #[track_caller]
    fn assert_error(input: &[u8], start: u64, end: u64) -> ParserError {
        let (err, span) = parse(input).expect_err("expected a parser error, got Ok");
        assert_eq!(
            (span.start(), span.end()),
            (start, end),
            "token span mismatch (start, end) as byte offsets"
        );
        err
    }

    #[test]
    fn valid_input_has_no_error() {
        assert!(parse(b"").is_ok());
        assert!(parse(b"(set-logic QF_UF)\n(check-sat)\n").is_ok());
        assert!(parse(b"(declare-const x Bool) (assert x) (check-sat) (exit)").is_ok());
    }

    #[test]
    fn bare_symbol_is_whole_token() {
        // a command must be parenthesized; the whole symbol token is the span
        let err = assert_error(b"check-sat", 0, 9);
        assert!(matches!(err, ParserError::ExpectedCommand), "{err:?}");
    }

    #[test]
    fn missing_term_points_at_close_paren() {
        let err = assert_error(b"(check-sat)\n(assert )", 20, 21);
        assert!(matches!(err, ParserError::ExpectedTerm), "{err:?}");
    }

    #[test]
    fn numeral_as_command_name() {
        let err = assert_error(b"(set-logic QF_UF)\n(1)", 19, 20);
        assert!(matches!(err, ParserError::ExpectedCommand), "{err:?}");
    }

    #[test]
    fn unclosed_command_points_at_eof() {
        // the error is on the zero-width EOF token
        let _ = assert_error(b"(check-sat", 10, 10);
        let _ = assert_error(b"(check-sat\n", 11, 11);
    }

    #[test]
    fn unknown_command() {
        let err = assert_error(b"(frobnicate)", 1, 11);
        assert!(matches!(err, ParserError::UnsupportedCommand), "{err:?}");
    }
}

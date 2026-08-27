use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtSpan,
    api::SmtHandler,
    token::{Token, TokenKind},
};

mod category;
mod command;

pub use category::*;
pub use command::*;

pub enum ParserErrorKind<H: SmtHandler + ?Sized> {
    ParserError(CategoryParserErrorKind),
    HandlerError(H::Error),
}

pub struct ParserError<H: SmtHandler + ?Sized> {
    kind: ParserErrorKind<H>,
    span: SmtSpan,
}

impl<H: SmtHandler> ParserError<H> {
    pub(crate) fn new(kind: ParserErrorKind<H>, span: SmtSpan) -> Self {
        Self { kind, span }
    }

    pub(crate) fn handler_error(err: H::Error, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::HandlerError(err), span)
    }

    pub(crate) fn category_error(err: CategoryParserErrorKind, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::ParserError(err), span)
    }

    pub fn kind(&self) -> &ParserErrorKind<H> {
        &self.kind
    }

    pub fn span(&self) -> SmtSpan {
        self.span
    }

    pub fn into_kind(self) -> ParserErrorKind<H> {
        self.kind
    }
}

impl<H: SmtHandler> From<CategoryParserError> for ParserError<H> {
    fn from(value: CategoryParserError) -> Self {
        let span = value.span();
        Self::new(ParserErrorKind::ParserError(value.into_kind()), span)
    }
}

pub struct Parser<'a, H: CommandHandler> {
    handler: &'a mut H,
    state: ParserState<H>,
}

pub(crate) enum ParserState<H: CommandHandler> {
    AwaitingCommand,
    CommandOpen,
    Command(CommandParser<H>),
    Exit,
}

impl<'a, H: CommandHandler> Parser<'a, H> {
    pub fn new(handler: &'a mut H) -> Self {
        Self {
            handler,
            state: ParserState::AwaitingCommand,
        }
    }

    pub fn parse_token(&mut self, token: Token) -> Result<(), ParserError<H>> {
        let span = token.span();
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
                        return Err(CategoryParserError::new(
                            CategoryParserErrorKind::ExpectedCommand,
                            span,
                        )
                        .into());
                    }
                }
            }
            ParserState::CommandOpen => {
                // expect a symbol identifying the command
                let TokenKind::Symbol(command_name) = token.into_kind() else {
                    return Err(CategoryParserError::new(
                        CategoryParserErrorKind::ExpectedCommandName,
                        span,
                    )
                    .into());
                };
                ParserState::Command(self.start_command(command_name, span)?)
            }
            ParserState::Command(mut stage) => match stage.progress(self.handler, token)? {
                ControlFlow::Continue(()) => ParserState::Command(stage),
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

    use crate::{
        CheckStandardSyntax, NonstandardCommandError, SmtAttributeValue, SmtFunctionSignature,
        SmtKeyword, SmtSExpr, SmtSort, SmtStringContent, SmtSymbol, SmtTerm,
        read::{
            lexer::Lexer,
            parser::{
                category::{ClosedParser, term::TermParser},
                command::{StandardCommand, StaticCommandParser},
            },
        },
    };

    /// Lexes the input and feeds the tokens to a fresh parser over the given handler.
    fn parse_with<H: CommandHandler>(handler: &mut H, input: &[u8]) -> Result<(), ParserError<H>> {
        let mut parser = Parser::new(handler);
        for token in Lexer::lex_all(input).expect("test input must lex") {
            parser.parse_token(token)?;
        }
        Ok(())
    }

    fn parse(input: &[u8]) -> Result<(), ParserError<CheckStandardSyntax>> {
        parse_with(&mut CheckStandardSyntax, input)
    }

    #[track_caller]
    fn assert_error_span<H: SmtHandler>(err: &ParserError<H>, start: u64, end: u64) {
        let span = err.span();
        assert_eq!(
            (span.start().offset(), span.end().offset()),
            (start, end),
            "error span mismatch (start, end) as byte offsets"
        );
    }

    /// Parses the input, requires a parser error, checks the byte span the error carries,
    /// and returns its kind so that the caller can inspect the variant.
    #[track_caller]
    fn assert_parser_error(input: &[u8], start: u64, end: u64) -> CategoryParserErrorKind {
        let err = parse(input).expect_err("expected a parser error, got Ok");
        assert_error_span(&err, start, end);
        match err.into_kind() {
            ParserErrorKind::ParserError(kind) => kind,
            ParserErrorKind::HandlerError(err) => {
                panic!("expected parser error, got handler error on {:?}", err.0)
            }
        }
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
        let err = assert_parser_error(b"check-sat", 0, 9);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedCommand),
            "{err:?}"
        );
    }

    #[test]
    fn missing_term_points_at_close_paren() {
        let err = assert_parser_error(b"(check-sat)\n(assert )", 20, 21);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedTerm),
            "{err:?}"
        );
    }

    #[test]
    fn numeral_as_command_name() {
        let err = assert_parser_error(b"(set-logic QF_UF)\n(1)", 19, 20);
        assert!(
            matches!(err, CategoryParserErrorKind::ExpectedCommandName),
            "{err:?}"
        );
    }

    #[test]
    fn unclosed_command_points_at_eof() {
        // the error is on the zero-width EOF token
        let _ = assert_parser_error(b"(check-sat", 10, 10);
        let _ = assert_parser_error(b"(check-sat\n", 11, 11);
    }

    // --- Nonstandard commands ---

    #[test]
    fn nonstandard_command_is_rejected_by_standard_syntax() {
        // the handler rejects the command by name; the span is that of the name symbol
        let err = parse(b"(frobnicate 1)").expect_err("expected a handler error");
        assert_error_span(&err, 1, 11);
        match err.into_kind() {
            ParserErrorKind::HandlerError(NonstandardCommandError(name)) => {
                assert_eq!(name.as_slice(), b"frobnicate");
            }
            ParserErrorKind::ParserError(kind) => {
                panic!("expected handler error, got {kind:?}")
            }
        }
    }

    /// Handler accepting the nonstandard command `(my-assert <term>)`
    /// and recording every command it sees.
    #[derive(Default)]
    struct Recording {
        commands: Vec<&'static str>,
    }

    struct MyAssert;

    impl StandardCommand<Recording> for MyAssert {
        type Parser = ClosedParser<Recording, TermParser<Recording>>;

        fn handle(handler: &mut Recording, _term: ()) -> Result<(), NonstandardCommandError> {
            handler.commands.push("my-assert");
            Ok(())
        }
    }

    impl SmtHandler for Recording {
        type Error = NonstandardCommandError;
        type SExpr = ();
        type Attribute = ();
        type Sort = ();
        type Term = ();

        fn handle_sort(&mut self, _sort: SmtSort) -> Result<(), Self::Error> {
            Ok(())
        }
        fn handle_term(&mut self, _term: SmtTerm<Self>) -> Result<(), Self::Error> {
            Ok(())
        }
        fn start_let(&mut self, _bindings: Vec<(SmtSymbol, ())>) -> Result<(), Self::Error> {
            Ok(())
        }
        fn end_let(&mut self, _term: ()) -> Result<(), Self::Error> {
            Ok(())
        }
        fn handle_s_expr(&mut self, _expr: SmtSExpr<()>) -> Result<(), Self::Error> {
            Ok(())
        }
        fn handle_attribute(
            &mut self,
            _name: SmtKeyword,
            _value: Option<SmtAttributeValue<Self>>,
        ) -> Result<(), Self::Error> {
            Ok(())
        }
    }

    impl CommandHandler for Recording {
        type NonstandardParser = StaticCommandParser<Self, MyAssert>;

        fn nonstandard_command(
            &mut self,
            name: SmtSymbol,
        ) -> Result<Self::NonstandardParser, Self::Error> {
            match name.as_slice() {
                b"my-assert" => Ok(StaticCommandParser::new()),
                _ => Err(NonstandardCommandError(name)),
            }
        }

        fn command_echo(&mut self, _value: SmtStringContent) -> Result<(), Self::Error> {
            self.commands.push("echo");
            Ok(())
        }
        fn command_get_option(&mut self, _option: SmtKeyword) -> Result<(), Self::Error> {
            self.commands.push("get-option");
            Ok(())
        }
        fn command_set_option(&mut self, _option: ()) -> Result<(), Self::Error> {
            self.commands.push("set-option");
            Ok(())
        }
        fn command_get_info(&mut self, _keyword: SmtKeyword) -> Result<(), Self::Error> {
            self.commands.push("get-info");
            Ok(())
        }
        fn command_set_info(&mut self, _attribute: ()) -> Result<(), Self::Error> {
            self.commands.push("set-info");
            Ok(())
        }
        fn command_set_logic(&mut self, _logic: SmtSymbol) -> Result<(), Self::Error> {
            self.commands.push("set-logic");
            Ok(())
        }
        fn command_declare_const(
            &mut self,
            _name: SmtSymbol,
            _sort: (),
        ) -> Result<(), Self::Error> {
            self.commands.push("declare-const");
            Ok(())
        }
        fn command_declare_fun(
            &mut self,
            _name: SmtSymbol,
            _param_sorts: Vec<()>,
            _result_sort: (),
        ) -> Result<(), Self::Error> {
            self.commands.push("declare-fun");
            Ok(())
        }
        fn command_define_fun(
            &mut self,
            _name: SmtSymbol,
            _params: Vec<(SmtSymbol, ())>,
            _result_sort: (),
            _definition: (),
        ) -> Result<(), Self::Error> {
            self.commands.push("define-fun");
            Ok(())
        }
        fn command_assert(&mut self, _term: ()) -> Result<(), Self::Error> {
            self.commands.push("assert");
            Ok(())
        }
        fn command_check_sat(&mut self) -> Result<(), Self::Error> {
            self.commands.push("check-sat");
            Ok(())
        }
        fn command_reset(&mut self) -> Result<(), Self::Error> {
            self.commands.push("reset");
            Ok(())
        }
        fn command_reset_assertions(&mut self) -> Result<(), Self::Error> {
            self.commands.push("reset-assertions");
            Ok(())
        }
        fn command_exit(&mut self) -> Result<(), Self::Error> {
            self.commands.push("exit");
            Ok(())
        }
        fn start_define_fun(
            &mut self,
            _signature: SmtFunctionSignature<()>,
        ) -> Result<(), Self::Error> {
            Ok(())
        }
        fn end_define_fun(&mut self, _term: ()) -> Result<(), Self::Error> {
            Ok(())
        }
    }

    #[test]
    fn nonstandard_command_is_parsed_by_handler_parser() {
        let mut handler = Recording::default();
        // the nonstandard command body is parsed with a library term parser,
        // and standard commands keep working after it
        parse_with(
            &mut handler,
            b"(declare-const x Bool) (my-assert (f x (g 1))) (check-sat)",
        )
        .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
        assert_eq!(
            handler.commands,
            ["declare-const", "my-assert", "check-sat"]
        );
    }

    #[test]
    fn nonstandard_command_body_is_checked() {
        // a malformed body is a parser error on the offending token
        let mut handler = Recording::default();
        let err = parse_with(&mut handler, b"(my-assert )").expect_err("expected a parser error");
        assert_error_span(&err, 11, 12);
        match err.into_kind() {
            ParserErrorKind::ParserError(CategoryParserErrorKind::ExpectedTerm) => {}
            ParserErrorKind::ParserError(kind) => panic!("unexpected parser error {kind:?}"),
            ParserErrorKind::HandlerError(_) => panic!("unexpected handler error"),
        }
        assert!(handler.commands.is_empty());
    }

    #[test]
    fn nonstandard_command_unknown_to_handler_is_rejected() {
        let mut handler = Recording::default();
        let err = parse_with(&mut handler, b"(my-assert x) (other)")
            .expect_err("expected a handler error");
        assert_error_span(&err, 15, 20);
        match err.into_kind() {
            ParserErrorKind::HandlerError(NonstandardCommandError(name)) => {
                assert_eq!(name.as_slice(), b"other");
            }
            ParserErrorKind::ParserError(kind) => panic!("unexpected parser error {kind:?}"),
        }
        assert_eq!(handler.commands, ["my-assert"]);
    }
}

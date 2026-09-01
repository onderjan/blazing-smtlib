use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtHandler, SmtSpan,
    token::{Token, TokenKind},
};

mod category;
mod command;

pub use category::*;
pub use command::*;

pub enum ParserErrorKind<H: SmtHandler + ?Sized> {
    Category(CategoryParserErrorKind),
    Handler(H::Error),
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
        Self::new(ParserErrorKind::Handler(err), span)
    }

    pub(crate) fn category_error(err: CategoryParserErrorKind, span: SmtSpan) -> Self {
        Self::new(ParserErrorKind::Category(err), span)
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
        Self::new(ParserErrorKind::Category(value.into_kind()), span)
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

fn handle_err<O, H: SmtHandler>(
    handled: Result<O, H::Error>,
    span: SmtSpan,
) -> Result<O, ParserError<H>> {
    match handled {
        Ok(ok) => Ok(ok),
        Err(err) => Err(ParserError::handler_error(err, span)),
    }
}

// TODO: fix tests
/*
#[cfg(test)]
mod tests {
    use super::*;

    use crate::{
        CheckStandardSyntax, NonstandardCommandError, SmtAttributeValue, SmtFunctionSignature,
        SmtKeyword, SmtSExpr, SmtSort, SmtStringContent, SmtSymbol, SmtTerm,
        read::{
            lexer::Lexer,
            parser::{
                category::{ClosedParser, TermParser},
                command::{StandardCommand, StaticCommandParser},
            },
        },
    };

    /// Lexes the input and feeds the tokens to a fresh parser over the given handler.
    pub(in crate::read::parser) fn parse_with<H: CommandHandler>(
        handler: &mut H,
        input: &[u8],
    ) -> Result<(), ParserError<H>> {
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
    pub(in crate::read::parser) fn assert_error_span<H: SmtHandler>(
        err: &ParserError<H>,
        start: u64,
        end: u64,
    ) {
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
    pub(in crate::read::parser) fn assert_parser_error(
        input: &[u8],
        start: u64,
        end: u64,
    ) -> CategoryParserErrorKind {
        let err = parse(input).expect_err("expected a parser error, got Ok");
        assert_error_span(&err, start, end);
        match err.into_kind() {
            ParserErrorKind::Category(kind) => kind,
            ParserErrorKind::Handler(err) => {
                panic!("expected parser error, got handler error on {:?}", err.0)
            }
        }
    }

    #[test]
    fn valid_input_has_no_error() {
        assert!(parse(b"").is_ok());
        assert!(parse(b"(set-logic QF_UF)\n(check-sat)\n").is_ok());
        assert!(parse(b"(declare-const x Bool) (assert x) (check-sat) (exit)").is_ok());
        assert!(parse(b"(define-fun inc ((x Int)) Int (+ x 1)) (check-sat)").is_ok());
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
            ParserErrorKind::Handler(NonstandardCommandError(name)) => {
                assert_eq!(name.as_slice(), b"frobnicate");
            }
            ParserErrorKind::Category(kind) => {
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

        fn handle_sort(&mut self, _sort: SmtSort<Self>) -> Result<(), Self::Error> {
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
        fn handle_s_expr(&mut self, _expr: SmtSExpr<Self>) -> Result<(), Self::Error> {
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
            _signature: SmtFunctionSignature<Self>,
        ) -> Result<(), Self::Error> {
            self.commands.push("start-define-fun");
            Ok(())
        }
        fn end_define_fun(&mut self, _term: ()) -> Result<(), Self::Error> {
            self.commands.push("end-define-fun");
            Ok(())
        }
    }

    #[test]
    fn trivial_commands_reach_their_handler_methods() {
        let mut handler = Recording::default();
        parse_with(
            &mut handler,
            b"(echo \"hi\") (get-option :opt) (set-option :produce-models true) \
              (get-info :name) (reset) (reset-assertions)",
        )
        .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
        assert_eq!(
            handler.commands,
            [
                "echo",
                "get-option",
                "set-option",
                "get-info",
                "reset",
                "reset-assertions"
            ]
        );
    }

    #[test]
    fn define_fun_start_and_end_surround_the_body() {
        let mut handler = Recording::default();
        parse_with(&mut handler, b"(define-fun f ((x Int)) Int x) (check-sat)")
            .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
        assert_eq!(
            handler.commands,
            ["start-define-fun", "end-define-fun", "check-sat"]
        );
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
            ParserErrorKind::Category(CategoryParserErrorKind::ExpectedTerm) => {}
            ParserErrorKind::Category(kind) => panic!("unexpected parser error {kind:?}"),
            ParserErrorKind::Handler(_) => panic!("unexpected handler error"),
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
            ParserErrorKind::Handler(NonstandardCommandError(name)) => {
                assert_eq!(name.as_slice(), b"other");
            }
            ParserErrorKind::Category(kind) => panic!("unexpected parser error {kind:?}"),
        }
        assert_eq!(handler.commands, ["my-assert"]);
    }
    #[test]
    fn set_info_with_s_expr_attribute_value() {
        assert!(parse(b"(set-info :notes (a (nested :list) 42 \"str\" let ()))").is_ok());
        // both closing parentheses are consumed; the next command still parses
        assert!(parse(b"(set-info :pattern ((f x))) (check-sat)").is_ok());
    }
    // --- Behavior after (exit) ---

    #[test]
    fn everything_after_exit_is_discarded() {
        // after (exit), the parser ignores all further tokens, even non-command
        // garbage and unbalanced parentheses: callers may keep feeding tokens
        assert!(parse(b"(exit) x ) ( 1 (check-sat").is_ok());
    }

    #[test]
    fn commands_after_exit_are_not_handled() {
        let mut handler = Recording::default();
        // `(other)` would be rejected by the handler before the exit,
        // but after it, the handler must not even be consulted
        parse_with(&mut handler, b"(my-assert x) (exit) (other)")
            .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
        assert_eq!(handler.commands, ["my-assert"]);
    }
}
*/

//! Public-API tests of command dispatch: command shape errors, handler
//! callbacks, nonstandard commands, and behavior after `(exit)`.

mod common;

use common::{assert_error_span, assert_parser_error, parse, parse_with};

use smt_parser_rs::{
    CommandHandler, NonstandardCommandError, SmtAttributeValue, SmtFunctionSignature, SmtHandler,
    SmtKeyword, SmtNumeral, SmtQuantifierKind, SmtSExpr, SmtSort, SmtStringContent, SmtSymbol,
    SmtSymbolView, SmtTerm,
    read::{
        SmtReadErrorKind,
        parser::{CategoryParserErrorKind, ClosedParser, CommandAction, CommandParser, TermParser},
    },
};

#[test]
fn valid_input_has_no_error() {
    assert!(parse(b"").is_ok());
    assert!(parse(b"(set-logic QF_UF)\n(check-sat)\n").is_ok());
    assert!(parse(b"(declare-const x Bool) (assert x) (check-sat) (exit)").is_ok());
    assert!(parse(b"(define-fun inc ((x Int)) Int (+ x 1)) (check-sat)").is_ok());
    assert!(parse(b"(define-const c Int 5) (check-sat-assuming ((= c 5)))").is_ok());
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
    match err.kind() {
        SmtReadErrorKind::Handler(NonstandardCommandError(name)) => {
            assert_eq!(name.as_slice(), b"frobnicate");
        }
        SmtReadErrorKind::Parser(kind) => {
            panic!("expected handler error, got parser error {kind:?}")
        }
        _ => panic!("expected handler error"),
    }
}

/// Handler accepting the nonstandard command `(my-assert <term>)`
/// and recording every command it sees.
#[derive(Default)]
struct Recording {
    commands: Vec<&'static str>,
}

struct MyAssert;

impl CommandAction<Recording> for MyAssert {
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
    fn annotate_term(&mut self, _term: (), _attributes: Vec<()>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _name: SmtSymbol,
        _sort: (),
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_quantifier(&mut self, _term: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_lambda(&mut self, _name: SmtSymbol, _sort: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_lambda(&mut self, _term: ()) -> Result<(), Self::Error> {
        Ok(())
    }
}

impl CommandHandler for Recording {
    type NonstandardParser = CommandParser<Self, MyAssert>;

    fn nonstandard_command(
        &mut self,
        name: SmtSymbolView<'_>,
    ) -> Result<Self::NonstandardParser, Self::Error> {
        match name.as_slice() {
            b"my-assert" => Ok(CommandParser::new()),
            _ => Err(NonstandardCommandError(name.into_owned())),
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
    fn command_declare_sort(
        &mut self,
        _name: SmtSymbol,
        _arity: SmtNumeral,
    ) -> Result<(), Self::Error> {
        self.commands.push("declare-sort");
        Ok(())
    }
    fn command_declare_sort_parameter(&mut self, _name: SmtSymbol) -> Result<(), Self::Error> {
        self.commands.push("declare-sort-parameter");
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
    fn command_check_sat(&mut self, assumptions: Vec<()>) -> Result<(), Self::Error> {
        self.commands.push(if assumptions.is_empty() {
            "check-sat"
        } else {
            "check-sat-assuming"
        });
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
          (get-info :name) (declare-sort U 1) (declare-sort-parameter T) \
          (reset) (reset-assertions)",
    )
    .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    assert_eq!(
        handler.commands,
        [
            "echo",
            "get-option",
            "set-option",
            "get-info",
            "declare-sort",
            "declare-sort-parameter",
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
        // declare-const is syntax sugar for declare-fun and shares its callback
        ["declare-fun", "my-assert", "check-sat"]
    );
}

#[test]
fn repeated_nonstandard_commands_each_get_a_fresh_parser() {
    let mut handler = Recording::default();
    // unlike the persistent standard command parsers, nonstandard parsers
    // are requested from the handler for every command
    parse_with(&mut handler, b"(my-assert x) (my-assert (f y)) (check-sat)")
        .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    assert_eq!(handler.commands, ["my-assert", "my-assert", "check-sat"]);
}

#[test]
fn nonstandard_command_body_is_checked() {
    // a malformed body is a parser error on the offending token
    let mut handler = Recording::default();
    let err = parse_with(&mut handler, b"(my-assert )").expect_err("expected a parser error");
    assert_error_span(&err, 11, 12);
    match err.kind() {
        SmtReadErrorKind::Parser(CategoryParserErrorKind::ExpectedTerm) => {}
        SmtReadErrorKind::Parser(kind) => panic!("unexpected parser error {kind:?}"),
        SmtReadErrorKind::Handler(_) => panic!("unexpected handler error"),
        _ => panic!("unexpected error kind"),
    }
    assert!(handler.commands.is_empty());
}

#[test]
fn nonstandard_command_unknown_to_handler_is_rejected() {
    let mut handler = Recording::default();
    let err =
        parse_with(&mut handler, b"(my-assert x) (other)").expect_err("expected a handler error");
    assert_error_span(&err, 15, 20);
    match err.kind() {
        SmtReadErrorKind::Handler(NonstandardCommandError(name)) => {
            assert_eq!(name.as_slice(), b"other");
        }
        SmtReadErrorKind::Parser(kind) => {
            panic!("expected handler error, got parser error {kind:?}")
        }
        _ => panic!("expected handler error"),
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
    // the exit command itself is delivered to the handler, but `(other)`,
    // which the handler would reject before the exit, must not even be
    // consulted after it
    parse_with(&mut handler, b"(my-assert x) (exit) (other)")
        .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    assert_eq!(handler.commands, ["my-assert", "exit"]);
}

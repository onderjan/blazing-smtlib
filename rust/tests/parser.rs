//! Public-API tests of command dispatch: command shape errors, handler
//! callbacks, nonstandard commands, and behavior after `(exit)`.
//!
//! They run against the parser that `parse_backend` selects: the Rust
//! library's, or the Lean port's through the Lean driver.

mod common;
mod parse_backend;

use blazing_smtlib::parser::{SmtMissingItem, SmtSyntaxExpected, SmtVersionErrorKind};
use std::ops::ControlFlow;

use common::{assert_error_span, assert_parser_error, parse, parse_with};
use parse_backend::{
    Adapt, AttributeValue, Bindings, CommandHandler, CommandParser, Constructors, Handler,
    MatchCases, NonstandardPayload, ReadErrorCause, Reader, SExpr, Signature, Signatures, Sort,
    SortArities, SortedVars, Symbols, Term,
};

use blazing_smtlib::{
    SmtHandler, SmtKeywordBuf, SmtNonstandardCommandError, SmtNumeralBuf, SmtPatternBuf,
    SmtQuantifierKind, SmtSpan, SmtStringContentBuf, SmtSymbolBuf,
    lexer::SmtLexer,
    parser::{
        SmtCommandOutcome, SmtParse, SmtParseError, SmtParseState, SmtScriptParser,
        SmtSyntaxErrorKind,
    },
    reader::SmtReader,
    token::{
        SmtBatchCursor, SmtConsume, SmtConsumeFrom, SmtCursor, SmtSyntaxToken, SmtTokenCategory,
        SmtVersionRefused,
    },
    version::{SmtVersion, SmtVersionPosture, SmtVersionPostureBuilder},
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
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // a command must be parenthesized; the whole symbol token is the span
    let err = assert_parser_error(b"check-sat", 0, 9);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[
                SmtSyntaxExpected::Token(SmtTokenCategory::ParenOpen),
                SmtSyntaxExpected::Token(SmtTokenCategory::EndOfFile)
            ])
        ),
        "{err:?}"
    );
}

#[test]
fn missing_term_points_at_close_paren() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    let err = assert_parser_error(b"(check-sat)\n(assert )", 20, 21);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Term])
        ),
        "{err:?}"
    );
}

#[test]
fn numeral_as_command_name() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    let err = assert_parser_error(b"(set-logic QF_UF)\n(1)", 19, 20);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::CommandName])
        ),
        "{err:?}"
    );
}

#[test]
fn unclosed_command_points_at_eof() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // the error is on the zero-width EOF token
    assert_parser_error(b"(check-sat", 10, 10);
    assert_parser_error(b"(check-sat\n", 11, 11);
}

// --- Nonstandard commands ---

#[test]
fn nonstandard_command_is_rejected_by_standard_syntax() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // the handler rejects the command by name; the span is that of the name symbol
    let err = parse(b"(frobnicate 1)").expect_err("expected a handler error");
    assert_error_span(&err, 1, 11);
    match err.cause() {
        ReadErrorCause::Handler(err) => {
            let name = err.name();
            assert_eq!(name.as_slice(), b"frobnicate");
        }
        ReadErrorCause::Syntax(kind) => {
            panic!("expected handler error, got parser error {kind:?}")
        }
        _ => panic!("expected handler error"),
    }
}

#[test]
fn quoted_standard_command_name_names_a_nonstandard_command() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // the standard command names are reserved words; quoted, the name is
    // a symbol, so it is handed to the handler as a nonstandard command
    let err = parse(b"(|check-sat|)").expect_err("expected a handler error");
    assert_error_span(&err, 1, 12);
    match err.cause() {
        ReadErrorCause::Handler(err) => {
            let name = err.name();
            assert_eq!(name.as_slice(), b"check-sat");
        }
        ReadErrorCause::Syntax(kind) => {
            panic!("expected handler error, got parser error {kind:?}")
        }
        _ => panic!("expected handler error"),
    }
}

#[test]
fn reserved_word_other_than_a_command_name_is_no_command_name() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    let err = assert_parser_error(b"(let ((x 1)) x)", 1, 4);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::CommandName])
        ),
        "{err:?}"
    );
}

/// Handler accepting the nonstandard commands `(my-assert <term>)`,
/// `(my-version-2.0)`, which switches the cursor to 2.0, and `(my-discard)`,
/// which has the cursor discard the rest of the input,
/// and recording every command it sees.
#[derive(Default)]
struct Recording {
    commands: Vec<&'static str>,
    /// Whether handled terms and attributes are recorded too, as `term` and `attribute`.
    records_terms_and_attributes: bool,
    /// Whether the versions the handler is set to are recorded too, as `set-version 2.x`.
    records_versions: bool,
}

impl Handler for Recording {
    type Error = SmtNonstandardCommandError;
    type SExpr = ();
    type Attribute = ();
    type Sort = ();
    type Term = ();
    type Scope = ();

    fn set_version(&mut self, version: SmtVersion) {
        if self.records_versions {
            self.commands.push(match version {
                SmtVersion::V2_0 => "set-version 2.0",
                SmtVersion::V2_5 => "set-version 2.5",
                SmtVersion::V2_6 => "set-version 2.6",
                SmtVersion::V2_7 => "set-version 2.7",
            });
        }
    }

    fn handle_sort(&mut self, _sort: Sort<Self::Sort>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn handle_term(&mut self, _term: Term<Self::Sort, Self::Term>) -> Result<(), Self::Error> {
        if self.records_terms_and_attributes {
            self.commands.push("term");
        }
        Ok(())
    }
    fn start_let(&mut self, _bindings: Bindings<Self::Term>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_let(&mut self, _scope: (), _body: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn handle_s_expr(&mut self, _expr: SExpr<Self::SExpr>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn handle_attribute(
        &mut self,
        _name: SmtKeywordBuf,
        _value: Option<AttributeValue<Self::SExpr>>,
    ) -> Result<(), Self::Error> {
        if self.records_terms_and_attributes {
            self.commands.push("attribute");
        }
        Ok(())
    }
    fn annotate_term(
        &mut self,
        _term: (),
        _attributes: Vec<Self::Attribute>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _vars: SortedVars<Self::Sort>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _scope: (),
        _body: (),
    ) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_lambda(&mut self, _vars: SortedVars<Self::Sort>) -> Result<(), Self::Error> {
        Ok(())
    }
    fn end_lambda(&mut self, _scope: (), _body: ()) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_match(&mut self, _scrutinee: &Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }
    fn start_match_case(
        &mut self,
        _scrutinee: &Self::Term,
        _pattern: SmtPatternBuf,
    ) -> Result<Self::Scope, Self::Error> {
        Ok(())
    }
    fn end_match_case(
        &mut self,
        _scope: Self::Scope,
        _scrutinee: &Self::Term,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error> {
        Ok(body)
    }
    fn end_match(
        &mut self,
        _scrutinee: Self::Term,
        _cases: MatchCases<Self::Term>,
    ) -> Result<Self::Term, Self::Error> {
        Ok(())
    }
}

impl CommandHandler for Recording {
    fn nonstandard_command(
        &mut self,
        name: SmtSymbolBuf,
    ) -> Result<NonstandardPayload, Self::Error> {
        match name.as_slice() {
            b"my-assert" => Ok(NonstandardPayload::Term),
            b"my-version-2.0" => {
                self.commands.push("my-version-2.0");
                Ok(NonstandardPayload::SwitchVersion(SmtVersion::V2_0))
            }
            b"my-discard" => {
                self.commands.push("my-discard");
                Ok(NonstandardPayload::DiscardRest)
            }
            _ => Err(SmtNonstandardCommandError::new(name)),
        }
    }

    fn nonstandard_term(&mut self, _term: ()) -> Result<(), Self::Error> {
        self.commands.push("my-assert");
        Ok(())
    }

    fn command_echo(&mut self, _value: SmtStringContentBuf) -> Result<(), Self::Error> {
        self.commands.push("echo");
        Ok(())
    }
    fn command_get_option(&mut self, _option: SmtKeywordBuf) -> Result<(), Self::Error> {
        self.commands.push("get-option");
        Ok(())
    }
    fn command_set_option(&mut self, _option: ()) -> Result<(), Self::Error> {
        self.commands.push("set-option");
        Ok(())
    }
    fn command_get_info(&mut self, _keyword: SmtKeywordBuf) -> Result<(), Self::Error> {
        self.commands.push("get-info");
        Ok(())
    }
    fn command_set_info(&mut self, _attribute: ()) -> Result<(), Self::Error> {
        self.commands.push("set-info");
        Ok(())
    }
    fn command_set_logic(&mut self, _logic: SmtSymbolBuf) -> Result<(), Self::Error> {
        self.commands.push("set-logic");
        Ok(())
    }
    fn command_get_value(&mut self, _terms: Vec<()>) -> Result<(), Self::Error> {
        self.commands.push("get-value");
        Ok(())
    }
    fn command_get_assertions(&mut self) -> Result<(), Self::Error> {
        self.commands.push("get-assertions");
        Ok(())
    }
    fn command_get_assignment(&mut self) -> Result<(), Self::Error> {
        self.commands.push("get-assignment");
        Ok(())
    }
    fn command_get_model(&mut self) -> Result<(), Self::Error> {
        self.commands.push("get-model");
        Ok(())
    }
    fn command_get_proof(&mut self) -> Result<(), Self::Error> {
        self.commands.push("get-proof");
        Ok(())
    }
    fn command_get_unsat_assumptions(&mut self) -> Result<(), Self::Error> {
        self.commands.push("get-unsat-assumptions");
        Ok(())
    }
    fn command_get_unsat_core(&mut self) -> Result<(), Self::Error> {
        self.commands.push("get-unsat-core");
        Ok(())
    }
    fn command_declare_sort(
        &mut self,
        _name: SmtSymbolBuf,
        _arity: SmtNumeralBuf,
    ) -> Result<(), Self::Error> {
        self.commands.push("declare-sort");
        Ok(())
    }
    fn command_declare_sort_parameter(&mut self, _name: SmtSymbolBuf) -> Result<(), Self::Error> {
        self.commands.push("declare-sort-parameter");
        Ok(())
    }
    fn command_declare_fun(
        &mut self,
        _name: SmtSymbolBuf,
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
    fn command_check_sat_assuming(&mut self, _assumptions: Vec<()>) -> Result<(), Self::Error> {
        self.commands.push("check-sat-assuming");
        Ok(())
    }
    fn command_declare_const(&mut self, _name: SmtSymbolBuf, _sort: ()) -> Result<(), Self::Error> {
        self.commands.push("declare-const");
        Ok(())
    }
    fn command_define_const(
        &mut self,
        _name: SmtSymbolBuf,
        _sort: (),
        _body: (),
    ) -> Result<(), Self::Error> {
        self.commands.push("define-const");
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
    fn command_push(&mut self, _amount: SmtNumeralBuf) -> Result<(), Self::Error> {
        self.commands.push("push");
        Ok(())
    }
    fn command_pop(&mut self, _amount: SmtNumeralBuf) -> Result<(), Self::Error> {
        self.commands.push("pop");
        Ok(())
    }
    fn start_define_sort(
        &mut self,
        _name: SmtSymbolBuf,
        _params: Symbols,
    ) -> Result<(), Self::Error> {
        self.commands.push("start-define-sort");
        Ok(())
    }
    fn end_define_sort(&mut self, _sort: ()) -> Result<(), Self::Error> {
        self.commands.push("end-define-sort");
        Ok(())
    }
    fn start_define_fun(&mut self, _signature: Signature<'_, ()>) -> Result<(), Self::Error> {
        self.commands.push("start-define-fun");
        Ok(())
    }
    fn end_define_fun(&mut self, _term: ()) -> Result<(), Self::Error> {
        self.commands.push("end-define-fun");
        Ok(())
    }
    fn start_define_funs_rec(
        &mut self,
        _signatures: Signatures<'_, ()>,
    ) -> Result<(), Self::Error> {
        self.commands.push("start-define-funs-rec");
        Ok(())
    }
    fn start_recursive_body(&mut self, _signature: Signature<'_, ()>) -> Result<(), Self::Error> {
        self.commands.push("start-recursive-body");
        Ok(())
    }
    fn end_recursive_body(&mut self, _term: ()) -> Result<(), Self::Error> {
        self.commands.push("end-recursive-body");
        Ok(())
    }
    fn end_define_funs_rec(&mut self) -> Result<(), Self::Error> {
        self.commands.push("end-define-funs-rec");
        Ok(())
    }
    fn start_define_fun_rec(&mut self, _signature: Signature<'_, ()>) -> Result<(), Self::Error> {
        self.commands.push("start-define-fun-rec");
        Ok(())
    }
    fn end_define_fun_rec(&mut self, _body: ()) -> Result<(), Self::Error> {
        self.commands.push("end-define-fun-rec");
        Ok(())
    }
    fn start_declare_datatype(
        &mut self,
        _name: SmtSymbolBuf,
        _params: Symbols,
    ) -> Result<(), Self::Error> {
        self.commands.push("start-declare-datatype");
        Ok(())
    }
    fn end_declare_datatype(&mut self, _constructors: Constructors<()>) -> Result<(), Self::Error> {
        self.commands.push("end-declare-datatype");
        Ok(())
    }
    fn start_declare_datatypes(
        &mut self,
        _sort_declarations: SortArities,
    ) -> Result<(), Self::Error> {
        self.commands.push("start-declare-datatypes");
        Ok(())
    }
    fn start_datatype_declaration(&mut self, _params: Symbols) -> Result<(), Self::Error> {
        self.commands.push("start-datatype");
        Ok(())
    }
    fn end_datatype_declaration(
        &mut self,
        _constructors: Constructors<()>,
    ) -> Result<(), Self::Error> {
        self.commands.push("end-datatype");
        Ok(())
    }
    fn end_declare_datatypes(&mut self) -> Result<(), Self::Error> {
        self.commands.push("end-declare-datatypes");
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
          (push 1) (pop 1) (reset) (reset-assertions)",
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
            "push",
            "pop",
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
fn define_sort_start_and_end_surround_the_body() {
    let mut handler = Recording::default();
    parse_with(
        &mut handler,
        b"(define-sort S (X) (Array X Int)) (check-sat)",
    )
    .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    assert_eq!(
        handler.commands,
        ["start-define-sort", "end-define-sort", "check-sat"]
    );
}

#[test]
fn declare_datatypes_callbacks_surround_each_datatype() {
    let mut handler = Recording::default();
    parse_with(
        &mut handler,
        b"(declare-datatypes ((A 0) (B 1)) (((a)) (par (X) ((b (v X)))))) (check-sat)",
    )
    .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    assert_eq!(
        handler.commands,
        [
            "start-declare-datatypes",
            "start-datatype",
            "end-datatype",
            "start-datatype",
            "end-datatype",
            "end-declare-datatypes",
            "check-sat",
        ]
    );
}

#[test]
fn declare_datatype_has_calls_of_its_own() {
    let mut handler = Recording::default();
    parse_with(&mut handler, b"(declare-datatype A ((a))) (check-sat)")
        .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    assert_eq!(
        handler.commands,
        [
            "start-declare-datatype",
            "end-declare-datatype",
            "check-sat"
        ]
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
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // a malformed body is a parser error on the offending token
    let mut handler = Recording::default();
    let err = parse_with(&mut handler, b"(my-assert )").expect_err("expected a parser error");
    assert_error_span(&err, 11, 12);
    match err.cause() {
        ReadErrorCause::Syntax(SmtSyntaxErrorKind::Expected([SmtSyntaxExpected::Term])) => {}
        ReadErrorCause::Syntax(kind) => panic!("unexpected parser error {kind:?}"),
        ReadErrorCause::Handler(_) => panic!("unexpected handler error"),
        _ => panic!("unexpected error kind"),
    }
    assert!(handler.commands.is_empty());
}

#[test]
fn nonstandard_command_unknown_to_handler_is_rejected() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    let mut handler = Recording::default();
    let err =
        parse_with(&mut handler, b"(my-assert x) (other)").expect_err("expected a handler error");
    assert_error_span(&err, 15, 20);
    match err.cause() {
        ReadErrorCause::Handler(err) => {
            let name = err.name();
            assert_eq!(name.as_slice(), b"other");
        }
        ReadErrorCause::Syntax(kind) => {
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
fn a_rejected_version_declaration_is_handled_as_set_info_first() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // a version declaration is a set-info command: the handler receives it
    // at its closing parenthesis, and only then is the declared value checked,
    // so the error comes after command_set_info, at that parenthesis
    for value in [
        // a decimal that names no version
        "2.8", // a version the default posture does not allow
        "2.0",
    ] {
        let input = format!("(check-sat)(set-info :smt-lib-version {value})");
        let mut handler = Recording::default();
        let err = parse_with(&mut handler, input.as_bytes())
            .expect_err("the declared version must be rejected");
        assert!(
            matches!(
                err.cause(),
                ReadErrorCause::Version(SmtVersionErrorKind::Unsupported)
            ),
            "{value}: {:?}",
            err.cause()
        );
        let close = input.len() as u64 - 1;
        assert_error_span(&err, close, close + 1);
        assert_eq!(handler.commands, ["check-sat", "set-info"], "{value}");
    }
}

#[test]
fn everything_after_exit_is_discarded() {
    // after (exit), reading stops: the rest of the input is not even lexed,
    // so garbage and unbalanced parentheses there raise no error
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

#[test]
fn define_funs_rec_callbacks_surround_each_body() {
    let mut handler = Recording::default();
    parse_with(
        &mut handler,
        b"(define-funs-rec ((f ((x Int)) Int) (g () Bool)) (x (f 1))) (check-sat)",
    )
    .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    assert_eq!(
        handler.commands,
        [
            "start-define-funs-rec",
            "start-recursive-body",
            "end-recursive-body",
            "start-recursive-body",
            "end-recursive-body",
            "end-define-funs-rec",
            "check-sat",
        ]
    );
}

#[test]
fn define_fun_rec_has_calls_of_its_own() {
    // the body is a term between the start and the end, with no body calls
    let mut handler = Recording::default();
    parse_with(
        &mut handler,
        b"(define-fun-rec f ((x Int)) Int (f x)) (check-sat)",
    )
    .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    assert_eq!(
        handler.commands,
        ["start-define-fun-rec", "end-define-fun-rec", "check-sat"]
    );
}

#[test]
fn no_end_call_comes_before_a_missing_closing_parenthesis() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // each input has a stray token where a closing parenthesis belongs;
    // the definition or declaration it closes is not ended before the error
    let cases: [(&[u8], u64, u64, &[&str]); 9] = [
        (
            b"(define-sort S () Int Int)",
            22,
            25,
            &["start-define-sort"],
        ),
        // define-const has a single call, at its `)`
        (b"(define-const c Int 1 2)", 22, 23, &[]),
        (b"(define-fun f () Int 1 2)", 23, 24, &["start-define-fun"]),
        (
            b"(define-fun-rec f () Int 1 2)",
            27,
            28,
            &["start-define-fun-rec"],
        ),
        (
            b"(define-funs-rec ((f () Int)) (1) 2)",
            34,
            35,
            &[
                "start-define-funs-rec",
                "start-recursive-body",
                "end-recursive-body",
            ],
        ),
        (
            b"(declare-datatypes ((A 0)) (((a))) x)",
            35,
            36,
            &["start-declare-datatypes", "start-datatype", "end-datatype"],
        ),
        (
            b"(declare-datatype A ((a)) x)",
            26,
            27,
            &["start-declare-datatype"],
        ),
        // a parametric datatype is not ended before the parenthesis closing the par
        (
            b"(declare-datatypes ((A 1)) ((par (X) ((a)) x)))",
            43,
            44,
            &["start-declare-datatypes", "start-datatype"],
        ),
        (
            b"(declare-datatype A (par (X) ((a)) x))",
            35,
            36,
            &["start-declare-datatype"],
        ),
    ];
    for (input, start, end, calls) in cases {
        let mut handler = Recording::default();
        let err = parse_with(&mut handler, input).expect_err("expected a parser error");
        assert_error_span(&err, start, end);
        assert!(
            matches!(
                err.cause(),
                ReadErrorCause::Syntax(SmtSyntaxErrorKind::Expected([SmtSyntaxExpected::Token(
                    SmtTokenCategory::ParenClose
                )]))
            ),
            "{:?} in {:?}",
            err.cause(),
            String::from_utf8_lossy(input)
        );
        assert_eq!(
            handler.commands,
            calls,
            "calls in {:?}",
            String::from_utf8_lossy(input)
        );
    }
}

#[test]
fn recursive_body_terms_are_handled_between_the_start_and_end_of_their_body() {
    let mut handler = Recording {
        records_terms_and_attributes: true,
        ..Recording::default()
    };
    parse_with(
        &mut handler,
        b"(define-funs-rec ((f () Int) (g ((x Int)) Int)) (1 (+ x 2))) \
          (define-fun-rec h () Int (let ((y 1)) y))",
    )
    .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    assert_eq!(
        handler.commands,
        [
            "start-define-funs-rec",
            // a body of one token
            "start-recursive-body",
            "term",
            "end-recursive-body",
            // a compound body
            "start-recursive-body",
            "term",
            "term",
            "term",
            "end-recursive-body",
            "end-define-funs-rec",
            // a body binding a variable, through define-fun-rec,
            // whose body is a term between its start and its end
            "start-define-fun-rec",
            "term",
            "term",
            "end-define-fun-rec",
        ]
    );
}

#[test]
fn define_funs_rec_makes_no_call_for_a_missing_or_an_extra_body() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // the input, the error span and kind, and the calls made before the error
    type Case = (
        &'static [u8],
        u64,
        u64,
        SmtSyntaxErrorKind,
        &'static [&'static str],
    );
    let cases: [Case; 2] = [
        // too few bodies: the shortfall is found at the closing parenthesis
        // of the bodies, and no start is made for the missing body
        (
            b"(define-funs-rec ((f () Int) (g () Int)) (1))",
            43,
            44,
            SmtSyntaxErrorKind::Missing(SmtMissingItem::FunctionBody),
            &[
                "start-define-funs-rec",
                "start-recursive-body",
                "end-recursive-body",
            ],
        ),
        // too many bodies: the excess is found at the first token of the extra body,
        // and no start is made for it
        (
            b"(define-funs-rec ((f () Int)) (1 2))",
            33,
            34,
            SmtSyntaxErrorKind::Expected(&[SmtSyntaxExpected::Token(SmtTokenCategory::ParenClose)]),
            &[
                "start-define-funs-rec",
                "start-recursive-body",
                "end-recursive-body",
            ],
        ),
    ];
    for (input, start, end, kind, calls) in cases {
        let mut handler = Recording::default();
        let err = parse_with(&mut handler, input).expect_err("expected a parser error");
        assert_error_span(&err, start, end);
        match err.into_cause() {
            ReadErrorCause::Syntax(actual) => {
                assert_eq!(actual, kind, "in {:?}", String::from_utf8_lossy(input))
            }
            _ => panic!(
                "expected a parser error in {:?}",
                String::from_utf8_lossy(input)
            ),
        }
        assert_eq!(
            handler.commands,
            calls,
            "calls in {:?}",
            String::from_utf8_lossy(input)
        );
    }
}

#[test]
fn a_second_option_or_info_attribute_is_rejected_before_the_first_is_handled() {
    if parse_backend::consumer_spans_not_applicable() {
        return;
    }
    // a valueless attribute is ended by the next token; in set-option and set-info
    // a second keyword is rejected at once, so the first is not handled
    for (input, start, end) in [
        (&b"(set-option :a :b)"[..], 15, 17),
        (&b"(set-info :a :b)"[..], 13, 15),
    ] {
        let mut handler = Recording {
            records_terms_and_attributes: true,
            ..Recording::default()
        };
        let err = parse_with(&mut handler, input).expect_err("expected a parser error");
        assert_error_span(&err, start, end);
        assert!(
            matches!(
                err.cause(),
                ReadErrorCause::Syntax(SmtSyntaxErrorKind::Expected([SmtSyntaxExpected::Token(
                    SmtTokenCategory::ParenClose
                )]))
            ),
            "{:?} in {:?}",
            err.cause(),
            String::from_utf8_lossy(input)
        );
        assert!(
            handler.commands.is_empty(),
            "calls {:?} in {:?}",
            handler.commands,
            String::from_utf8_lossy(input)
        );
    }
}

#[test]
fn get_value_reaches_its_handler_method() {
    let mut handler = Recording::default();
    parse_with(&mut handler, b"(get-value (x (f y))) (check-sat)")
        .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    assert_eq!(handler.commands, ["get-value", "check-sat"]);
}

#[test]
fn argument_free_queries_reach_their_handler_methods() {
    let mut handler = Recording::default();
    parse_with(
        &mut handler,
        b"(get-assertions) (get-assignment) (get-model) (get-proof) \
          (get-unsat-assumptions) (get-unsat-core) (check-sat)",
    )
    .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    assert_eq!(
        handler.commands,
        [
            "get-assertions",
            "get-assignment",
            "get-model",
            "get-proof",
            "get-unsat-assumptions",
            "get-unsat-core",
            "check-sat",
        ]
    );
}

/// A recording handler that also records the versions it is set to.
fn recording_versions() -> Recording {
    Recording {
        records_versions: true,
        ..Recording::default()
    }
}

#[test]
fn the_handler_is_told_the_version_before_anything_else_in_each_input() {
    let mut handler = recording_versions();
    {
        // a reader starting in a version other than the default
        let mut reader =
            Reader::script(&mut handler, SmtVersionPosture::default(), SmtVersion::V2_6);
        reader
            .read_all(&b"(check-sat) (check-sat)"[..])
            .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
        // an empty input is told the version too
        reader
            .read_all(&b""[..])
            .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
        reader
            .read_all(&b"(exit)"[..])
            .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    }
    assert_eq!(
        handler.commands,
        [
            "set-version 2.6",
            "check-sat",
            "check-sat",
            "set-version 2.6",
            "set-version 2.6",
            "exit",
        ]
    );
}

#[test]
fn a_version_declaration_sets_the_handler_after_the_command() {
    let mut handler = recording_versions();
    parse_with(
        &mut handler,
        b"(check-sat) (set-info :smt-lib-version 2.6) (check-sat)",
    )
    .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    assert_eq!(
        handler.commands,
        [
            "set-version 2.7",
            "check-sat",
            "set-info",
            "set-version 2.6",
            "check-sat",
        ]
    );
}

#[test]
fn a_command_parser_outside_a_script_switches_nothing() {
    let mut handler = recording_versions();
    let outcome = {
        let mut reader = Reader::new(&mut handler, CommandParser, SmtVersion::V2_7);
        reader
            .read_all(&b"(set-info :smt-lib-version 2.6)"[..])
            .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()))
    };
    assert!(
        matches!(outcome, SmtCommandOutcome::SetVersion(SmtVersion::V2_6)),
        "{outcome:?}"
    );
    // only the version in force at the start of the input
    assert_eq!(handler.commands, ["set-version 2.7", "set-info"]);
}

// --- What a nonstandard parser may do with the cursor ---
//
// The command parser hands the parser of a nonstandard command the cursor it
// holds, and the script parser does not check what that parser does with it.

/// Reads the input as a script in two pieces, split at the offset, then the
/// end of the input. Returns the version in force after each piece, the
/// location where discarding began after each piece and the location of the
/// end.
fn read_split(
    handler: &mut Recording,
    input: &[u8],
    at: usize,
) -> (
    [(SmtVersion, Option<parse_backend::Location>); 2],
    parse_backend::Location,
) {
    let (first, second) = input.split_at(at);
    let mut reader = Reader::script(handler, SmtVersionPosture::default(), SmtVersion::V2_7);
    let mut after = Vec::new();
    for piece in [first, second] {
        reader
            .read_slice(piece)
            .unwrap_or_else(|err| panic!("error {:?} at {:?}", err.cause(), err.span()));
        after.push((reader.version(), reader.discarded_from()));
    }
    let end = reader
        .read_eof()
        .unwrap_or_else(|err| panic!("error {:?} at {:?}", err.cause(), err.span()));
    assert_eq!(
        reader.version(),
        SmtVersion::V2_7,
        "the end resets the version"
    );
    assert_eq!(
        reader.discarded_from(),
        None,
        "the end resets the discarding"
    );
    (
        after.try_into().expect("two pieces were read"),
        end.location(),
    )
}

#[test]
fn a_nonstandard_parser_may_switch_the_version_unchecked() {
    // the parser of `(my-version-2.0)` switches the cursor to 2.0 after its
    // closing parenthesis: the commands after it are read under 2.0, where
    // `lambda` is a symbol and a backslash escapes a quote in a string,
    // although the default posture does not allow 2.0; the switch is no
    // declaration, so the one declaration the posture allows is still
    // available; and the handler is not told the version
    let input: &[u8] = b"(my-version-2.0)(declare-fun lambda () Bool)(set-option :x \"a\\\"b\")\
        (set-info :smt-lib-version 2.6)(assert lambda)";
    let switched = b"(my-version-2.0)".len();
    let declaration = b"(set-info :smt-lib-version 2.6)";
    let declared = input
        .windows(declaration.len())
        .position(|window| window == declaration)
        .expect("the input declares a version")
        + declaration.len();
    for at in 0..=input.len() {
        let mut handler = recording_versions();
        let (after, _) = read_split(&mut handler, input, at);
        assert_eq!(
            handler.commands,
            [
                "set-version 2.7",
                "my-version-2.0",
                "declare-fun",
                "set-option",
                "set-info",
                "set-version 2.6",
                "assert",
            ],
            "split at {at}"
        );
        let first = if at < switched {
            SmtVersion::V2_7
        } else if at < declared {
            SmtVersion::V2_0
        } else {
            SmtVersion::V2_6
        };
        assert_eq!(
            after,
            [(first, None), (SmtVersion::V2_6, None)],
            "split at {at}"
        );
    }
}

#[test]
fn a_nonstandard_parser_may_discard_the_rest() {
    // the parser of `(my-discard)` has the cursor discard the rest of the
    // input after its closing parenthesis: nothing after it is read, not even
    // lexed, and the script ends at the end of the input, located where the
    // discarding began
    let input: &[u8] = b"(my-assert x)(my-discard) x ) ( 1 (check-sat \"open";
    let discarded = b"(my-assert x)(my-discard)".len() as u64;
    for at in 0..=input.len() {
        let mut handler = Recording::default();
        let (after, end) = read_split(&mut handler, input, at);
        assert_eq!(
            handler.commands,
            ["my-assert", "my-discard"],
            "split at {at}"
        );
        let from = parse_backend::Location::new(discarded, 0, discarded);
        let first = (at >= discarded as usize).then_some(from);
        assert_eq!(
            after,
            [(SmtVersion::V2_7, first), (SmtVersion::V2_7, Some(from))],
            "split at {at}"
        );
        assert_eq!(end, from, "split at {at}");
    }
}

// --- A token-observing consumer built by a user ---
//
// The library offers no handler that receives whitespace and comments: a user
// who needs them (a formatter that keeps comments, for one) builds a concrete
// consumer of their own, which observes every token and hands the others to a
// parser one at a time. These tests check that the public interface allows
// it: the consumer below uses nothing a user cannot write. They check the
// Rust interface itself, so they run the Rust library whatever
// `parse_backend` selects, with the test handler behind its Rust adapter.

/// A producer offering the parser one token of another producer, with no
/// lookahead, and forwarding the version and the discarding to it.
struct OneToken<'z, Z> {
    inner: &'z mut Z,
    taken: bool,
}

impl<Z: SmtCursor> SmtCursor for OneToken<'_, Z> {
    type Token = Z::Token;
    type Lookahead = ();

    fn syntax<'t>(&self, token: &'t Z::Token) -> SmtSyntaxToken<'t> {
        self.inner.syntax(token)
    }

    fn next(&mut self) -> Option<Z::Token> {
        if self.taken {
            return None;
        }
        let token = self.inner.next()?;
        self.taken = true;
        Some(token)
    }

    fn peek(&self) -> Option<Z::Token> {
        if self.taken { None } else { self.inner.peek() }
    }

    fn version(&self) -> SmtVersion {
        self.inner.version()
    }

    fn set_version(&mut self, version: SmtVersion) -> Result<(), SmtVersionRefused> {
        self.inner.set_version(version)
    }

    fn discard_rest(&mut self) {
        self.inner.discard_rest()
    }
}

/// A concrete consumer that records the span of every token handed over,
/// records each comment in the handler's log as `comment`, and parses a
/// script from the other tokens.
struct Observing<'h> {
    handler: Adapt<'h, Recording>,
    parse_state: SmtParseState<Adapt<'h, Recording>>,
    parser: SmtScriptParser<Adapt<'h, Recording>>,
    version_set: bool,
    spans: Vec<SmtSpan>,
}

impl SmtConsume for Observing<'_> {
    type Result = ();
    type Error = SmtParseError<SmtNonstandardCommandError>;
    const IS_CONCRETE: bool = true;
}

impl<'a> SmtConsumeFrom<SmtBatchCursor<'a>> for Observing<'_> {
    fn consume(&mut self, cursor: &mut SmtBatchCursor<'a>) -> Result<ControlFlow<()>, Self::Error> {
        // the handler learns the version at the start of every input
        if !self.version_set {
            self.handler.set_version(cursor.version());
            self.version_set = true;
        }
        while let Some(token) = cursor.peek() {
            self.spans.push(token.span());
            match cursor.syntax(&token) {
                SmtSyntaxToken::Whitespace(_) => {
                    cursor.next();
                    continue;
                }
                SmtSyntaxToken::Comment(_) => {
                    self.handler.0.commands.push("comment");
                    cursor.next();
                    continue;
                }
                _ => {}
            }
            let mut one = OneToken {
                inner: &mut *cursor,
                taken: false,
            };
            let flow = self
                .parser
                .parse(&mut self.handler, &mut self.parse_state, &mut one)?;
            if flow.is_break() {
                self.version_set = false;
                return Ok(flow);
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// A posture that allows a switch from 2.7 to 2.0.
fn posture_with_2_0() -> SmtVersionPosture {
    let mut builder = SmtVersionPostureBuilder::new();
    builder.add_allowed(SmtVersion::V2_0);
    builder.build()
}

#[test]
fn a_user_built_consumer_observes_every_token_and_parses_the_rest() {
    // the string is lexed differently in 2.0, where `\"` is an escape, so the
    // switch must reach the lexer; the input after (exit) is discarded
    let input = b"; header\n(set-info :smt-lib-version 2.0) ; switch\n\
        (set-info :source \"a\\\" b\")\n(assert (and x ; inside\n  true))\n\
        ; before exit\n(exit) x ) ( 1 (check-sat";
    let exit_end = input
        .windows(6)
        .position(|window| window == b"(exit)")
        .expect("the input has an exit")
        + 6;

    let mut plain = Recording {
        records_terms_and_attributes: true,
        records_versions: true,
        ..Recording::default()
    };
    SmtReader::script(&mut Adapt(&mut plain), posture_with_2_0(), SmtVersion::V2_7)
        .read_all(&input[..])
        .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));

    let mut observed = Recording {
        records_terms_and_attributes: true,
        records_versions: true,
        ..Recording::default()
    };
    let mut lexer = SmtLexer::new(
        Observing {
            handler: Adapt(&mut observed),
            parse_state: SmtParseState::new(),
            parser: SmtScriptParser::new(posture_with_2_0()),
            version_set: false,
            spans: Vec::new(),
        },
        SmtVersion::V2_7,
    );
    lexer
        .lex_all(input)
        .unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
    let spans = std::mem::take(&mut lexer.consumer_mut().spans);
    drop(lexer);

    // the tokens observed tile the input up to the exit, then the end of input
    let (eof, tokens) = spans.split_last().expect("the end of input is observed");
    let mut offset = 0;
    for span in tokens {
        assert_eq!(
            span.start().offset(),
            offset,
            "a gap or overlap at {span:?}"
        );
        offset = span.end().offset();
    }
    assert_eq!(offset, exit_end as u64, "the tokens end at the exit");
    assert_eq!(eof.start().offset(), eof.end().offset(), "{eof:?}");

    // the calls are those of the library's own adapter, with the comments
    // observed in their places among them
    assert_eq!(
        observed.commands,
        [
            "set-version 2.7",
            "comment",
            "attribute",
            "set-info",
            "set-version 2.0",
            "comment",
            "attribute",
            "set-info",
            "term",
            "comment",
            "term",
            "term",
            "assert",
            "comment",
            "exit",
        ]
    );
    let without_comments: Vec<_> = observed
        .commands
        .iter()
        .copied()
        .filter(|call| *call != "comment")
        .collect();
    assert_eq!(without_comments, plain.commands);
}

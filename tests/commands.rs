//! Public-API tests of the standard commands: define-fun callback ordering,
//! handler errors, and per-command shape errors.

mod common;

use common::{assert_error_span, assert_parser_error, parse_with};

use smt_parser_rs::{
    CommandHandler, SmtAttributeValue, SmtFunctionSignature, SmtHandler, SmtIdent, SmtIndex,
    SmtKeyword, SmtQuantifierKind, SmtSExpr, SmtSort, SmtSpecialConstant, SmtStringContent,
    SmtSymbol, SmtSymbolView, SmtTerm,
    read::{
        SmtReadErrorKind,
        parser::{CategoryParserErrorKind, NoCommandParser},
    },
    token::TokenType,
};

/// Handler that resolves body identifiers against the parameters of the
/// define-fun currently in progress, marking resolved ones as `[name]`.
/// The resolution succeeding proves that `start_define_fun` delivers the
/// signature before the body terms are constructed.
#[derive(Default)]
struct Resolving {
    /// Callbacks received, in order.
    events: Vec<String>,
    /// Parameter names of the define-fun in progress, empty outside one.
    params: Vec<String>,
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).expect("test inputs are ASCII")
}

/// Renders an identifier including its indices, so that stale indices
/// leaking from a previously parsed command would show up in the events.
fn ident_text(ident: &SmtIdent) -> String {
    let name = text(ident.name.as_slice());
    if ident.indices.is_empty() {
        return name;
    }
    let indices: Vec<String> = ident
        .indices
        .iter()
        .map(|index| match index {
            SmtIndex::Numeral(numeral) => text(numeral.as_slice()),
            SmtIndex::Symbol(symbol) => text(symbol.as_slice()),
        })
        .collect();
    format!("(_ {} {})", name, indices.join(" "))
}

impl SmtHandler for Resolving {
    type Error = String;
    type SExpr = ();
    type Attribute = ();
    type Sort = String;
    type Term = String;

    fn handle_sort(&mut self, sort: SmtSort<Self>) -> Result<String, String> {
        let name = ident_text(&sort.ident);
        Ok(if sort.applied.is_empty() {
            name
        } else {
            format!("({} {})", name, sort.applied.join(" "))
        })
    }

    fn handle_term(&mut self, term: SmtTerm<Self>) -> Result<String, String> {
        Ok(match term {
            SmtTerm::SpecialConstant(constant) => match constant {
                SmtSpecialConstant::Numeral(numeral) => text(numeral.as_slice()),
                _ => "<constant>".into(),
            },
            SmtTerm::QualifiedIdent(qualified_ident) => {
                let name = ident_text(&qualified_ident.ident);
                if self.params.contains(&name) {
                    format!("[{name}]")
                } else {
                    name
                }
            }
            SmtTerm::Application(application) => {
                let function = ident_text(&application.function.ident);
                format!("({} {})", function, application.args.join(" "))
            }
        })
    }

    fn start_let(&mut self, _bindings: Vec<(SmtSymbol, String)>) -> Result<(), String> {
        Ok(())
    }

    fn end_let(&mut self, term: String) -> Result<String, String> {
        Ok(term)
    }

    fn handle_s_expr(&mut self, _expr: SmtSExpr<Self>) -> Result<(), String> {
        Ok(())
    }

    fn handle_attribute(
        &mut self,
        _name: SmtKeyword,
        _value: Option<SmtAttributeValue<Self>>,
    ) -> Result<(), String> {
        Ok(())
    }

    fn annotate_term(&mut self, term: String, _attributes: Vec<()>) -> Result<String, String> {
        Ok(term)
    }

    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _name: SmtSymbol,
        _sort: String,
    ) -> Result<(), String> {
        Ok(())
    }
    fn end_quantifier(&mut self, term: String) -> Result<String, String> {
        Ok(term)
    }
    fn start_lambda(&mut self, _name: SmtSymbol, _sort: String) -> Result<(), String> {
        Ok(())
    }
    fn end_lambda(&mut self, term: String) -> Result<String, String> {
        Ok(term)
    }
}

impl CommandHandler for Resolving {
    type NonstandardParser = NoCommandParser;

    fn nonstandard_command(
        &mut self,
        name: SmtSymbolView<'_>,
    ) -> Result<Self::NonstandardParser, String> {
        Err(format!("nonstandard command {:?}", text(name.as_slice())))
    }

    fn command_echo(&mut self, _value: SmtStringContent) -> Result<(), String> {
        Ok(())
    }
    fn command_get_option(&mut self, _option: SmtKeyword) -> Result<(), String> {
        Ok(())
    }
    fn command_set_option(&mut self, _option: ()) -> Result<(), String> {
        Ok(())
    }
    fn command_get_info(&mut self, _keyword: SmtKeyword) -> Result<(), String> {
        Ok(())
    }
    fn command_set_info(&mut self, _attribute: ()) -> Result<(), String> {
        Ok(())
    }
    fn command_set_logic(&mut self, _logic: SmtSymbol) -> Result<(), String> {
        Ok(())
    }
    fn command_declare_fun(
        &mut self,
        name: SmtSymbol,
        param_sorts: Vec<String>,
        result_sort: String,
    ) -> Result<(), String> {
        self.events.push(format!(
            "declare-fun {} ({}) {}",
            text(name.as_slice()),
            param_sorts.join(" "),
            result_sort
        ));
        Ok(())
    }

    fn command_assert(&mut self, term: String) -> Result<(), String> {
        self.events.push(format!("assert {term}"));
        Ok(())
    }

    fn command_check_sat(&mut self, assumptions: Vec<String>) -> Result<(), String> {
        // rendered as plain `check-sat` without assumptions, so that
        // `check-sat` and `(check-sat-assuming ())` are indistinguishable
        self.events.push(if assumptions.is_empty() {
            "check-sat".into()
        } else {
            format!("check-sat ({})", assumptions.join(" "))
        });
        Ok(())
    }

    fn command_reset(&mut self) -> Result<(), String> {
        Ok(())
    }
    fn command_reset_assertions(&mut self) -> Result<(), String> {
        Ok(())
    }
    fn command_exit(&mut self) -> Result<(), String> {
        Ok(())
    }

    fn start_define_fun(&mut self, signature: SmtFunctionSignature<Self>) -> Result<(), String> {
        let name = text(signature.name.as_slice());
        if name == "forbidden" {
            return Err("forbidden function name".into());
        }
        let params: Vec<String> = signature
            .params
            .iter()
            .map(|(param, sort)| format!("({} {})", text(param.as_slice()), sort))
            .collect();
        self.events.push(format!(
            "start {name} ({}) {}",
            params.join(" "),
            signature.result_sort
        ));
        self.params = signature
            .params
            .iter()
            .map(|(param, _)| text(param.as_slice()))
            .collect();
        Ok(())
    }

    fn end_define_fun(&mut self, term: String) -> Result<(), String> {
        if term == "boom" {
            return Err("exploding body".into());
        }
        self.events.push(format!("end {term}"));
        self.params.clear();
        Ok(())
    }
}

#[track_caller]
fn parse_resolving(handler: &mut Resolving, input: &[u8]) {
    parse_with(handler, input).unwrap_or_else(|err| panic!("unexpected error at {:?}", err.span()));
}

#[test]
fn params_resolve_while_body_is_parsed() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(define-fun inc ((x Int)) Int (+ x 1)) (assert x) (check-sat)",
    );
    assert_eq!(
        handler.events,
        [
            // the signature arrives before any body term
            "start inc ((x Int)) Int",
            // `x` was resolved as a parameter while the body was constructed
            "end (+ [x] 1)",
            // the parameter scope ended with the define-fun
            "assert x",
            "check-sat",
        ]
    );
}

#[test]
fn zero_params_and_applied_result_sort() {
    let mut handler = Resolving::default();
    parse_resolving(&mut handler, b"(define-fun c () (Array Int Bool) zero)");
    assert_eq!(handler.events, ["start c () (Array Int Bool)", "end zero"]);
}

#[test]
fn declare_fun_parameter_list() {
    // regression: the parameter list's opening parenthesis must be consumed
    // by the list parser itself, not leak into the first parameter sort
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(declare-fun f (A (Array Int Int)) Bool) (declare-fun g () Int)",
    );
    assert_eq!(
        handler.events,
        [
            "declare-fun f (A (Array Int Int)) Bool",
            "declare-fun g () Int",
        ]
    );
}

// --- Syntax-sugar commands ---
//
// `declare-const`, `define-const` and `check-sat` are abbreviations of
// `declare-fun`, `define-fun` and `check-sat-assuming` respectively, and
// share their handler callbacks. These tests check that the sugar form is
// observationally identical to the spelled-out one, including callback order.

#[test]
fn declare_const_is_declare_fun_without_params() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(declare-const x Int) (declare-fun y () Int) (declare-const a (Array Int Bool))",
    );
    assert_eq!(
        handler.events,
        [
            "declare-fun x () Int",
            "declare-fun y () Int",
            "declare-fun a () (Array Int Bool)",
        ]
    );
}

#[test]
fn define_const_is_define_fun_without_params() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(define-const c Int (+ x 1)) (define-fun d () Int (+ x 1))",
    );
    assert_eq!(
        handler.events,
        [
            "start c () Int",
            "end (+ x 1)",
            "start d () Int",
            "end (+ x 1)",
        ]
    );
}

#[test]
fn define_const_signature_arrives_before_body() {
    // a handler error raised from start_define_fun must prevent the body
    // from being handled at all, exactly as for define-fun
    let handler = assert_handler_error(
        b"(define-const forbidden Int 5)",
        "forbidden function name",
        24,
        27,
    );
    assert!(handler.events.is_empty());
}

#[test]
fn define_const_body_error_points_at_last_body_token() {
    let handler = assert_handler_error(b"(define-const c Int boom)", "exploding body", 20, 24);
    assert_eq!(handler.events, ["start c () Int"]);
}

#[test]
fn define_const_does_not_inherit_previous_scope() {
    // the parameter scope of a preceding define-fun must be closed before
    // the define-const body is constructed
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(define-fun a ((x Int)) Int x) (define-const c Int x) (define-fun b ((x Int)) Int x)",
    );
    assert_eq!(
        handler.events,
        [
            "start a ((x Int)) Int",
            "end [x]",
            "start c () Int",
            "end x",
            "start b ((x Int)) Int",
            "end [x]",
        ]
    );
}

#[test]
fn define_const_errors_point_at_offending_token() {
    // the constant name must be a symbol
    let err = assert_parser_error(b"(define-const 1 Int 5)", 14, 15);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
    // define-const has no parameter list, an empty one is not a sort
    let err = assert_parser_error(b"(define-const c () Int 5)", 17, 18);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedSortInner),
        "{err:?}"
    );
    // the body term is required
    let err = assert_parser_error(b"(define-const c Int)", 19, 20);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedTerm),
        "{err:?}"
    );
    // exactly one body term is allowed
    let err = assert_parser_error(b"(define-const c Int 5 6)", 22, 23);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
}

#[test]
fn check_sat_assuming_passes_assumption_terms() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(check-sat-assuming (a b)) (check-sat-assuming ((not a) (f 1 x)))",
    );
    assert_eq!(
        handler.events,
        ["check-sat (a b)", "check-sat ((not a) (f 1 x))"]
    );
}

#[test]
fn check_sat_is_check_sat_assuming_without_assumptions() {
    let mut handler = Resolving::default();
    parse_resolving(&mut handler, b"(check-sat) (check-sat-assuming ())");
    assert_eq!(handler.events, ["check-sat", "check-sat"]);
}

#[test]
fn repeated_check_sat_assumings_reuse_the_persistent_parser() {
    // assumptions of a previous command must not leak into the next one
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(check-sat-assuming (a b c)) (check-sat) (check-sat-assuming (d)) (check-sat-assuming ())",
    );
    assert_eq!(
        handler.events,
        [
            "check-sat (a b c)",
            "check-sat",
            "check-sat (d)",
            "check-sat"
        ]
    );
}

#[test]
fn check_sat_errors_point_at_offending_token() {
    // check-sat takes no arguments, assumptions need check-sat-assuming
    let err = assert_parser_error(b"(check-sat x)", 11, 12);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
    // the assumption list is required, even when empty
    let err = assert_parser_error(b"(check-sat-assuming)", 19, 20);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
        ),
        "{err:?}"
    );
    // the assumptions must be parenthesized as a list
    let err = assert_parser_error(b"(check-sat-assuming a)", 20, 21);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
        ),
        "{err:?}"
    );
    // nothing may follow the assumption list
    let err = assert_parser_error(b"(check-sat-assuming (a b) extra)", 26, 31);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
    // each assumption must be a term
    let err = assert_parser_error(b"(check-sat-assuming (a :kw))", 23, 26);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedTerm),
        "{err:?}"
    );
}

// --- Parser persistence across commands ---
//
// The command parsers are persistent inside the reader and restarted per
// command, so consecutive commands of the same kind reuse the same parser
// instance (including its category parsers and their buffers). These tests
// record full term and sort content: state leaking from a previous command
// would corrupt the rendered events.

#[test]
fn repeated_asserts_reuse_the_persistent_parser() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(assert ((_ extract 3 0) x)) (assert y) (assert ((_ extract 7 4) (f 1)))",
    );
    assert_eq!(
        handler.events,
        [
            "assert ((_ extract 3 0) x)",
            "assert y",
            "assert ((_ extract 7 4) (f 1))",
        ]
    );
}

#[test]
fn repeated_declare_funs_reuse_the_persistent_parser() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(declare-fun f (Bool (_ BitVec 8)) Int) \
          (declare-fun g ((Array Int Int)) (_ BitVec 4))",
    );
    assert_eq!(
        handler.events,
        [
            "declare-fun f (Bool (_ BitVec 8)) Int",
            "declare-fun g ((Array Int Int)) (_ BitVec 4)",
        ]
    );
}

#[test]
fn repeated_define_funs_reset_signature_and_scope() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(define-fun a ((x Int)) Int (+ x 1)) (define-fun b ((y Bool)) Bool y)",
    );
    assert_eq!(
        handler.events,
        [
            "start a ((x Int)) Int",
            "end (+ [x] 1)",
            "start b ((y Bool)) Bool",
            "end [y]",
        ]
    );
}

#[test]
fn alternating_commands_reuse_their_parsers() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(assert (f 1)) (check-sat) (assert (g 2)) (check-sat)",
    );
    assert_eq!(
        handler.events,
        ["assert (f 1)", "check-sat", "assert (g 2)", "check-sat"]
    );
}

#[test]
fn signature_errors_point_at_offending_token() {
    // the function name must be a symbol
    let err = assert_parser_error(b"(define-fun 1 () Int 5)", 12, 13);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
    // each sorted var must be parenthesized
    let err = assert_parser_error(b"(define-fun f (x Int) Int x)", 15, 16);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
        ),
        "{err:?}"
    );
    // the body term is required
    let err = assert_parser_error(b"(define-fun f () Int)", 20, 21);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedTerm),
        "{err:?}"
    );
    // exactly one body term is allowed
    let err = assert_parser_error(b"(define-fun f () Int 5 6)", 23, 24);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
}

#[track_caller]
fn assert_handler_error(input: &[u8], message: &str, start: u64, end: u64) -> Resolving {
    let mut handler = Resolving::default();
    let err = parse_with(&mut handler, input).expect_err("expected a handler error");
    assert_error_span(&err, start, end);
    match err.kind() {
        SmtReadErrorKind::Handler(handler_message) => assert_eq!(handler_message, message),
        SmtReadErrorKind::Parser(kind) => panic!("expected handler error, got {kind:?}"),
        _ => panic!("expected handler error"),
    }
    handler
}

#[test]
fn start_define_fun_error_points_at_last_signature_token() {
    let handler = assert_handler_error(
        b"(define-fun forbidden () Int 5)",
        "forbidden function name",
        25,
        28,
    );
    assert!(handler.events.is_empty());
}

#[test]
fn end_define_fun_error_points_at_last_body_token() {
    let handler = assert_handler_error(b"(define-fun f () Int boom)", "exploding body", 21, 25);
    assert_eq!(handler.events, ["start f () Int"]);
}

#[test]
fn trivial_command_errors_point_at_offending_token() {
    // echo takes a string literal
    let err = assert_parser_error(b"(echo 1)", 6, 7);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::String])
        ),
        "{err:?}"
    );
    // exactly one string literal
    let err = assert_parser_error(b"(echo \"hi\" \"there\")", 11, 18);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
    // get-option and get-info take a keyword, not a symbol or string
    let err = assert_parser_error(b"(get-option opt)", 12, 15);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(get-info \"x\")", 10, 13);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Keyword])
        ),
        "{err:?}"
    );
    // set-option requires an attribute
    let err = assert_parser_error(b"(set-option)", 11, 12);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedAttribute),
        "{err:?}"
    );
    // reset and reset-assertions take no arguments
    let err = assert_parser_error(b"(reset x)", 7, 8);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(reset-assertions x)", 18, 19);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
}

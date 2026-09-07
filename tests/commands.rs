//! Public-API tests of the standard commands: define-fun callback ordering,
//! handler errors, and per-command shape errors.

mod common;

use common::{assert_error_span, assert_parser_error, parse_with};

use smt_parser_rs::{
    CommandHandler, SmtAttributeValue, SmtDatatypeConstructor, SmtFunctionSignature, SmtHandler,
    SmtIdent, SmtIndex, SmtKeyword, SmtNumeral, SmtQuantifierKind, SmtSExpr, SmtSort,
    SmtSpecialConstant, SmtStringContent, SmtSymbol, SmtSymbolView, SmtTerm,
    read::{
        SmtReadErrorKind,
        lexer::LexerErrorKind,
        parser::{CategoryParserErrorKind, NoCommandParser},
    },
    token::TokenType,
};

/// Handler that resolves body identifiers against the parameters of the
/// define-fun currently in progress, marking resolved ones as `[name]`,
/// and body sorts against the parameters of the define-sort or datatype
/// in progress in the same way. Sorts declared by the declare-datatypes
/// in progress are marked as `<name>`. The resolution succeeding proves
/// that the start callbacks deliver the signature before the body is
/// constructed.
#[derive(Default)]
struct Resolving {
    /// Callbacks received, in order.
    events: Vec<String>,
    /// Parameter names of the define-fun in progress, empty outside one.
    params: Vec<String>,
    /// Parameter names of the define-sort or datatype in progress,
    /// empty outside one.
    sort_params: Vec<String>,
    /// Sort names declared by the declare-datatypes in progress,
    /// in declaration order, empty outside one.
    datatype_sorts: Vec<String>,
    /// Index into `datatype_sorts` of the datatype in progress.
    datatype_index: usize,
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
        let name = if self.sort_params.contains(&name) {
            format!("[{name}]")
        } else if self.datatype_sorts.contains(&name) {
            format!("<{name}>")
        } else {
            name
        };
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
    fn command_declare_sort(&mut self, name: SmtSymbol, arity: SmtNumeral) -> Result<(), String> {
        self.events.push(format!(
            "declare-sort {} {}",
            text(name.as_slice()),
            text(arity.as_slice())
        ));
        Ok(())
    }
    fn command_declare_sort_parameter(&mut self, name: SmtSymbol) -> Result<(), String> {
        self.events
            .push(format!("declare-sort-parameter {}", text(name.as_slice())));
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
    fn command_push(&mut self, amount: SmtNumeral) -> Result<(), String> {
        self.events
            .push(format!("push {}", text(amount.as_slice())));
        Ok(())
    }
    fn command_pop(&mut self, amount: SmtNumeral) -> Result<(), String> {
        self.events.push(format!("pop {}", text(amount.as_slice())));
        Ok(())
    }

    fn start_define_sort(&mut self, name: SmtSymbol, params: Vec<SmtSymbol>) -> Result<(), String> {
        let name = text(name.as_slice());
        if name == "forbidden" {
            return Err("forbidden sort name".into());
        }
        let params: Vec<String> = params.iter().map(|param| text(param.as_slice())).collect();
        self.events
            .push(format!("start-sort {name} ({})", params.join(" ")));
        self.sort_params = params;
        Ok(())
    }

    fn end_define_sort(&mut self, sort: String) -> Result<(), String> {
        if sort == "Boom" {
            return Err("exploding sort".into());
        }
        self.events.push(format!("end-sort {sort}"));
        self.sort_params.clear();
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

    fn start_declare_datatypes(
        &mut self,
        sort_declarations: Vec<(SmtSymbol, SmtNumeral)>,
    ) -> Result<(), String> {
        let mut rendered = Vec::new();
        self.datatype_sorts.clear();
        self.datatype_index = 0;
        for (name, arity) in &sort_declarations {
            let name = text(name.as_slice());
            if name == "Forbidden" {
                return Err("forbidden datatype name".into());
            }
            rendered.push(format!("({} {})", name, text(arity.as_slice())));
            self.datatype_sorts.push(name);
        }
        self.events
            .push(format!("start-datatypes ({})", rendered.join(" ")));
        Ok(())
    }

    fn start_datatype(&mut self, params: Vec<SmtSymbol>) -> Result<(), String> {
        // the datatypes arrive in sort-declaration order, so the handler
        // knows which sort is being started by counting
        let name = self
            .datatype_sorts
            .get(self.datatype_index)
            .cloned()
            .unwrap_or_else(|| panic!("datatype {} started without a sort", self.datatype_index));
        if name == "Unstartable" {
            return Err("unstartable datatype".into());
        }
        let params: Vec<String> = params.iter().map(|param| text(param.as_slice())).collect();
        self.events
            .push(format!("start-datatype ({})", params.join(" ")));
        self.sort_params = params;
        Ok(())
    }

    fn end_datatype(
        &mut self,
        constructors: Vec<SmtDatatypeConstructor<Self>>,
    ) -> Result<(), String> {
        let mut rendered = Vec::new();
        for constructor in &constructors {
            let name = text(constructor.name.as_slice());
            if name == "boom" {
                return Err("exploding constructor".into());
            }
            let selectors: Vec<String> = constructor
                .selectors
                .iter()
                .map(|(selector, sort)| format!("({} {})", text(selector.as_slice()), sort))
                .collect();
            rendered.push(if selectors.is_empty() {
                format!("({name})")
            } else {
                format!("({name} {})", selectors.join(" "))
            });
        }
        self.events
            .push(format!("end-datatype ({})", rendered.join(" ")));
        self.sort_params.clear();
        self.datatype_index += 1;
        Ok(())
    }

    fn end_declare_datatypes(&mut self) -> Result<(), String> {
        if self.datatype_sorts.iter().any(|name| name == "Unendable") {
            return Err("unendable datatypes".into());
        }
        self.events.push("end-datatypes".into());
        // a real handler keeps the sorts; forgetting them here makes
        // the end of the command observable in later events
        self.datatype_sorts.clear();
        self.datatype_index = 0;
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
fn sort_params_resolve_while_body_is_parsed() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(define-sort Pair (X Y) (Tuple X (Array Y Int))) (declare-fun f (X) Y)",
    );
    assert_eq!(
        handler.events,
        [
            // the signature arrives before any body sort
            "start-sort Pair (X Y)",
            // `X` and `Y` were resolved as parameters while the body was constructed
            "end-sort (Tuple [X] (Array [Y] Int))",
            // the parameter scope ended with the define-sort
            "declare-fun f (X) Y",
        ]
    );
}

#[test]
fn define_sort_with_zero_params() {
    let mut handler = Resolving::default();
    parse_resolving(&mut handler, b"(define-sort S () (Array Int Bool))");
    assert_eq!(
        handler.events,
        ["start-sort S ()", "end-sort (Array Int Bool)"]
    );
}

#[test]
fn define_sort_and_define_fun_scopes_are_independent() {
    // the same name is a sort parameter in one command and a term
    // parameter in the next; each must resolve only in its own body
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(define-sort S (X) X) (define-fun f ((X Int)) X X) (define-sort T (Y) (Array Y X))",
    );
    assert_eq!(
        handler.events,
        [
            "start-sort S (X)",
            "end-sort [X]",
            // the sort `X` in the signature and body is no longer a sort parameter
            "start f ((X Int)) X",
            // but the term `X` is a function parameter
            "end [X]",
            "start-sort T (Y)",
            "end-sort (Array [Y] X)",
        ]
    );
}

#[test]
fn start_define_sort_error_points_at_last_signature_token() {
    let handler = assert_handler_error(
        b"(define-sort forbidden () Int)",
        "forbidden sort name",
        24,
        25,
    );
    assert!(handler.events.is_empty());
}

#[test]
fn end_define_sort_error_points_at_last_body_token() {
    let handler = assert_handler_error(b"(define-sort S () Boom)", "exploding sort", 18, 22);
    assert_eq!(handler.events, ["start-sort S ()"]);
}

#[test]
fn define_sort_errors_point_at_offending_token() {
    // the sort name must be a symbol
    let err = assert_parser_error(b"(define-sort 1 () Int)", 13, 14);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
    // the parameter list is required, even when empty
    let err = assert_parser_error(b"(define-sort S Int)", 15, 18);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
        ),
        "{err:?}"
    );
    // the parameters are bare symbols, not sorted vars or numerals
    let err = assert_parser_error(b"(define-sort S ((X)) Int)", 16, 17);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(define-sort S (X 1) Int)", 18, 19);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
    // the body sort is required
    let err = assert_parser_error(b"(define-sort S ())", 17, 18);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedSort),
        "{err:?}"
    );
    // exactly one body sort is allowed
    let err = assert_parser_error(b"(define-sort S () Int Bool)", 22, 26);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
}

#[test]
fn push_and_pop_deliver_unconverted_amounts() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(push 1) (assert x) (pop 1) (push 0) (pop 0) (push 99999999999999999999999)",
    );
    assert_eq!(
        handler.events,
        [
            "push 1",
            "assert x",
            "pop 1",
            // zero is a valid amount
            "push 0",
            "pop 0",
            // the amount is passed through as the numeral text, however large
            "push 99999999999999999999999",
        ]
    );
}

#[test]
fn push_and_pop_errors_point_at_offending_token() {
    // the amount is required
    let err = assert_parser_error(b"(push)", 5, 6);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Numeral])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(pop)", 4, 5);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Numeral])
        ),
        "{err:?}"
    );
    // the amount must be a numeral
    let err = assert_parser_error(b"(push x)", 6, 7);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Numeral])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(pop 1.0)", 5, 8);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Numeral])
        ),
        "{err:?}"
    );
    // exactly one amount
    let err = assert_parser_error(b"(push 1 2)", 8, 9);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(pop 1 2)", 7, 8);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
}

#[test]
fn declare_sort_delivers_name_and_unconverted_arity() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(declare-sort U 0) (declare-sort |Quoted Sort| 12) \
          (declare-sort-parameter T) (declare-fun f (U) T)",
    );
    assert_eq!(
        handler.events,
        [
            "declare-sort U 0",
            // the arity is passed through as the numeral text
            "declare-sort Quoted Sort 12",
            "declare-sort-parameter T",
            "declare-fun f (U) T",
        ]
    );
}

#[test]
fn declare_sort_errors_point_at_offending_token() {
    // the sort name must be a symbol
    let err = assert_parser_error(b"(declare-sort 1 0)", 14, 15);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
    // the arity is required
    let err = assert_parser_error(b"(declare-sort U)", 15, 16);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Numeral])
        ),
        "{err:?}"
    );
    // the arity must be a numeral, not a decimal or another constant
    let err = assert_parser_error(b"(declare-sort U 1.5)", 16, 19);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Numeral])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(declare-sort U #x0)", 16, 19);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Numeral])
        ),
        "{err:?}"
    );
    // exactly one arity
    let err = assert_parser_error(b"(declare-sort U 0 0)", 18, 19);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
}

#[test]
fn declare_sort_leading_zero_arity_is_rejected_by_lexer() {
    // a numeral with leading zeros is not a numeral at all,
    // so this never reaches the command parser
    let err = parse_with(&mut Resolving::default(), b"(declare-sort U 007)")
        .expect_err("expected a lexer error");
    // the lexer reports the error as soon as a digit follows the leading zero
    assert_error_span(&err, 16, 18);
    match err.kind() {
        SmtReadErrorKind::Lexer(LexerErrorKind::NumeralLeadingZero) => {}
        kind => panic!("expected a leading zero lexer error, got {kind:?}"),
    }
}

#[test]
fn declare_sort_parameter_errors_point_at_offending_token() {
    // the parameter name is required and must be a symbol
    let err = assert_parser_error(b"(declare-sort-parameter)", 23, 24);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(declare-sort-parameter 1)", 24, 25);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
    // exactly one parameter per command
    let err = assert_parser_error(b"(declare-sort-parameter T U)", 26, 27);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
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

// --- declare-datatypes ---
//
// The command streams: the sort declarations arrive first, so that the
// handler knows the declared sort symbols before any selector sort is
// constructed (the recursive references below resolve as `<name>`), and
// each datatype's parameters arrive before its constructors (parameters
// resolve as `[name]` inside the selector sorts of that datatype only).

#[test]
fn datatype_callbacks_deliver_sorts_and_params_before_selector_sorts() {
    // the spec's mutually recursive Tree / TreeList example
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(declare-datatypes ((Tree 1) (TreeList 1)) \
            ((par (X) ((node (value X) (children (TreeList X))))) \
             (par (Y) ((empty) (insert (head (Tree Y)) (tail (TreeList Y)))))))",
    );
    assert_eq!(
        handler.events,
        [
            "start-datatypes ((Tree 1) (TreeList 1))",
            "start-datatype (X)",
            // `TreeList` was declared before this selector sort was constructed,
            // and `X` is the parameter of this datatype
            "end-datatype ((node (value [X]) (children (<TreeList> [X]))))",
            "start-datatype (Y)",
            "end-datatype ((empty) (insert (head (<Tree> [Y])) (tail (<TreeList> [Y]))))",
            "end-datatypes",
        ]
    );
}

#[test]
fn enumeration_datatype_has_nullary_constructors() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(declare-datatypes ((Color 0)) (((red) (green) (blue))))",
    );
    assert_eq!(
        handler.events,
        [
            "start-datatypes ((Color 0))",
            // the simple form has no parameters
            "start-datatype ()",
            "end-datatype ((red) (green) (blue))",
            "end-datatypes",
        ]
    );
}

#[test]
fn recursive_datatype_resolves_its_own_sort_in_selectors() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))",
    );
    assert_eq!(
        handler.events,
        [
            "start-datatypes ((Lst 0))",
            "start-datatype ()",
            "end-datatype ((nil) (cons (hd Int) (tl <Lst>)))",
            "end-datatypes",
        ]
    );
}

#[test]
fn corpus_datatype_with_indexed_selector_sorts() {
    // shape taken from the UFBVDT corpus: a record-like datatype whose
    // selectors mix the datatype itself and indexed bit-vector sorts
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(declare-datatypes ((x254 0)) \
            (((x304 (x379 x254) (x127 (_ BitVec 256))) \
              (x269 (x222 x254) (x221 x254) (x534 (_ BitVec 256))) \
              (x409 (x99 (_ BitVec 256))))))",
    );
    assert_eq!(
        handler.events,
        [
            "start-datatypes ((x254 0))",
            "start-datatype ()",
            "end-datatype (\
                (x304 (x379 <x254>) (x127 (_ BitVec 256))) \
                (x269 (x222 <x254>) (x221 <x254>) (x534 (_ BitVec 256))) \
                (x409 (x99 (_ BitVec 256))))",
            "end-datatypes",
        ]
    );
}

#[test]
fn simple_and_parametric_datatypes_mix_in_one_command() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(declare-datatypes ((Unit 0) (Box 1) (Pair 2)) \
            (((unit)) \
             (par (X) ((box (unbox X)))) \
             (par (X Y) ((pair (first X) (second Y))))))",
    );
    assert_eq!(
        handler.events,
        [
            "start-datatypes ((Unit 0) (Box 1) (Pair 2))",
            "start-datatype ()",
            "end-datatype ((unit))",
            "start-datatype (X)",
            "end-datatype ((box (unbox [X])))",
            "start-datatype (X Y)",
            "end-datatype ((pair (first [X]) (second [Y])))",
            "end-datatypes",
        ]
    );
}

#[test]
fn datatype_params_are_scoped_to_their_datatype() {
    // `X` is a parameter of the first datatype only; in the second
    // datatype and in the following command it is an ordinary sort
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(declare-datatypes ((A 1) (B 0)) ((par (X) ((a (v X)))) ((b (w X))))) \
          (declare-fun f (X A) B)",
    );
    assert_eq!(
        handler.events,
        [
            "start-datatypes ((A 1) (B 0))",
            "start-datatype (X)",
            "end-datatype ((a (v [X])))",
            "start-datatype ()",
            "end-datatype ((b (w X)))",
            "end-datatypes",
            // the command has ended: this handler forgets the sorts on end
            "declare-fun f (X A) B",
        ]
    );
}

#[test]
fn quoted_par_is_an_ordinary_constructor_name() {
    // `par` is a reserved word only when unquoted
    let mut handler = Resolving::default();
    parse_resolving(&mut handler, b"(declare-datatypes ((A 0)) (((|par|))))");
    assert_eq!(
        handler.events,
        [
            "start-datatypes ((A 0))",
            "start-datatype ()",
            "end-datatype ((par))",
            "end-datatypes",
        ]
    );
    // unquoted, it cannot name a constructor
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) (((par))))", 30, 33);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
}

#[test]
fn repeated_declare_datatypes_reuse_the_persistent_parser() {
    // a parametric declaration followed by simple ones: the parameter list,
    // the constructor buffers, and the declaration count must all reset
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(declare-datatypes ((T 1)) ((par (X) ((t (v X) (w (T X))))))) \
          (declare-datatypes ((B 0) (C 0)) (((b (f C))) ((c)))) \
          (declare-datatypes ((D 0)) (((d))))",
    );
    assert_eq!(
        handler.events,
        [
            "start-datatypes ((T 1))",
            "start-datatype (X)",
            "end-datatype ((t (v [X]) (w (<T> [X]))))",
            "end-datatypes",
            "start-datatypes ((B 0) (C 0))",
            "start-datatype ()",
            "end-datatype ((b (f <C>)))",
            "start-datatype ()",
            "end-datatype ((c))",
            "end-datatypes",
            "start-datatypes ((D 0))",
            "start-datatype ()",
            "end-datatype ((d))",
            "end-datatypes",
        ]
    );
}

#[test]
fn declare_datatypes_handler_errors_point_at_the_triggering_token() {
    // start_declare_datatypes: the closing parenthesis of the sort declarations
    let handler = assert_handler_error(
        b"(declare-datatypes ((Forbidden 0)) (((a))))",
        "forbidden datatype name",
        33,
        34,
    );
    assert!(handler.events.is_empty());

    // start_datatype, simple form: the opening parenthesis of the first
    // constructor, which is the token revealing that there are no parameters
    let handler = assert_handler_error(
        b"(declare-datatypes ((Unstartable 0)) (((a))))",
        "unstartable datatype",
        39,
        40,
    );
    assert_eq!(handler.events, ["start-datatypes ((Unstartable 0))"]);

    // start_datatype, parametric form: the closing parenthesis of the parameters
    let handler = assert_handler_error(
        b"(declare-datatypes ((Unstartable 1)) ((par (X) ((a)))))",
        "unstartable datatype",
        45,
        46,
    );
    assert_eq!(handler.events, ["start-datatypes ((Unstartable 1))"]);

    // end_datatype, simple form: the closing parenthesis of the constructors,
    // which also closes the declaration
    let handler = assert_handler_error(
        b"(declare-datatypes ((A 0)) (((boom))))",
        "exploding constructor",
        35,
        36,
    );
    assert_eq!(
        handler.events,
        ["start-datatypes ((A 0))", "start-datatype ()"]
    );

    // end_datatype, parametric form: the closing parenthesis of the constructors,
    // one before the parenthesis closing the declaration
    let handler = assert_handler_error(
        b"(declare-datatypes ((A 1)) ((par (X) ((boom)))))",
        "exploding constructor",
        44,
        45,
    );
    assert_eq!(
        handler.events,
        ["start-datatypes ((A 1))", "start-datatype (X)"]
    );

    // end_declare_datatypes: the closing parenthesis of the declaration list
    let handler = assert_handler_error(
        b"(declare-datatypes ((Unendable 0)) (((a))))",
        "unendable datatypes",
        41,
        42,
    );
    assert_eq!(
        handler.events,
        [
            "start-datatypes ((Unendable 0))",
            "start-datatype ()",
            "end-datatype ((a))",
        ]
    );
}

#[test]
fn declare_datatypes_errors_point_at_offending_token() {
    // at least one sort must be declared
    let err = assert_parser_error(b"(declare-datatypes () ())", 20, 21);
    assert!(
        matches!(err, CategoryParserErrorKind::EmptyDatatypeSortDeclarations),
        "{err:?}"
    );
    // each sort declaration is parenthesized
    let err = assert_parser_error(b"(declare-datatypes (A 0) (((a))))", 20, 21);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
        ),
        "{err:?}"
    );
    // the arity is required
    let err = assert_parser_error(b"(declare-datatypes ((A)) (((a))))", 22, 23);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Numeral])
        ),
        "{err:?}"
    );
    // the declaration list is required
    let err = assert_parser_error(b"(declare-datatypes ((A 0)))", 26, 27);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
        ),
        "{err:?}"
    );
    // fewer declarations than sorts: the list closes where a declaration should start
    let err = assert_parser_error(b"(declare-datatypes ((A 0) (B 0)) (((a))))", 39, 40);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedDatatype),
        "{err:?}"
    );
    // more declarations than sorts: only the list end is allowed after the last one
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) (((a)) ((b))))", 34, 35);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
    // a declaration starts with `par` or a constructor, not a symbol
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) ((foo)))", 29, 32);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedDatatypeKind),
        "{err:?}"
    );
    // nor may it be empty
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) (()))", 29, 30);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedDatatypeKind),
        "{err:?}"
    );
    // a parametric declaration needs at least one parameter
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) ((par () ((a)))))", 34, 35);
    assert!(
        matches!(err, CategoryParserErrorKind::EmptyDatatypeParameters),
        "{err:?}"
    );
    // and at least one constructor
    let err = assert_parser_error(b"(declare-datatypes ((A 1)) ((par (X) ())))", 38, 39);
    assert!(
        matches!(err, CategoryParserErrorKind::EmptyDatatypeConstructors),
        "{err:?}"
    );
    // a parametric declaration is closed by its own parenthesis
    let err = assert_parser_error(b"(declare-datatypes ((A 1)) ((par (X) ((a))))", 44, 44);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
    // a constructor name is a symbol
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) (((1))))", 30, 31);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
    // a selector is a parenthesized pair
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) (((a x))))", 32, 33);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
        ),
        "{err:?}"
    );
    // with a sort
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) (((a (x)))))", 34, 35);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedSort),
        "{err:?}"
    );
    // nothing may follow the declaration list
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) (((a))) extra)", 35, 40);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
}

// --- declare-datatype (syntax sugar) ---
//
// `(declare-datatype D dec)` abbreviates `(declare-datatypes ((D k)) (dec))`
// with `k` the number of parameters of `dec` (zero for the simple form),
// so the handler observes exactly the events of the desugared command.

#[test]
fn declare_datatype_is_declare_datatypes_with_one_sort() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(declare-datatype Lst ((nil) (cons (hd Int) (tl Lst))))",
    );
    assert_eq!(
        handler.events,
        [
            // the arity of the simple form is zero
            "start-datatypes ((Lst 0))",
            "start-datatype ()",
            "end-datatype ((nil) (cons (hd Int) (tl <Lst>)))",
            "end-datatypes",
        ]
    );
}

#[test]
fn parametric_declare_datatype_derives_arity_from_params() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(declare-datatype Tree (par (X) ((leaf) (node (l (Tree X)) (v X) (r (Tree X)))))) \
          (declare-datatype Pair (par (X Y) ((pair (first X) (second Y)))))",
    );
    assert_eq!(
        handler.events,
        [
            "start-datatypes ((Tree 1))",
            "start-datatype (X)",
            "end-datatype ((leaf) (node (l (<Tree> [X])) (v [X]) (r (<Tree> [X]))))",
            "end-datatypes",
            "start-datatypes ((Pair 2))",
            "start-datatype (X Y)",
            "end-datatype ((pair (first [X]) (second [Y])))",
            "end-datatypes",
        ]
    );
}

#[test]
fn declare_datatype_and_declare_datatypes_produce_identical_events() {
    let mut sugar = Resolving::default();
    parse_resolving(
        &mut sugar,
        b"(declare-datatype Opt (par (X) ((none) (some (val X)))))",
    );
    let mut plain = Resolving::default();
    parse_resolving(
        &mut plain,
        b"(declare-datatypes ((Opt 1)) ((par (X) ((none) (some (val X))))))",
    );
    assert_eq!(sugar.events, plain.events);
}

#[test]
fn declare_datatype_handler_errors_point_at_the_triggering_token() {
    // start_declare_datatypes is deferred until the arity is known,
    // but the error is about the name, so it points at the name
    let handler = assert_handler_error(
        b"(declare-datatype Forbidden ((a)))",
        "forbidden datatype name",
        18,
        27,
    );
    assert!(handler.events.is_empty());

    // start_datatype: the opening parenthesis of the first constructor
    let handler = assert_handler_error(
        b"(declare-datatype Unstartable ((a)))",
        "unstartable datatype",
        31,
        32,
    );
    assert_eq!(handler.events, ["start-datatypes ((Unstartable 0))"]);

    // end_datatype: the closing parenthesis of the constructors
    let handler = assert_handler_error(
        b"(declare-datatype A ((boom)))",
        "exploding constructor",
        27,
        28,
    );
    assert_eq!(
        handler.events,
        ["start-datatypes ((A 0))", "start-datatype ()"]
    );

    // end_declare_datatypes: the same token, as the single declaration ends the list
    let handler = assert_handler_error(
        b"(declare-datatype Unendable ((a)))",
        "unendable datatypes",
        32,
        33,
    );
    assert_eq!(
        handler.events,
        [
            "start-datatypes ((Unendable 0))",
            "start-datatype ()",
            "end-datatype ((a))",
        ]
    );
}

#[test]
fn declare_datatype_errors_point_at_offending_token() {
    // the name is a symbol
    let err = assert_parser_error(b"(declare-datatype 1 ((a)))", 18, 19);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::Symbol])
        ),
        "{err:?}"
    );
    // the declaration is required
    let err = assert_parser_error(b"(declare-datatype A)", 19, 20);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenOpen])
        ),
        "{err:?}"
    );
    // the declaration has the same shape as in declare-datatypes
    let err = assert_parser_error(b"(declare-datatype A (()))", 21, 22);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedDatatypeKind),
        "{err:?}"
    );
    let err = assert_parser_error(b"(declare-datatype A (par () ((a))))", 26, 27);
    assert!(
        matches!(err, CategoryParserErrorKind::EmptyDatatypeParameters),
        "{err:?}"
    );
    // exactly one declaration, without a surrounding list
    let err = assert_parser_error(b"(declare-datatype A ((a)) ((b)))", 26, 27);
    assert!(
        matches!(
            err,
            CategoryParserErrorKind::ExpectedToken(&[TokenType::ParenClose])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(declare-datatype A (((a))))", 21, 22);
    assert!(
        matches!(err, CategoryParserErrorKind::ExpectedDatatypeKind),
        "{err:?}"
    );
}

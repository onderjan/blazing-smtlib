//! Public-API tests of the standard commands: define-fun callback ordering,
//! handler errors, and per-command shape errors.

mod common;

use std::convert::Infallible;

use common::{assert_error_span, assert_parser_error, parse_with};

use blazing_smtlib::{
    CommandHandler, SmtAttributeValue, SmtAttributes, SmtBindings, SmtDatatypeConstructor,
    SmtFunctionSignature, SmtHandler, SmtIdentView, SmtIndexView, SmtKeyword, SmtKeywordView,
    SmtNumeral, SmtPatternView, SmtQuantifierKind, SmtSExpr, SmtSimplePatternView, SmtSort,
    SmtSpecialConstantView, SmtStringContent, SmtSymbol, SmtSymbolView, SmtTerm,
    read::{SmtReadErrorKind, lexer::SmtLexicalErrorKind, parser::SmtSyntaxErrorKind},
    token::SmtTokenCategory,
};

/// Handler that resolves body identifiers against the parameters of the
/// define-fun or recursive function body currently in progress, marking
/// resolved ones as `[name]`, and body sorts against the parameters of the
/// define-sort or datatype in progress in the same way. Sorts declared by
/// the declare-datatypes in progress are marked as `<name>`, functions
/// of the define-funs-rec in progress as `{name}`, and variables of the
/// match case in progress as `$name`. The resolution succeeding
/// proves that the start callbacks deliver the signature before the body is
/// constructed.
#[derive(Default)]
struct Resolving {
    /// Callbacks received, in order.
    events: Vec<String>,
    /// Parameter names of the define-fun or recursive function body
    /// in progress, empty outside one.
    params: Vec<String>,
    /// Parameter names of the define-sort or datatype in progress,
    /// empty outside one.
    sort_params: Vec<String>,
    /// Sort names declared by the declare-datatypes in progress,
    /// in declaration order, empty outside one.
    datatype_sorts: Vec<String>,
    /// Index into `datatype_sorts` of the datatype in progress.
    datatype_index: usize,
    /// Function names of the define-funs-rec in progress,
    /// in signature order, empty outside one.
    rec_functions: Vec<String>,
    /// Parameter names of each function of the define-funs-rec
    /// in progress, in signature order, empty outside one.
    rec_params: Vec<Vec<String>>,
    /// Index into `rec_functions` and `rec_params` of the body in progress.
    rec_index: usize,
    /// Matches in progress, innermost last, empty outside one.
    matches: Vec<ResolvingMatch>,
}

/// A match in progress: its scrutinee and the variables bound by the
/// pattern of the case in progress, `None` between cases.
struct ResolvingMatch {
    scrutinee: String,
    case_vars: Option<Vec<String>>,
}

fn simple_pattern_text(pattern: SmtSimplePatternView<'_>) -> String {
    match pattern {
        SmtSimplePatternView::Symbol(symbol) => text(symbol.as_slice()),
        SmtSimplePatternView::Wildcard => "_".into(),
    }
}

/// Renders a pattern as written, so that the events show it unclassified.
fn pattern_text(pattern: SmtPatternView<'_>) -> String {
    match pattern {
        SmtPatternView::Simple(simple) => simple_pattern_text(simple),
        SmtPatternView::Application { constructor, args } => {
            let args: Vec<String> = args.iter().map(simple_pattern_text).collect();
            format!("({} {})", text(constructor.as_slice()), args.join(" "))
        }
    }
}

impl Resolving {
    /// Resolves a term identifier against the variables of the match cases
    /// in progress, marked as `$name`, then against the parameters of the
    /// body in progress, marked as `[name]`, and otherwise against the
    /// functions of the define-funs-rec in progress, marked as `{name}`.
    fn resolve_term_ident(&self, ident: SmtIdentView<'_>) -> String {
        let name = ident_view_text(ident);
        let is_case_var = self
            .matches
            .iter()
            .filter_map(|m| m.case_vars.as_ref())
            .any(|vars| vars.contains(&name));
        if is_case_var {
            format!("${name}")
        } else if self.params.contains(&name) {
            format!("[{name}]")
        } else if self.rec_functions.contains(&name) {
            format!("{{{name}}}")
        } else {
            name
        }
    }
}

fn text(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).expect("test inputs are ASCII")
}

/// Renders an identifier including its indices, so that stale indices
/// leaking from a previously parsed command would show up in the events.
fn ident_view_text(ident: SmtIdentView<'_>) -> String {
    let name = text(ident.name.as_slice());
    if ident.indices.is_empty() {
        return name;
    }
    let indices: Vec<String> = ident
        .indices
        .iter()
        .map(|index| match index {
            SmtIndexView::Numeral(numeral) => text(numeral.as_slice()),
            SmtIndexView::Symbol(symbol) => text(symbol.as_slice()),
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

    fn handle_sort(&mut self, sort: SmtSort<'_, Self>) -> Result<String, String> {
        let name = ident_view_text(sort.ident);
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
            format!("({} {})", name, sort.applied.as_slice().join(" "))
        })
    }

    fn handle_term(&mut self, term: SmtTerm<'_, Self>) -> Result<String, String> {
        Ok(match term {
            SmtTerm::SpecialConstant(constant) => match constant {
                SmtSpecialConstantView::Numeral(numeral) => text(numeral.as_slice()),
                _ => "<constant>".into(),
            },
            SmtTerm::QualifiedIdent(qualified_ident) => {
                self.resolve_term_ident(qualified_ident.ident)
            }
            SmtTerm::Application(application) => {
                let function = self.resolve_term_ident(application.function.ident);
                format!("({} {})", function, application.args.as_slice().join(" "))
            }
        })
    }

    fn start_let(&mut self, _bindings: SmtBindings<'_, Self>) -> Result<(), String> {
        Ok(())
    }

    fn end_let(&mut self, term: String) -> Result<String, String> {
        Ok(term)
    }

    fn handle_s_expr(&mut self, _expr: SmtSExpr<'_, Self>) -> Result<(), String> {
        Ok(())
    }

    fn handle_attribute(
        &mut self,
        _name: SmtKeywordView<'_>,
        _value: Option<SmtAttributeValue<'_, Self>>,
    ) -> Result<(), String> {
        Ok(())
    }

    fn annotate_term(
        &mut self,
        term: String,
        _attributes: SmtAttributes<'_, Self>,
    ) -> Result<String, String> {
        Ok(term)
    }

    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _name: SmtSymbolView<'_>,
        _sort: String,
    ) -> Result<(), String> {
        Ok(())
    }
    fn end_quantifier(&mut self, term: String) -> Result<String, String> {
        Ok(term)
    }
    fn start_lambda(&mut self, _name: SmtSymbolView<'_>, _sort: String) -> Result<(), String> {
        Ok(())
    }
    fn end_lambda(&mut self, term: String) -> Result<String, String> {
        Ok(term)
    }

    fn start_match(&mut self, scrutinee: String) -> Result<(), String> {
        if scrutinee == "forbidden" {
            return Err("forbidden scrutinee".into());
        }
        self.events.push(format!("start-match {scrutinee}"));
        self.matches.push(ResolvingMatch {
            scrutinee,
            case_vars: None,
        });
        Ok(())
    }

    fn start_match_case(&mut self, pattern: SmtPatternView<'_>) -> Result<(), String> {
        let current = self
            .matches
            .last_mut()
            .expect("start_match_case without start_match");
        assert!(
            current.case_vars.is_none(),
            "start_match_case while a case is still open"
        );
        // a bare symbol is taken as a variable; a real handler would
        // first check whether it names a nullary constructor
        let vars: Vec<String> = match pattern {
            SmtPatternView::Simple(SmtSimplePatternView::Symbol(symbol)) => {
                vec![text(symbol.as_slice())]
            }
            SmtPatternView::Simple(SmtSimplePatternView::Wildcard) => Vec::new(),
            SmtPatternView::Application { constructor, args } => {
                if constructor.as_slice() == b"unstartable" {
                    return Err("unstartable case".into());
                }
                args.iter()
                    .filter_map(|arg| match arg {
                        SmtSimplePatternView::Symbol(symbol) => Some(text(symbol.as_slice())),
                        SmtSimplePatternView::Wildcard => None,
                    })
                    .collect()
            }
        };
        if vars.iter().any(|var| var == "unstartable") {
            return Err("unstartable case".into());
        }
        self.events
            .push(format!("start-case {}", pattern_text(pattern)));
        current.case_vars = Some(vars);
        Ok(())
    }

    fn end_match_case(&mut self, term: String) -> Result<(), String> {
        if term == "boom" {
            return Err("exploding case".into());
        }
        let current = self
            .matches
            .last_mut()
            .expect("end_match_case without start_match");
        assert!(
            current.case_vars.is_some(),
            "end_match_case without start_match_case"
        );
        self.events.push(format!("end-case {term}"));
        current.case_vars = None;
        Ok(())
    }

    fn end_match(&mut self) -> Result<String, String> {
        let current = self.matches.pop().expect("end_match without start_match");
        assert!(
            current.case_vars.is_none(),
            "end_match while a case is still open"
        );
        if current.scrutinee == "unendable" {
            return Err("unendable match".into());
        }
        self.events.push("end-match".into());
        Ok(format!("(match {})", current.scrutinee))
    }
}

impl CommandHandler for Resolving {
    type NonstandardParser = Infallible;

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
    fn command_get_value(&mut self, terms: Vec<String>) -> Result<(), String> {
        if terms.iter().any(|term| term == "boom") {
            return Err("exploding get-value".into());
        }
        self.events.push(format!("get-value ({})", terms.join(" ")));
        Ok(())
    }
    fn command_get_assertions(&mut self) -> Result<(), String> {
        self.events.push("get-assertions".into());
        Ok(())
    }
    fn command_get_assignment(&mut self) -> Result<(), String> {
        self.events.push("get-assignment".into());
        Ok(())
    }
    fn command_get_model(&mut self) -> Result<(), String> {
        self.events.push("get-model".into());
        Ok(())
    }
    fn command_get_proof(&mut self) -> Result<(), String> {
        self.events.push("get-proof".into());
        Ok(())
    }
    fn command_get_unsat_assumptions(&mut self) -> Result<(), String> {
        self.events.push("get-unsat-assumptions".into());
        Ok(())
    }
    fn command_get_unsat_core(&mut self) -> Result<(), String> {
        self.events.push("get-unsat-core".into());
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

    fn start_define_funs_rec(
        &mut self,
        signatures: Vec<SmtFunctionSignature<Self>>,
    ) -> Result<(), String> {
        let mut rendered = Vec::new();
        self.rec_functions.clear();
        self.rec_params.clear();
        self.rec_index = 0;
        for signature in &signatures {
            let name = text(signature.name.as_slice());
            if name == "forbidden" {
                return Err("forbidden recursive function name".into());
            }
            let params: Vec<String> = signature
                .params
                .iter()
                .map(|(param, sort)| format!("({} {})", text(param.as_slice()), sort))
                .collect();
            rendered.push(format!(
                "({name} ({}) {})",
                params.join(" "),
                signature.result_sort
            ));
            self.rec_functions.push(name);
            self.rec_params.push(
                signature
                    .params
                    .iter()
                    .map(|(param, _)| text(param.as_slice()))
                    .collect(),
            );
        }
        self.events
            .push(format!("start-funs-rec ({})", rendered.join(" ")));
        Ok(())
    }

    fn start_recursive_body(&mut self) -> Result<(), String> {
        // the bodies arrive in signature order, so the handler
        // knows which function is being started by counting
        let name = self
            .rec_functions
            .get(self.rec_index)
            .cloned()
            .unwrap_or_else(|| panic!("body {} started without a signature", self.rec_index));
        if name == "unstartable" {
            return Err("unstartable function".into());
        }
        self.events.push("start-body".into());
        self.params = self.rec_params[self.rec_index].clone();
        Ok(())
    }

    fn end_recursive_body(&mut self, term: String) -> Result<(), String> {
        if term == "boom" {
            return Err("exploding recursive body".into());
        }
        self.events.push(format!("end-body {term}"));
        self.params.clear();
        self.rec_index += 1;
        Ok(())
    }

    fn end_define_funs_rec(&mut self) -> Result<(), String> {
        if self.rec_functions.iter().any(|name| name == "unendable") {
            return Err("unendable functions".into());
        }
        self.events.push("end-funs-rec".into());
        // a real handler keeps the functions; forgetting them here makes
        // the end of the command observable in later events
        self.rec_functions.clear();
        self.rec_params.clear();
        self.rec_index = 0;
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

    fn start_datatype_declaration(&mut self, params: Vec<SmtSymbol>) -> Result<(), String> {
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

    fn end_datatype_declaration(
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
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    // the parameter list is required, even when empty
    let err = assert_parser_error(b"(define-sort S Int)", 15, 18);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // the parameters are bare symbols, not sorted vars or numerals
    let err = assert_parser_error(b"(define-sort S ((X)) Int)", 16, 17);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    let err = assert_parser_error(b"(define-sort S (X 1) Int)", 18, 19);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    // the body sort is required
    let err = assert_parser_error(b"(define-sort S ())", 17, 18);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSort), "{err:?}");
    // exactly one body sort is allowed
    let err = assert_parser_error(b"(define-sort S () Int Bool)", 22, 26);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
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
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::Numeral])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(pop)", 4, 5);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::Numeral])
        ),
        "{err:?}"
    );
    // the amount must be a numeral
    let err = assert_parser_error(b"(push x)", 6, 7);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::Numeral])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(pop 1.0)", 5, 8);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::Numeral])
        ),
        "{err:?}"
    );
    // exactly one amount
    let err = assert_parser_error(b"(push 1 2)", 8, 9);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(pop 1 2)", 7, 8);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
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
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    // the arity is required
    let err = assert_parser_error(b"(declare-sort U)", 15, 16);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::Numeral])
        ),
        "{err:?}"
    );
    // the arity must be a numeral, not a decimal or another constant
    let err = assert_parser_error(b"(declare-sort U 1.5)", 16, 19);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::Numeral])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(declare-sort U #x0)", 16, 19);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::Numeral])
        ),
        "{err:?}"
    );
    // exactly one arity
    let err = assert_parser_error(b"(declare-sort U 0 0)", 18, 19);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
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
        SmtReadErrorKind::Lexical(SmtLexicalErrorKind::NumeralLeadingZero) => {}
        kind => panic!("expected a leading zero lexer error, got {kind:?}"),
    }
}

#[test]
fn declare_sort_parameter_errors_point_at_offending_token() {
    // the parameter name is required and must be a symbol
    let err = assert_parser_error(b"(declare-sort-parameter)", 23, 24);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    let err = assert_parser_error(b"(declare-sort-parameter 1)", 24, 25);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    // exactly one parameter per command
    let err = assert_parser_error(b"(declare-sort-parameter T U)", 26, 27);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
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
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    // define-const has no parameter list, an empty one is not a sort
    let err = assert_parser_error(b"(define-const c () Int 5)", 17, 18);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedSortInner),
        "{err:?}"
    );
    // the body term is required
    let err = assert_parser_error(b"(define-const c Int)", 19, 20);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedTerm), "{err:?}");
    // exactly one body term is allowed
    let err = assert_parser_error(b"(define-const c Int 5 6)", 22, 23);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
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
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
    // the assumption list is required, even when empty
    let err = assert_parser_error(b"(check-sat-assuming)", 19, 20);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // the assumptions must be parenthesized as a list
    let err = assert_parser_error(b"(check-sat-assuming a)", 20, 21);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // nothing may follow the assumption list
    let err = assert_parser_error(b"(check-sat-assuming (a b) extra)", 26, 31);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
    // each assumption must be a term
    let err = assert_parser_error(b"(check-sat-assuming (a :kw))", 23, 26);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedTerm), "{err:?}");
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
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    // each sorted var must be parenthesized
    let err = assert_parser_error(b"(define-fun f (x Int) Int x)", 15, 16);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // the body term is required
    let err = assert_parser_error(b"(define-fun f () Int)", 20, 21);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedTerm), "{err:?}");
    // exactly one body term is allowed
    let err = assert_parser_error(b"(define-fun f () Int 5 6)", 23, 24);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
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
        SmtReadErrorKind::Syntax(kind) => panic!("expected handler error, got {kind:?}"),
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
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::String])
        ),
        "{err:?}"
    );
    // exactly one string literal
    let err = assert_parser_error(b"(echo \"hi\" \"there\")", 11, 18);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
    // get-option and get-info take a keyword, not a symbol or string
    let err = assert_parser_error(b"(get-option opt)", 12, 15);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::Keyword])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(get-info \"x\")", 10, 13);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::Keyword])
        ),
        "{err:?}"
    );
    // set-option requires an attribute
    let err = assert_parser_error(b"(set-option)", 11, 12);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedAttribute),
        "{err:?}"
    );
    // reset and reset-assertions take no arguments
    let err = assert_parser_error(b"(reset x)", 7, 8);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(reset-assertions x)", 18, 19);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
    // the queries without arguments take none
    for (input, start, end) in [
        (&b"(get-assertions x)"[..], 16, 17),
        (b"(get-assignment x)", 16, 17),
        (b"(get-model x)", 11, 12),
        (b"(get-proof x)", 11, 12),
        (b"(get-unsat-assumptions x)", 23, 24),
        (b"(get-unsat-core x)", 16, 17),
    ] {
        let err = assert_parser_error(input, start, end);
        assert!(
            matches!(
                err,
                SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
            ),
            "{err:?} for {:?}",
            text(input)
        );
    }
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
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
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
        matches!(err, SmtSyntaxErrorKind::EmptyDatatypeIntroductions),
        "{err:?}"
    );
    // each sort declaration is parenthesized
    let err = assert_parser_error(b"(declare-datatypes (A 0) (((a))))", 20, 21);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // the arity is required
    let err = assert_parser_error(b"(declare-datatypes ((A)) (((a))))", 22, 23);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::Numeral])
        ),
        "{err:?}"
    );
    // the declaration list is required
    let err = assert_parser_error(b"(declare-datatypes ((A 0)))", 26, 27);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // fewer declarations than sorts: the list closes where a declaration should start
    let err = assert_parser_error(b"(declare-datatypes ((A 0) (B 0)) (((a))))", 39, 40);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedDatatype),
        "{err:?}"
    );
    // more declarations than sorts: only the list end is allowed after the last one
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) (((a)) ((b))))", 34, 35);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
    // a declaration starts with `par` or a constructor, not a symbol
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) ((foo)))", 29, 32);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedDatatypeKind),
        "{err:?}"
    );
    // nor may it be empty
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) (()))", 29, 30);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedDatatypeKind),
        "{err:?}"
    );
    // a parametric declaration needs at least one parameter
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) ((par () ((a)))))", 34, 35);
    assert!(
        matches!(err, SmtSyntaxErrorKind::EmptyDatatypeParameters),
        "{err:?}"
    );
    // and at least one constructor
    let err = assert_parser_error(b"(declare-datatypes ((A 1)) ((par (X) ())))", 38, 39);
    assert!(
        matches!(err, SmtSyntaxErrorKind::EmptyDatatypeConstructors),
        "{err:?}"
    );
    // a parametric declaration is closed by its own parenthesis
    let err = assert_parser_error(b"(declare-datatypes ((A 1)) ((par (X) ((a))))", 44, 44);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
    // a constructor name is a symbol
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) (((1))))", 30, 31);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    // a selector is a parenthesized pair
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) (((a x))))", 32, 33);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // with a sort
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) (((a (x)))))", 34, 35);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSort), "{err:?}");
    // nothing may follow the declaration list
    let err = assert_parser_error(b"(declare-datatypes ((A 0)) (((a))) extra)", 35, 40);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
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
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    // the declaration is required
    let err = assert_parser_error(b"(declare-datatype A)", 19, 20);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // the declaration has the same shape as in declare-datatypes
    let err = assert_parser_error(b"(declare-datatype A ())", 21, 22);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedDatatypeKind),
        "{err:?}"
    );
    let err = assert_parser_error(b"(declare-datatype A (par () ((a))))", 26, 27);
    assert!(
        matches!(err, SmtSyntaxErrorKind::EmptyDatatypeParameters),
        "{err:?}"
    );
    // exactly one declaration, without a surrounding list
    let err = assert_parser_error(b"(declare-datatype A ((a)) ((b)))", 26, 27);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
    // a list around the declaration is read as a simple declaration whose
    // first constructor starts with a parenthesis instead of a name
    let err = assert_parser_error(b"(declare-datatype A (((a))))", 22, 23);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
}

// --- Recursive function definitions ---

#[test]
fn define_funs_rec_delivers_all_signatures_before_any_body() {
    // the standard's mutually recursive even / odd example
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(define-funs-rec ((even ((n Int)) Bool) (odd ((n Int)) Bool)) \
            ((ite (= n 0) true (odd (- n 1))) (ite (= n 0) false (even (- n 1)))))",
    );
    assert_eq!(
        handler.events,
        [
            "start-funs-rec ((even ((n Int)) Bool) (odd ((n Int)) Bool))",
            "start-body",
            // `odd` is already known while the body of `even` is constructed
            "end-body (ite (= [n] 0) true ({odd} (- [n] 1)))",
            "start-body",
            "end-body (ite (= [n] 0) false ({even} (- [n] 1)))",
            "end-funs-rec",
        ]
    );
}

#[test]
fn recursive_body_params_are_scoped_to_their_body() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(define-funs-rec ((f ((x Int)) Int) (g ((y Int)) Int)) ((+ x y) (+ x y)))",
    );
    assert_eq!(
        handler.events,
        [
            "start-funs-rec ((f ((x Int)) Int) (g ((y Int)) Int))",
            "start-body",
            "end-body (+ [x] y)",
            "start-body",
            "end-body (+ x [y])",
            "end-funs-rec",
        ]
    );
}

#[test]
fn recursive_constant_refers_to_itself() {
    // a function without parameters is a bare identifier in its own body
    let mut handler = Resolving::default();
    parse_resolving(&mut handler, b"(define-funs-rec ((c () Int)) (c))");
    assert_eq!(
        handler.events,
        [
            "start-funs-rec ((c () Int))",
            "start-body",
            "end-body {c}",
            "end-funs-rec",
        ]
    );
}

#[test]
fn define_fun_rec_is_define_funs_rec_with_one_function() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(define-fun-rec fact ((n Int)) Int (ite (<= n 1) 1 (* n (fact (- n 1)))))",
    );
    assert_eq!(
        handler.events,
        [
            "start-funs-rec ((fact ((n Int)) Int))",
            "start-body",
            "end-body (ite (<= [n] 1) 1 (* [n] ({fact} (- [n] 1))))",
            "end-funs-rec",
        ]
    );
}

#[test]
fn define_fun_rec_and_define_funs_rec_produce_identical_events() {
    let mut sugar = Resolving::default();
    parse_resolving(
        &mut sugar,
        b"(define-fun-rec sum ((n Int)) Int (ite (= n 0) 0 (+ n (sum (- n 1)))))",
    );
    let mut plain = Resolving::default();
    parse_resolving(
        &mut plain,
        b"(define-funs-rec ((sum ((n Int)) Int)) ((ite (= n 0) 0 (+ n (sum (- n 1))))))",
    );
    assert_eq!(sugar.events, plain.events);
}

#[test]
fn repeated_recursive_definitions_reset_count_functions_and_scope() {
    // two functions, then one, then the sugar, then a plain define-fun:
    // the signature count, the function names, and the parameters must all reset
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(define-funs-rec ((f ((x Int)) Int) (g ((y Int)) Int)) ((g x) (f y))) \
          (define-funs-rec ((h ((z Int)) Int)) ((h (f x)))) \
          (define-fun-rec k ((x Int)) Int (k (h z))) \
          (define-fun m ((y Int)) Int (k (g y)))",
    );
    assert_eq!(
        handler.events,
        [
            "start-funs-rec ((f ((x Int)) Int) (g ((y Int)) Int))",
            "start-body",
            "end-body ({g} [x])",
            "start-body",
            "end-body ({f} [y])",
            "end-funs-rec",
            // `f` and `x` were forgotten with the previous command
            "start-funs-rec ((h ((z Int)) Int))",
            "start-body",
            "end-body ({h} (f x))",
            "end-funs-rec",
            "start-funs-rec ((k ((x Int)) Int))",
            "start-body",
            "end-body ({k} (h z))",
            "end-funs-rec",
            // a define-fun body sees neither the functions nor the parameters
            "start m ((y Int)) Int",
            "end (k (g [y]))",
        ]
    );
}

#[test]
fn define_funs_rec_handler_errors_point_at_the_triggering_token() {
    // start_define_funs_rec: the closing parenthesis of the signature list
    let handler = assert_handler_error(
        b"(define-funs-rec ((forbidden () Int)) (1))",
        "forbidden recursive function name",
        36,
        37,
    );
    assert!(handler.events.is_empty());

    // start_recursive_body: the first token of the body, whether it is
    // a constant or the opening parenthesis of an application
    let handler = assert_handler_error(
        b"(define-funs-rec ((unstartable () Int)) (1))",
        "unstartable function",
        41,
        42,
    );
    assert_eq!(handler.events, ["start-funs-rec ((unstartable () Int))"]);
    let handler = assert_handler_error(
        b"(define-funs-rec ((unstartable () Int)) ((+ 1 2)))",
        "unstartable function",
        41,
        42,
    );
    assert_eq!(handler.events, ["start-funs-rec ((unstartable () Int))"]);

    // start_recursive_body of the second function: the first token of the second body
    let handler = assert_handler_error(
        b"(define-funs-rec ((f () Int) (unstartable () Int)) (1 2))",
        "unstartable function",
        54,
        55,
    );
    assert_eq!(
        handler.events,
        [
            "start-funs-rec ((f () Int) (unstartable () Int))",
            "start-body",
            "end-body 1",
        ]
    );

    // end_recursive_body: the last token of the body, whether it is
    // a constant or the closing parenthesis of a compound term
    let handler = assert_handler_error(
        b"(define-funs-rec ((f () Int)) (boom))",
        "exploding recursive body",
        31,
        35,
    );
    assert_eq!(
        handler.events,
        ["start-funs-rec ((f () Int))", "start-body"]
    );
    let handler = assert_handler_error(
        b"(define-funs-rec ((f () Int)) ((let ((x 1)) boom)))",
        "exploding recursive body",
        48,
        49,
    );
    assert_eq!(
        handler.events,
        ["start-funs-rec ((f () Int))", "start-body"]
    );

    // end_define_funs_rec: the closing parenthesis of the body list
    let handler = assert_handler_error(
        b"(define-funs-rec ((unendable () Int)) (1))",
        "unendable functions",
        40,
        41,
    );
    assert_eq!(
        handler.events,
        [
            "start-funs-rec ((unendable () Int))",
            "start-body",
            "end-body 1",
        ]
    );
}

#[test]
fn define_fun_rec_handler_errors_point_at_the_triggering_token() {
    // start_define_funs_rec: the last token of the signature
    let handler = assert_handler_error(
        b"(define-fun-rec forbidden () Int 1)",
        "forbidden recursive function name",
        29,
        32,
    );
    assert!(handler.events.is_empty());

    // start_recursive_body: the first token of the body
    let handler = assert_handler_error(
        b"(define-fun-rec unstartable () Int 1)",
        "unstartable function",
        35,
        36,
    );
    assert_eq!(handler.events, ["start-funs-rec ((unstartable () Int))"]);

    // end_recursive_body: the last token of the body
    let handler = assert_handler_error(
        b"(define-fun-rec f () Int boom)",
        "exploding recursive body",
        25,
        29,
    );
    assert_eq!(
        handler.events,
        ["start-funs-rec ((f () Int))", "start-body"]
    );

    // end_define_funs_rec: also the last token of the body,
    // as the single body ends the definitions
    let handler = assert_handler_error(
        b"(define-fun-rec unendable () Int 1)",
        "unendable functions",
        33,
        34,
    );
    assert_eq!(
        handler.events,
        [
            "start-funs-rec ((unendable () Int))",
            "start-body",
            "end-body 1",
        ]
    );
}

#[test]
fn define_funs_rec_errors_point_at_offending_token() {
    // at least one function must be defined
    let err = assert_parser_error(b"(define-funs-rec () ())", 18, 19);
    assert!(
        matches!(err, SmtSyntaxErrorKind::EmptyFunctionSignatures),
        "{err:?}"
    );
    // each signature is parenthesized
    let err = assert_parser_error(b"(define-funs-rec (f () Int) (1))", 18, 19);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // the function name must be a symbol
    let err = assert_parser_error(b"(define-funs-rec ((1 () Int)) (1))", 19, 20);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    // each sorted var is parenthesized
    let err = assert_parser_error(b"(define-funs-rec ((f (x Int) Int)) (1))", 22, 23);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // the result sort is required
    let err = assert_parser_error(b"(define-funs-rec ((f ())) (1))", 23, 24);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSort), "{err:?}");
    // the body list is required
    let err = assert_parser_error(b"(define-funs-rec ((f () Int)))", 29, 30);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // one body per function: the shortfall is detected at the end of the body list
    let err = assert_parser_error(b"(define-funs-rec ((f () Int) (g () Int)) (1))", 43, 44);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedFunctionBody),
        "{err:?}"
    );
    let err = assert_parser_error(b"(define-funs-rec ((f () Int)) ())", 31, 32);
    assert!(
        matches!(err, SmtSyntaxErrorKind::ExpectedFunctionBody),
        "{err:?}"
    );
    // one body per function: the excess is detected at the excess body
    let err = assert_parser_error(b"(define-funs-rec ((f () Int)) (1 2))", 33, 34);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
    // nothing follows the body list
    let err = assert_parser_error(b"(define-funs-rec ((f () Int)) (1) 2)", 34, 35);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
    // the number of allowed bodies does not leak into the next command
    let err = assert_parser_error(
        b"(define-funs-rec ((f () Int) (g () Int)) (1 2)) (define-funs-rec ((h () Int)) (1 2))",
        81,
        82,
    );
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
}

#[test]
fn define_fun_rec_errors_point_at_offending_token() {
    // the function name must be a symbol
    let err = assert_parser_error(b"(define-fun-rec 1 () Int 1)", 16, 17);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    // the signature is not listed as in define-funs-rec
    let err = assert_parser_error(b"(define-fun-rec ((f () Int)) (1))", 16, 17);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedSymbol), "{err:?}");
    // each sorted var is parenthesized
    let err = assert_parser_error(b"(define-fun-rec f (x Int) Int x)", 19, 20);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // the body term is required
    let err = assert_parser_error(b"(define-fun-rec f () Int)", 24, 25);
    assert!(matches!(err, SmtSyntaxErrorKind::ExpectedTerm), "{err:?}");
    // exactly one body term is allowed
    let err = assert_parser_error(b"(define-fun-rec f () Int 1 2)", 27, 28);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
}

#[test]
fn missing_recursive_body_is_started_only_in_the_sugar_form() {
    // the callbacks received before a parser error are an expectation of
    // the current implementation, not a contract: the sugar form has no
    // body list, so the closing parenthesis reaches the body parser and
    // starts the body before the missing term is detected
    let mut handler = Resolving::default();
    let err = parse_with(&mut handler, b"(define-fun-rec f () Int)")
        .expect_err("expected a parser error");
    assert_error_span(&err, 24, 25);
    assert!(
        matches!(
            err.kind(),
            SmtReadErrorKind::Syntax(SmtSyntaxErrorKind::ExpectedTerm)
        ),
        "{:?}",
        err.kind()
    );
    assert_eq!(
        handler.events,
        ["start-funs-rec ((f () Int))", "start-body"]
    );

    // in the full form, the body list filters out the closing parenthesis
    // before any body is started
    let mut handler = Resolving::default();
    let err = parse_with(&mut handler, b"(define-funs-rec ((f () Int)) ())")
        .expect_err("expected a parser error");
    assert_error_span(&err, 31, 32);
    assert!(
        matches!(
            err.kind(),
            SmtReadErrorKind::Syntax(SmtSyntaxErrorKind::ExpectedFunctionBody)
        ),
        "{:?}",
        err.kind()
    );
    assert_eq!(handler.events, ["start-funs-rec ((f () Int))"]);
}

// --- Match terms ---

#[test]
fn match_case_variables_resolve_while_the_body_is_parsed() {
    // the standard's list append example; `nil` arrives as a bare symbol
    // and is taken as a variable by this handler, a real one would consult
    // the datatype of `l` first
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(assert (match l ((nil l2) ((cons h t) (cons h (append t l2))))))",
    );
    assert_eq!(
        handler.events,
        [
            "start-match l",
            "start-case nil",
            "end-case l2",
            "start-case (cons h t)",
            "end-case (cons $h (append $t l2))",
            "end-match",
            "assert (match l)",
        ]
    );
}

#[test]
fn wildcards_bind_nothing() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(assert (match l (((cons _ t) (+ 1 (length t))) (_ 0))))",
    );
    assert_eq!(
        handler.events,
        [
            "start-match l",
            "start-case (cons _ t)",
            "end-case (+ 1 (length $t))",
            "start-case _",
            "end-case 0",
            "end-match",
            "assert (match l)",
        ]
    );
}

#[test]
fn match_case_variables_are_scoped_to_their_case() {
    // `x` is bound in the first case only, `y` in the second only
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(assert (match a ((x (f x y)) (y (f x y)))))",
    );
    assert_eq!(
        handler.events,
        [
            "start-match a",
            "start-case x",
            "end-case (f $x y)",
            "start-case y",
            "end-case (f x $y)",
            "end-match",
            "assert (match a)",
        ]
    );
}

#[test]
fn nested_match_in_a_case_body_sees_the_outer_case_variables() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(assert (match a ((x (match b ((y (f x y))))) (y (f x y)))))",
    );
    assert_eq!(
        handler.events,
        [
            "start-match a",
            "start-case x",
            "start-match b",
            "start-case y",
            // both the outer and the inner case variable are in scope
            "end-case (f $x $y)",
            "end-match",
            "end-case (match b)",
            "start-case y",
            // the first case has ended, so `x` is no longer bound
            "end-case (f x $y)",
            "end-match",
            "assert (match a)",
        ]
    );
}

#[test]
fn nested_match_in_the_scrutinee_completes_first() {
    let mut handler = Resolving::default();
    parse_resolving(&mut handler, b"(assert (match (match a ((x x))) ((y y))))");
    assert_eq!(
        handler.events,
        [
            "start-match a",
            "start-case x",
            "end-case $x",
            "end-match",
            "start-match (match a)",
            "start-case y",
            "end-case $y",
            "end-match",
            "assert (match (match a))",
        ]
    );
}

#[test]
fn match_inside_a_function_body_sees_the_parameters() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(define-fun f ((p Int)) Int (match p ((z (+ z p)) (p p))))",
    );
    assert_eq!(
        handler.events,
        [
            "start f ((p Int)) Int",
            "start-match [p]",
            "start-case z",
            "end-case (+ $z [p])",
            "start-case p",
            // the case variable shadows the parameter
            "end-case $p",
            "end-match",
            "end (match [p])",
        ]
    );
}

#[test]
fn match_handler_errors_point_at_the_triggering_token() {
    // start_match: the last token of the scrutinee
    let handler = assert_handler_error(
        b"(assert (match forbidden ((x 1))))",
        "forbidden scrutinee",
        15,
        24,
    );
    assert!(handler.events.is_empty());

    // start_match_case: the last token of the pattern, whether the
    // symbol itself or the closing parenthesis of the application
    let handler = assert_handler_error(
        b"(assert (match s ((unstartable 1))))",
        "unstartable case",
        19,
        30,
    );
    assert_eq!(handler.events, ["start-match s"]);
    let handler = assert_handler_error(
        b"(assert (match s (((unstartable a) 1))))",
        "unstartable case",
        33,
        34,
    );
    assert_eq!(handler.events, ["start-match s"]);

    // end_match_case: the last token of the case body, whether a symbol
    // or the closing parenthesis of a compound term
    let handler = assert_handler_error(b"(assert (match s ((x boom))))", "exploding case", 21, 25);
    assert_eq!(handler.events, ["start-match s", "start-case x"]);
    let handler = assert_handler_error(
        b"(assert (match s ((x (let ((y 1)) boom)))))",
        "exploding case",
        38,
        39,
    );
    assert_eq!(handler.events, ["start-match s", "start-case x"]);

    // end_match: the closing parenthesis of the case list
    let handler = assert_handler_error(
        b"(assert (match unendable ((x 1))))",
        "unendable match",
        31,
        32,
    );
    assert_eq!(
        handler.events,
        ["start-match unendable", "start-case x", "end-case 1"]
    );
}

// --- get-value ---

#[test]
fn get_value_delivers_terms_in_order() {
    let mut handler = Resolving::default();
    parse_resolving(&mut handler, b"(get-value (x (f 1 y) (let ((z 2)) z)))");
    assert_eq!(handler.events, ["get-value (x (f 1 y) z)"]);
}

#[test]
fn repeated_get_values_reuse_the_persistent_parser() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(get-value (a b)) (get-value (c)) (get-value ((g a)))",
    );
    assert_eq!(
        handler.events,
        ["get-value (a b)", "get-value (c)", "get-value ((g a))"]
    );
}

#[test]
fn get_value_terms_do_not_see_the_previous_definition_scope() {
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(define-fun g ((x Int)) Int x) (get-value (x (g x)))",
    );
    assert_eq!(
        handler.events,
        ["start g ((x Int)) Int", "end [x]", "get-value (x (g x))"]
    );
}

#[test]
fn get_value_handler_error_points_at_the_closing_parenthesis_of_the_command() {
    // the handler is called once the whole command is parsed
    let handler = assert_handler_error(b"(get-value (x boom))", "exploding get-value", 19, 20);
    assert!(handler.events.is_empty());
}

#[test]
fn get_value_errors_point_at_offending_token() {
    // at least one term is required
    let err = assert_parser_error(b"(get-value ())", 12, 13);
    assert!(
        matches!(err, SmtSyntaxErrorKind::EmptyGetValueTerms),
        "{err:?}"
    );
    // the term list is required and parenthesized
    let err = assert_parser_error(b"(get-value)", 10, 11);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    let err = assert_parser_error(b"(get-value x)", 11, 12);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen])
        ),
        "{err:?}"
    );
    // the list holds terms, which are checked as terms
    let err = assert_parser_error(b"(get-value ((f)))", 14, 15);
    assert!(
        matches!(err, SmtSyntaxErrorKind::EmptyTermApplication),
        "{err:?}"
    );
    // nothing follows the term list
    let err = assert_parser_error(b"(get-value (x) 1)", 15, 16);
    assert!(
        matches!(
            err,
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose])
        ),
        "{err:?}"
    );
}

// --- Argument-free queries ---

#[test]
fn argument_free_queries_are_dispatched_by_name() {
    // each query, repeated, to exercise dispatch and parser reuse
    let mut handler = Resolving::default();
    parse_resolving(
        &mut handler,
        b"(get-model) (get-unsat-core) (get-model) (get-proof) (get-assertions) \
          (get-assignment) (get-unsat-assumptions) (get-unsat-core)",
    );
    assert_eq!(
        handler.events,
        [
            "get-model",
            "get-unsat-core",
            "get-model",
            "get-proof",
            "get-assertions",
            "get-assignment",
            "get-unsat-assumptions",
            "get-unsat-core",
        ]
    );
}

//! The Rust backend: the library's parser calls a test handler through an
//! adapter that turns the views it hands over into owned values.

use blazing_smtlib::{
    SmtAttributeValue, SmtAttributes, SmtBindings, SmtCommandHandler, SmtConstructors,
    SmtFunctionSignature, SmtFunctionSignatures, SmtHandler, SmtIdent, SmtKeyword, SmtMatchCases,
    SmtMultiple, SmtNumeral, SmtPattern, SmtQualifiedIdent, SmtQuantifierKind, SmtSExpr, SmtSort,
    SmtSortArities, SmtSortedVars, SmtStringContent, SmtSymbol, SmtSymbols, SmtTerm,
    parser::{SmtClosedParser, SmtCommandPayloadParser, SmtCommandRule, SmtTermParser},
    token::SmtVersion,
};

use super::nodes::{
    Application, AttributeValue, CommandHandler, Handler, QualifiedIdent, SExpr, Signature, Sort,
    SortedVars, Term,
};

/// A test handler as the library's handler.
pub struct Adapt<'h, H>(pub &'h mut H);

fn qualified_ident<A: SmtHandler>(view: SmtQualifiedIdent<'_, A>) -> QualifiedIdent<A::Sort> {
    QualifiedIdent {
        ident: SmtIdent::into_owned(view.ident),
        sort: view.sort,
    }
}

fn sorted_vars<S>(vars: SmtSortedVars<'_, S>) -> SortedVars<S> {
    vars.into_iter()
        .map(|(name, sort)| (name.into_owned(), sort))
        .collect()
}

fn signature<'a, S>(view: SmtFunctionSignature<'a, S>) -> Signature<'a, S> {
    Signature {
        name: view.name().into_owned(),
        params: view
            .params()
            .map(|(name, sort)| (name.into_owned(), sort))
            .collect(),
        result_sort: view.result_sort(),
    }
}

fn constructors<S>(
    view: SmtConstructors<'_, S>,
) -> Vec<(blazing_smtlib::SmtSymbolBuf, SortedVars<S>)> {
    view.into_iter()
        .map(|(name, selectors)| (name.into_owned(), sorted_vars(selectors)))
        .collect()
}

fn symbols(view: SmtSymbols<'_>) -> Vec<blazing_smtlib::SmtSymbolBuf> {
    view.iter().map(SmtSymbol::into_owned).collect()
}

impl<H: Handler> SmtHandler for Adapt<'_, H> {
    type Error = H::Error;
    type SExpr = H::SExpr;
    type Attribute = H::Attribute;
    type Sort = H::Sort;
    type Term = H::Term;
    type Scope = H::Scope;

    fn set_version(&mut self, version: SmtVersion) {
        self.0.set_version(version)
    }

    fn handle_sort(&mut self, sort: SmtSort<'_, Self>) -> Result<H::Sort, H::Error> {
        self.0.handle_sort(Sort {
            ident: sort.ident.into_owned(),
            applied: sort.applied.into_iter().collect(),
        })
    }

    fn handle_term(&mut self, term: SmtTerm<'_, Self>) -> Result<H::Term, H::Error> {
        let term = match term {
            SmtTerm::SpecialConstant(constant) => Term::SpecialConstant(constant.into_owned()),
            SmtTerm::QualifiedIdent(ident) => Term::QualifiedIdent(qualified_ident(ident)),
            SmtTerm::Application(application) => Term::Application(Application {
                function: qualified_ident(application.function),
                args: application.args.into_iter().collect(),
            }),
        };
        self.0.handle_term(term)
    }

    fn handle_s_expr(&mut self, expr: SmtSExpr<'_, Self>) -> Result<H::SExpr, H::Error> {
        let expr = match expr {
            SmtSExpr::SpecialConstant(constant) => SExpr::SpecialConstant(constant.into_owned()),
            SmtSExpr::Symbol(symbol) => SExpr::Symbol(symbol.into_owned()),
            SmtSExpr::Reserved(reserved) => SExpr::Reserved(reserved),
            SmtSExpr::Keyword(keyword) => SExpr::Keyword(keyword.into_owned()),
            SmtSExpr::SExprs(exprs) => SExpr::SExprs(exprs.into_iter().collect()),
        };
        self.0.handle_s_expr(expr)
    }

    fn handle_attribute(
        &mut self,
        name: SmtKeyword<'_>,
        value: Option<SmtAttributeValue<'_, Self>>,
    ) -> Result<H::Attribute, H::Error> {
        let value = value.map(|value| match value {
            SmtAttributeValue::SpecialConstant(constant) => {
                AttributeValue::SpecialConstant(constant.into_owned())
            }
            SmtAttributeValue::Symbol(symbol) => AttributeValue::Symbol(symbol.into_owned()),
            SmtAttributeValue::SExprs(exprs) => AttributeValue::SExprs(exprs.into_iter().collect()),
        });
        self.0.handle_attribute(name.into_owned(), value)
    }

    fn annotate_term(
        &mut self,
        term: H::Term,
        attributes: SmtAttributes<'_, Self>,
    ) -> Result<H::Term, H::Error> {
        self.0.annotate_term(term, attributes.into_iter().collect())
    }

    fn start_let(&mut self, bindings: SmtBindings<'_, H::Term>) -> Result<H::Scope, H::Error> {
        self.0.start_let(sorted_vars(bindings))
    }

    fn end_let(&mut self, scope: H::Scope, body: H::Term) -> Result<H::Term, H::Error> {
        self.0.end_let(scope, body)
    }

    fn start_quantifier(
        &mut self,
        kind: SmtQuantifierKind,
        vars: SmtSortedVars<'_, H::Sort>,
    ) -> Result<H::Scope, H::Error> {
        self.0.start_quantifier(kind, sorted_vars(vars))
    }

    fn end_quantifier(
        &mut self,
        kind: SmtQuantifierKind,
        scope: H::Scope,
        body: H::Term,
    ) -> Result<H::Term, H::Error> {
        self.0.end_quantifier(kind, scope, body)
    }

    fn start_lambda(&mut self, vars: SmtSortedVars<'_, H::Sort>) -> Result<H::Scope, H::Error> {
        self.0.start_lambda(sorted_vars(vars))
    }

    fn end_lambda(&mut self, scope: H::Scope, body: H::Term) -> Result<H::Term, H::Error> {
        self.0.end_lambda(scope, body)
    }

    fn start_match(&mut self, scrutinee: &H::Term) -> Result<(), H::Error> {
        self.0.start_match(scrutinee)
    }

    fn start_match_case(
        &mut self,
        scrutinee: &H::Term,
        pattern: SmtPattern<'_>,
    ) -> Result<H::Scope, H::Error> {
        self.0.start_match_case(scrutinee, pattern.into_owned())
    }

    fn end_match_case(
        &mut self,
        scope: H::Scope,
        scrutinee: &H::Term,
        term: H::Term,
    ) -> Result<H::Term, H::Error> {
        self.0.end_match_case(scope, scrutinee, term)
    }

    fn end_match(
        &mut self,
        scrutinee: H::Term,
        cases: SmtMatchCases<'_, Self>,
    ) -> Result<H::Term, H::Error> {
        let cases = cases
            .into_iter()
            .map(|(pattern, term)| (pattern.into_owned(), term))
            .collect();
        self.0.end_match(scrutinee, cases)
    }
}

/// The rule of a nonstandard command that the test handler accepts: one term,
/// then the closing parenthesis.
pub struct NonstandardRule;

impl<'h, H: CommandHandler> SmtCommandRule<Adapt<'h, H>> for NonstandardRule {
    type Parser = SmtClosedParser<Adapt<'h, H>, SmtTermParser<Adapt<'h, H>>>;

    fn handle(handler: &mut Adapt<'h, H>, term: H::Term) -> Result<(), H::Error> {
        handler.0.nonstandard_term(term)
    }
}

impl<'h, H: CommandHandler> SmtCommandHandler for Adapt<'h, H> {
    type NonstandardParser = SmtCommandPayloadParser<Self, NonstandardRule>;

    fn nonstandard_command(
        &mut self,
        name: SmtSymbol<'_>,
    ) -> Result<Self::NonstandardParser, H::Error> {
        self.0
            .nonstandard_command(name.into_owned())
            .map(|_| SmtCommandPayloadParser::default())
    }

    fn command_echo(&mut self, value: SmtStringContent<'_>) -> Result<(), H::Error> {
        self.0.command_echo(value.into_owned())
    }

    fn command_get_option(&mut self, option: SmtKeyword<'_>) -> Result<(), H::Error> {
        self.0.command_get_option(option.into_owned())
    }

    fn command_set_option(&mut self, option: H::Attribute) -> Result<(), H::Error> {
        self.0.command_set_option(option)
    }

    fn command_get_info(&mut self, keyword: SmtKeyword<'_>) -> Result<(), H::Error> {
        self.0.command_get_info(keyword.into_owned())
    }

    fn command_set_info(&mut self, attribute: H::Attribute) -> Result<(), H::Error> {
        self.0.command_set_info(attribute)
    }

    fn command_set_logic(&mut self, logic: SmtSymbol<'_>) -> Result<(), H::Error> {
        self.0.command_set_logic(logic.into_owned())
    }

    fn command_get_value(&mut self, terms: SmtMultiple<'_, H::Term>) -> Result<(), H::Error> {
        self.0.command_get_value(terms.into_iter().collect())
    }

    fn command_get_assertions(&mut self) -> Result<(), H::Error> {
        self.0.command_get_assertions()
    }

    fn command_get_assignment(&mut self) -> Result<(), H::Error> {
        self.0.command_get_assignment()
    }

    fn command_get_model(&mut self) -> Result<(), H::Error> {
        self.0.command_get_model()
    }

    fn command_get_proof(&mut self) -> Result<(), H::Error> {
        self.0.command_get_proof()
    }

    fn command_get_unsat_assumptions(&mut self) -> Result<(), H::Error> {
        self.0.command_get_unsat_assumptions()
    }

    fn command_get_unsat_core(&mut self) -> Result<(), H::Error> {
        self.0.command_get_unsat_core()
    }

    fn command_declare_sort(
        &mut self,
        name: SmtSymbol<'_>,
        arity: SmtNumeral<'_>,
    ) -> Result<(), H::Error> {
        self.0
            .command_declare_sort(name.into_owned(), arity.into_owned())
    }

    fn command_declare_sort_parameter(&mut self, name: SmtSymbol<'_>) -> Result<(), H::Error> {
        self.0.command_declare_sort_parameter(name.into_owned())
    }

    fn command_declare_const(
        &mut self,
        name: SmtSymbol<'_>,
        sort: H::Sort,
    ) -> Result<(), H::Error> {
        self.0.command_declare_const(name.into_owned(), sort)
    }

    fn command_declare_fun(
        &mut self,
        name: SmtSymbol<'_>,
        param_sorts: SmtMultiple<'_, H::Sort>,
        result_sort: H::Sort,
    ) -> Result<(), H::Error> {
        self.0.command_declare_fun(
            name.into_owned(),
            param_sorts.into_iter().collect(),
            result_sort,
        )
    }

    fn command_assert(&mut self, term: H::Term) -> Result<(), H::Error> {
        self.0.command_assert(term)
    }

    fn command_check_sat(&mut self) -> Result<(), H::Error> {
        self.0.command_check_sat()
    }

    fn command_check_sat_assuming(
        &mut self,
        assumptions: SmtMultiple<'_, H::Term>,
    ) -> Result<(), H::Error> {
        self.0
            .command_check_sat_assuming(assumptions.into_iter().collect())
    }

    fn command_reset(&mut self) -> Result<(), H::Error> {
        self.0.command_reset()
    }

    fn command_reset_assertions(&mut self) -> Result<(), H::Error> {
        self.0.command_reset_assertions()
    }

    fn command_exit(&mut self) -> Result<(), H::Error> {
        self.0.command_exit()
    }

    fn command_push(&mut self, amount: SmtNumeral<'_>) -> Result<(), H::Error> {
        self.0.command_push(amount.into_owned())
    }

    fn command_pop(&mut self, amount: SmtNumeral<'_>) -> Result<(), H::Error> {
        self.0.command_pop(amount.into_owned())
    }

    fn start_define_sort(
        &mut self,
        name: SmtSymbol<'_>,
        params: SmtSymbols<'_>,
    ) -> Result<(), H::Error> {
        self.0.start_define_sort(name.into_owned(), symbols(params))
    }

    fn end_define_sort(&mut self, sort: H::Sort) -> Result<(), H::Error> {
        self.0.end_define_sort(sort)
    }

    fn start_define_fun(
        &mut self,
        signature_view: SmtFunctionSignature<'_, H::Sort>,
    ) -> Result<(), H::Error> {
        self.0.start_define_fun(signature(signature_view))
    }

    fn command_define_const(
        &mut self,
        name: SmtSymbol<'_>,
        sort: H::Sort,
        body: H::Term,
    ) -> Result<(), H::Error> {
        self.0.command_define_const(name.into_owned(), sort, body)
    }

    fn end_define_fun(&mut self, term: H::Term) -> Result<(), H::Error> {
        self.0.end_define_fun(term)
    }

    fn start_define_fun_rec(
        &mut self,
        signature_view: SmtFunctionSignature<'_, H::Sort>,
    ) -> Result<(), H::Error> {
        self.0.start_define_fun_rec(signature(signature_view))
    }

    fn end_define_fun_rec(&mut self, body: H::Term) -> Result<(), H::Error> {
        self.0.end_define_fun_rec(body)
    }

    fn start_define_funs_rec(
        &mut self,
        signatures: SmtFunctionSignatures<'_, H::Sort>,
    ) -> Result<(), H::Error> {
        self.0
            .start_define_funs_rec(signatures.into_iter().map(signature).collect())
    }

    fn end_define_funs_rec(&mut self) -> Result<(), H::Error> {
        self.0.end_define_funs_rec()
    }

    fn start_recursive_body(
        &mut self,
        signature_view: SmtFunctionSignature<'_, H::Sort>,
    ) -> Result<(), H::Error> {
        self.0.start_recursive_body(signature(signature_view))
    }

    fn end_recursive_body(&mut self, term: H::Term) -> Result<(), H::Error> {
        self.0.end_recursive_body(term)
    }

    fn start_declare_datatype(
        &mut self,
        name: SmtSymbol<'_>,
        params: SmtSymbols<'_>,
    ) -> Result<(), H::Error> {
        self.0
            .start_declare_datatype(name.into_owned(), symbols(params))
    }

    fn end_declare_datatype(
        &mut self,
        constructors_view: SmtConstructors<'_, H::Sort>,
    ) -> Result<(), H::Error> {
        self.0.end_declare_datatype(constructors(constructors_view))
    }

    fn start_declare_datatypes(
        &mut self,
        introductions: SmtSortArities<'_>,
    ) -> Result<(), H::Error> {
        self.0.start_declare_datatypes(
            introductions
                .into_iter()
                .map(|(name, arity)| (name.into_owned(), arity.into_owned()))
                .collect(),
        )
    }

    fn end_declare_datatypes(&mut self) -> Result<(), H::Error> {
        self.0.end_declare_datatypes()
    }

    fn start_datatype_declaration(&mut self, sort_params: SmtSymbols<'_>) -> Result<(), H::Error> {
        self.0.start_datatype_declaration(symbols(sort_params))
    }

    fn end_datatype_declaration(
        &mut self,
        constructors_view: SmtConstructors<'_, H::Sort>,
    ) -> Result<(), H::Error> {
        self.0
            .end_datatype_declaration(constructors(constructors_view))
    }
}

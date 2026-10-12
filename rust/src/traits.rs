use std::{convert::Infallible, fmt::Debug};

use crate::{
    SmtAttributeValue, SmtAttributes, SmtBindings, SmtDatatypeConstructor, SmtFunctionSignature,
    SmtFunctionSignatures, SmtKeyword, SmtMatchCases, SmtMultiple, SmtNumeral, SmtNumeralBuf,
    SmtPattern, SmtQuantifierKind, SmtSExpr, SmtSort, SmtSortedVars, SmtStringContent, SmtSymbol,
    SmtSymbolBuf, SmtSymbols, SmtTerm, parser::SmtParse, token::SmtVersion,
};

pub trait SmtHandler {
    type Error;

    type SExpr;
    type Attribute;
    type Sort;
    type Term;

    type Scope;

    /// Informs the handler of the SMT-LIB version in force.
    ///
    /// The caller must set the version before calling
    /// other methods so the handler can process them
    /// according to the version semantics.
    ///
    /// The handler should start in [`SmtVersion::default`].
    ///
    /// In the library,
    /// [`SmtParseAdapter`](crate::parser::SmtParseAdapter)
    /// calls this method before any other calls, and
    /// [`SmtScriptParser`](crate::parser::SmtScriptParser)
    /// calls this method when switching versions.
    fn set_version(&mut self, version: SmtVersion);

    fn handle_sort(&mut self, sort: SmtSort<'_, Self>) -> Result<Self::Sort, Self::Error>;
    fn handle_term(&mut self, term: SmtTerm<'_, Self>) -> Result<Self::Term, Self::Error>;
    fn handle_s_expr(&mut self, expr: SmtSExpr<'_, Self>) -> Result<Self::SExpr, Self::Error>;
    fn handle_attribute(
        &mut self,
        name: SmtKeyword<'_>,
        value: Option<SmtAttributeValue<'_, Self>>,
    ) -> Result<Self::Attribute, Self::Error>;

    fn annotate_term(
        &mut self,
        term: Self::Term,
        attributes: SmtAttributes<'_, Self>,
    ) -> Result<Self::Term, Self::Error>;

    fn start_let(
        &mut self,
        bindings: SmtBindings<'_, Self::Term>,
    ) -> Result<Self::Scope, Self::Error>;
    fn end_let(&mut self, scope: Self::Scope, body: Self::Term) -> Result<Self::Term, Self::Error>;

    fn start_quantifier(
        &mut self,
        kind: SmtQuantifierKind,
        vars: SmtSortedVars<'_, Self::Sort>,
    ) -> Result<Self::Scope, Self::Error>;
    fn end_quantifier(
        &mut self,
        kind: SmtQuantifierKind,
        scope: Self::Scope,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error>;

    fn start_lambda(
        &mut self,
        vars: SmtSortedVars<'_, Self::Sort>,
    ) -> Result<Self::Scope, Self::Error>;
    fn end_lambda(
        &mut self,
        scope: Self::Scope,
        body: Self::Term,
    ) -> Result<Self::Term, Self::Error>;

    /// Starts a match term.
    ///
    /// The parameter `scrutinee` is the term being matched.
    /// The parser calls this method before any match case is started,
    /// as the patterns can only be interpreted knowing the scrutinee.
    ///
    /// The parser guarantees:
    /// 1. If this method is nested, i.e. called again before the corresponding
    ///    `end_match`, from within a match case body, the nesting is proper:
    ///    the inner match ends before the outer match continues.
    /// 2. There is at least one match case, its body handled between
    ///    `start_match_case` and `end_match_case`, before the corresponding `end_match`.
    ///
    /// There are no other guarantees, including on the sort of the scrutinee.
    ///
    /// Consult the standard for proper handling.
    fn start_match(&mut self, scrutinee: &Self::Term) -> Result<(), Self::Error>;

    /// Starts a match case.
    ///
    /// The parameter `pattern` is the case pattern.
    ///
    /// The parser guarantees:
    /// 1. This method is only called between `start_match` and `end_match`,
    ///    and the case semantically belongs to the innermost match.
    /// 2. This method is never nested before the corresponding `end_match_case`.
    /// 3. The case body is handled after this method is called
    ///    and before the respective `end_match_case` is called.
    /// 4. If `pattern` is a constructor application pattern,
    ///    it has at least one argument.
    ///
    /// There are no other guarantees, including on constructor names, arities,
    /// or distinctness of pattern variables.
    ///
    /// Consult the standard for proper handling.
    fn start_match_case(
        &mut self,
        scrutinee: &Self::Term,
        pattern: SmtPattern<'_>,
    ) -> Result<Self::Scope, Self::Error>;

    /// Ends a match case.
    ///
    /// The parameter `term` is the case body result.
    ///
    /// The parser guarantees:
    /// 1. This method is only called between `start_match` and `end_match`.
    /// 2. There is a pending unended `start_match_case`,
    ///    to which this method semantically belongs.
    ///
    /// Consult the standard for proper handling.
    fn end_match_case(
        &mut self,
        scope: Self::Scope,
        scrutinee: &Self::Term,
        term: Self::Term,
    ) -> Result<Self::Term, Self::Error>;

    /// Ends a match term.
    ///
    /// The parser guarantees:
    /// 1. There is a pending unended `start_match`,
    ///    to which this method semantically belongs.
    /// 2. There is no pending unended `start_match_case`.
    /// 3. At least one match case was ended since the corresponding `start_match`.
    ///
    /// The result of this method should be the handled match term.
    ///
    /// Consult the standard for proper handling.
    fn end_match(
        &mut self,
        scrutinee: Self::Term,
        cases: SmtMatchCases<'_, Self>,
    ) -> Result<Self::Term, Self::Error>;
}

pub trait SmtCommandHandler: SmtHandler {
    type NonstandardParser: SmtParse<Self, Result = ()>;

    /// Returns a parser that parses a non-standard command with the given name.
    fn nonstandard_command(
        &mut self,
        name: SmtSymbol<'_>,
    ) -> Result<Self::NonstandardParser, Self::Error>;

    fn command_echo(&mut self, value: SmtStringContent<'_>) -> Result<(), Self::Error>;

    fn command_get_option(&mut self, option: SmtKeyword<'_>) -> Result<(), Self::Error>;
    fn command_set_option(&mut self, option: Self::Attribute) -> Result<(), Self::Error>;
    fn command_get_info(&mut self, keyword: SmtKeyword<'_>) -> Result<(), Self::Error>;
    fn command_set_info(&mut self, attribute: Self::Attribute) -> Result<(), Self::Error>;

    fn command_set_logic(&mut self, logic: SmtSymbol<'_>) -> Result<(), Self::Error>;

    fn command_get_value(&mut self, terms: SmtMultiple<'_, Self::Term>) -> Result<(), Self::Error>;
    fn command_get_assertions(&mut self) -> Result<(), Self::Error>;
    fn command_get_assignment(&mut self) -> Result<(), Self::Error>;
    fn command_get_model(&mut self) -> Result<(), Self::Error>;
    fn command_get_proof(&mut self) -> Result<(), Self::Error>;
    fn command_get_unsat_assumptions(&mut self) -> Result<(), Self::Error>;
    fn command_get_unsat_core(&mut self) -> Result<(), Self::Error>;

    /// Adds a sort symbol with an associated arity.
    ///
    /// As per the standard, the handler should return an error if `name`
    /// is a sort symbol or parameter that is already present in the current signature.
    fn command_declare_sort(
        &mut self,
        name: SmtSymbol<'_>,
        arity: SmtNumeral<'_>,
    ) -> Result<(), Self::Error>;

    /// Adds a global sort parameter `name` to the current signature.
    ///
    /// As per the standard, the handler should return an error
    /// if `name` is a sort symbol, sort parameter, or theory symbol
    /// that is already present in the current signature.
    fn command_declare_sort_parameter(&mut self, name: SmtSymbol<'_>) -> Result<(), Self::Error>;

    /// Declares a constant (`declare-const`).
    ///
    /// Semantically, `declare-const` is syntax sugar for
    /// `declare-fun` without any parameters.
    fn command_declare_const(
        &mut self,
        name: SmtSymbol<'_>,
        sort: Self::Sort,
    ) -> Result<(), Self::Error>;

    /// Declares a function (`declare-fun`).
    fn command_declare_fun(
        &mut self,
        name: SmtSymbol<'_>,
        param_sorts: SmtMultiple<'_, Self::Sort>,
        result_sort: Self::Sort,
    ) -> Result<(), Self::Error>;

    fn command_assert(&mut self, term: Self::Term) -> Result<(), Self::Error>;

    /// Checks satisfiability (`check-sat`).
    ///
    /// Semantically, command `check-sat` is syntax sugar for
    /// `check-sat-assuming` without additional assumptions.
    fn command_check_sat(&mut self) -> Result<(), Self::Error>;

    /// Checks satisfiability with additional assumptions (`check-sat-assuming`).
    ///
    /// The command `check-sat-assuming` triggers checking satisfiability
    /// of the conjunction of the assertions in the current context
    /// and additional assumptions given within the command.
    fn command_check_sat_assuming(
        &mut self,
        assumptions: SmtMultiple<'_, Self::Term>,
    ) -> Result<(), Self::Error>;

    fn command_reset(&mut self) -> Result<(), Self::Error>;

    fn command_reset_assertions(&mut self) -> Result<(), Self::Error>;

    fn command_exit(&mut self) -> Result<(), Self::Error>;

    /// Pushes `amount` of empty assertion levels onto the assertion stack.
    ///
    /// If `amount` is 0, no levels are pushed (i.e. successful no-op).
    fn command_push(&mut self, amount: SmtNumeral<'_>) -> Result<(), Self::Error>;

    /// Pops `amount` of assertion levels from the assertion stack.
    ///
    /// If `amount` is 0, no levels are popped (i.e. successful no-op).
    ///
    /// As per the standard, the handler should return an error
    /// when popping more than the amount of remaining assertion levels
    /// beyond the inherent first assertion level.
    fn command_pop(&mut self, amount: SmtNumeral<'_>) -> Result<(), Self::Error>;

    /// Starts sort definition (in `define-sort`).
    ///
    /// The handler should bring `params` into scope as local sort parameters
    /// before the body sort is handled. As per the standard, they shadow
    /// previously user-declared sort symbols and parameters of the same name,
    /// but not theory sort symbols.
    ///
    /// As per the standard, the handler should return an error
    /// 1. if `name` is a sort symbol or parameter already present in the current signature,
    /// 2. if a theory sort symbol is used as a sort parameter.
    fn start_define_sort(
        &mut self,
        name: SmtSymbol<'_>,
        params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error>;

    /// Ends sort definition (in `define-sort`).
    ///
    /// As per the standard, the handler should return an error
    /// if `sort` is not a well-defined (polymorphic) sort with respect to the
    /// current signature extended with the sort parameters.
    fn end_define_sort(&mut self, sort: Self::Sort) -> Result<(), Self::Error>;

    /// Starts function definition body (in `define-fun`).
    fn start_define_fun(
        &mut self,
        signature: SmtFunctionSignature<'_, Self::Sort>,
    ) -> Result<(), Self::Error>;

    /// Defines a constant (`define-const`).
    ///
    /// The command `define-const` is syntax sugar for `define-fun`
    /// without parameters.
    fn command_define_const(
        &mut self,
        name: SmtSymbol<'_>,
        sort: Self::Sort,
        body: Self::Term,
    ) -> Result<(), Self::Error>;

    /// Ends function definition body (in `define-fun`).
    fn end_define_fun(&mut self, term: Self::Term) -> Result<(), Self::Error>;

    /// Starts a recursive function definition (`define-fun-rec`).
    fn start_define_fun_rec(
        &mut self,
        signature: SmtFunctionSignature<'_, Self::Sort>,
    ) -> Result<(), Self::Error>;

    /// Ends a recursive function definition (`define-fun-rec`).
    fn end_define_fun_rec(&mut self, body: Self::Term) -> Result<(), Self::Error>;

    /// Starts recursive function definitions (`define-funs-rec`).
    ///
    /// The parser guarantees:
    /// 1. This method is never nested before the corresponding `end_define_funs_rec`.
    /// 2. The parameter `signatures` is nonempty and contains all signatures
    ///    of functions to be defined.
    /// 3. Exactly one body per signature, in the same order, is delivered
    ///    between `start_recursive_body` and `end_recursive_body` before
    ///    the corresponding `end_define_funs_rec`.
    ///
    /// All signatures arrive before any body is started, as every body may
    /// refer to every defined function within the recursive function definitions.
    /// The function names in `signatures` are in scope from this method call onwards,
    /// while the function parameters are only in scope between the corresponding
    /// `start_recursive_body` and `end_recursive_body`.
    ///
    /// The command `define-fun-rec` is just syntax sugar for
    /// `define-funs-rec` with a single function. It is desugared before being handled.
    ///
    /// Consult the standard for proper handling.
    fn start_define_funs_rec(
        &mut self,
        signatures: SmtFunctionSignatures<'_, Self::Sort>,
    ) -> Result<(), Self::Error>;

    /// Ends recursive function definitions (in `define-funs-rec`).
    ///
    /// The parser guarantees:
    /// 1. There is a pending unended `start_define_funs_rec`.
    /// 2. There is no pending unended `start_recursive_body`.
    ///
    /// The command `define-fun-rec` is just syntax sugar for
    /// `define-funs-rec` with a single function. It is desugared before being handled.
    ///
    /// Consult the standard for proper handling.
    fn end_define_funs_rec(&mut self) -> Result<(), Self::Error>;

    /// Starts the body of a recursive function (in `define-fun-rec` / `define-funs-rec`).
    ///
    /// The parser guarantees:
    /// 1. This method is only called between `start_define_funs_rec` and `end_define_funs_rec`.
    /// 2. This method is never nested before the corresponding `end_recursive_body`.
    /// 3. This body corresponds to the signature at the same index in `start_define_funs_rec`.
    /// 4. The body of this function definition is handled after this method is called
    ///    and before the respective `end_recursive_body` is called.
    ///
    /// The command `define-fun-rec` is just syntax sugar for
    /// `define-funs-rec` with a single function. It is desugared before being handled.
    ///
    /// Consult the standard for proper handling.
    fn start_recursive_body(&mut self) -> Result<(), Self::Error>;

    /// Ends the body of a recursive function (in `define-funs-rec`).
    ///
    /// The parameter `term` is the result term of the function definition body.
    ///
    /// The parser guarantees:
    /// 1. This method is only called between `start_define_funs_rec` and `end_define_funs_rec`.
    /// 2. There is a pending unended `start_recursive_body`.
    ///
    /// Consult the standard for proper handling.
    fn end_recursive_body(&mut self, term: Self::Term) -> Result<(), Self::Error>;

    /// Starts a datatype declaration (`declare-datatype`).
    fn start_declare_datatype(
        &mut self,
        name: SmtSymbolBuf,
        params: Vec<SmtSymbolBuf>,
    ) -> Result<(), Self::Error>;

    /// Ends a datatype declaration (`declare-datatype`).
    fn end_declare_datatype(
        &mut self,
        constructors: Vec<SmtDatatypeConstructor<Self>>,
    ) -> Result<(), Self::Error>;

    /// Starts datatype declarations (`declare-datatypes`).
    ///
    /// The parameter `introductions` contains ordered introductions of
    /// the name and arity of datatypes. The parser calls this method before any
    /// datatype declaration is started, as the sorts can be referenced by selector
    /// sorts of the datatypes.
    ///
    /// The parser guarantees:
    /// 1. This method is never nested before the corresponding `end_declare_datatypes`.
    /// 2. There is at least one datatype introduction, i.e. `introductions` is nonempty.
    /// 3. There is exactly one datatype per introduction,
    ///    arriving in the same order as the introductions.
    ///
    /// There are no other guarantees, including on arities.
    ///
    /// The command `declare-datatype` is just syntax sugar for
    /// `declare-datatypes` with a single introduction where the
    /// arity is the number of parameters of the datatype (zero if there are none).
    /// The command is desugared before being handled.
    ///
    /// Consult the standard for proper handling.
    fn start_declare_datatypes(
        &mut self,
        introductions: Vec<(SmtSymbolBuf, SmtNumeralBuf)>,
    ) -> Result<(), Self::Error>;

    /// Ends datatype declarations (`declare-datatypes`).
    ///
    /// The parser guarantees:
    /// 1. There is a pending unended `start_declare_datatypes`.
    /// 2. There is no pending unended `start_datatype_declaration`.
    ///
    /// Consult the standard for proper handling.
    fn end_declare_datatypes(&mut self) -> Result<(), Self::Error>;

    /// Starts a datatype declaration (in `declare-datatypes`).
    ///
    /// The parser guarantees:
    /// 1. This method is only called between `start_declare_datatypes` and `end_declare_datatypes`.
    /// 2. This method is never nested before the corresponding `end_datatype_declaration`.
    /// 3. This declaration corresponds to the introduction at the same index
    ///    in `start_declare_datatypes`.
    /// 4. The sort parameters (`sort_params`) are nonempty exactly when the datatype is parametric.
    /// 5. The selector sorts of the datatype declaration are handled after this method is called
    ///    and before the respective `end_datatype_declaration` is called.
    ///
    /// There are no other guarantees, including on arities.
    ///
    /// Consult the standard for proper handling.
    fn start_datatype_declaration(
        &mut self,
        sort_params: Vec<SmtSymbolBuf>,
    ) -> Result<(), Self::Error>;

    /// Ends a datatype declaration (in `declare-datatypes` / `declare-datatype`).
    ///
    /// The parser guarantees:
    /// 1. This method is only called between `start_declare_datatypes` and `end_declare_datatypes`.
    /// 2. There is a pending unended `start_datatype_declaration`.
    /// 3. There is at least one datatype constructor, i.e. `constructors` is nonempty.
    ///
    /// There are no other guarantees, including on arities.
    ///
    /// Consult the standard for proper handling.
    fn end_datatype_declaration(
        &mut self,
        constructors: Vec<SmtDatatypeConstructor<Self>>,
    ) -> Result<(), Self::Error>;
}

#[derive(Debug)]
pub struct SmtSyntaxChecker;

#[derive(Debug, Clone)]
pub struct NonstandardCommandError(pub SmtSymbolBuf);

impl SmtHandler for SmtSyntaxChecker {
    type Error = NonstandardCommandError;

    type SExpr = ();
    type Attribute = ();
    type Sort = ();
    type Term = ();

    type Scope = ();

    fn set_version(&mut self, _version: SmtVersion) {}

    fn handle_sort(&mut self, _sort: SmtSort<'_, Self>) -> Result<Self::Sort, Self::Error> {
        Ok(())
    }

    #[inline]
    fn handle_term(&mut self, _term: SmtTerm<'_, Self>) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn handle_s_expr(&mut self, _expr: SmtSExpr<'_, Self>) -> Result<Self::SExpr, Self::Error> {
        Ok(())
    }

    fn handle_attribute(
        &mut self,
        _name: SmtKeyword<'_>,
        _value: Option<SmtAttributeValue<'_, Self>>,
    ) -> Result<Self::Attribute, Self::Error> {
        Ok(())
    }

    fn annotate_term(
        &mut self,
        _term: Self::Term,
        _attributes: SmtAttributes<'_, Self>,
    ) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_let(&mut self, _bindings: SmtBindings<'_, Self::Term>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_let(
        &mut self,
        _scope: Self::Scope,
        _body: Self::Term,
    ) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _vars: SmtSortedVars<'_, Self::Sort>,
    ) -> Result<Self::Scope, Self::Error> {
        Ok(())
    }
    fn end_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _scope: Self::Scope,
        _body: Self::Term,
    ) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_lambda(
        &mut self,
        _vars: SmtSortedVars<'_, Self::Sort>,
    ) -> Result<Self::Scope, Self::Error> {
        Ok(())
    }
    fn end_lambda(
        &mut self,
        _scope: Self::Scope,
        _body: Self::Term,
    ) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_match(&mut self, _scrutinee: &Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_match_case(
        &mut self,
        _scrutinee: &Self::Term,
        _pattern: SmtPattern<'_>,
    ) -> Result<Self::Scope, Self::Error> {
        Ok(())
    }

    fn end_match_case(
        &mut self,
        _scope: Self::Scope,
        _scrutinee: &Self::Term,
        _term: Self::Term,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_match(
        &mut self,
        _scrutinee: Self::Term,
        _cases: SmtMatchCases<'_, Self>,
    ) -> Result<Self::Term, Self::Error> {
        Ok(())
    }
}

impl SmtCommandHandler for SmtSyntaxChecker {
    type NonstandardParser = Infallible;

    fn nonstandard_command(
        &mut self,
        name: SmtSymbol<'_>,
    ) -> Result<Self::NonstandardParser, Self::Error> {
        // reject nonstandard command
        Err(NonstandardCommandError(name.into_owned()))
    }

    fn command_echo(&mut self, _value: SmtStringContent<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_option(&mut self, _option: SmtKeyword<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_option(&mut self, _option: Self::Attribute) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_info(&mut self, _keyword: SmtKeyword<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_info(&mut self, _attribute: Self::Attribute) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_logic(&mut self, _logic: SmtSymbol<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_value(
        &mut self,
        _terms: SmtMultiple<'_, Self::Term>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_assertions(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_assignment(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_model(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_proof(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_unsat_assumptions(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_unsat_core(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_sort(
        &mut self,
        _name: SmtSymbol<'_>,
        _arity: SmtNumeral<'_>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_sort_parameter(&mut self, _name: SmtSymbol<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_fun(
        &mut self,
        _name: SmtSymbol<'_>,
        _param_sorts: SmtMultiple<'_, Self::Sort>,
        _result_sort: Self::Sort,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_assert(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_check_sat(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_reset(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_reset_assertions(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_exit(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_push(&mut self, _amount: SmtNumeral<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_pop(&mut self, _amount: SmtNumeral<'_>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_define_sort(
        &mut self,
        _name: SmtSymbol<'_>,
        _params: SmtSymbols<'_>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_define_sort(&mut self, _sort: Self::Sort) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_define_fun(
        &mut self,
        _signature: SmtFunctionSignature<'_, Self::Sort>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_define_fun(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_define_funs_rec(
        &mut self,
        _signatures: SmtFunctionSignatures<'_, Self::Sort>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_recursive_body(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_recursive_body(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_define_funs_rec(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_declare_datatypes(
        &mut self,
        _sorts: Vec<(SmtSymbolBuf, SmtNumeralBuf)>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_datatype_declaration(
        &mut self,
        _sort_params: Vec<SmtSymbolBuf>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_datatype_declaration(
        &mut self,
        _constructors: Vec<SmtDatatypeConstructor<Self>>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_declare_datatypes(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_const(
        &mut self,
        _name: SmtSymbol<'_>,
        _sort: Self::Sort,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_check_sat_assuming(
        &mut self,
        _assumptions: SmtMultiple<'_, Self::Term>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_define_const(
        &mut self,
        _name: SmtSymbol<'_>,
        _sort: Self::Sort,
        _body: Self::Term,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_define_fun_rec(
        &mut self,
        _signature: SmtFunctionSignature<'_, Self::Sort>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_define_fun_rec(&mut self, _body: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }

    fn start_declare_datatype(
        &mut self,
        _name: SmtSymbolBuf,
        _params: Vec<SmtSymbolBuf>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_declare_datatype(
        &mut self,
        _constructors: Vec<SmtDatatypeConstructor<Self>>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }
}

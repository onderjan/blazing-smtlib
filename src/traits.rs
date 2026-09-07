use std::fmt::Debug;

use crate::{
    SmtAttributeValue, SmtFunctionSignature, SmtKeyword, SmtNumeral, SmtQuantifierKind, SmtSExpr,
    SmtSort, SmtStringContent, SmtSymbol, SmtSymbolView, SmtTerm,
    read::parser::{NoCommandParser, ParseCommand},
};

pub trait SmtHandler {
    type Error;

    type SExpr;
    type Attribute;
    type Sort;
    type Term;

    fn handle_sort(&mut self, sort: SmtSort<Self>) -> Result<Self::Sort, Self::Error>;
    fn handle_term(&mut self, term: SmtTerm<Self>) -> Result<Self::Term, Self::Error>;
    fn handle_s_expr(&mut self, expr: SmtSExpr<Self>) -> Result<Self::SExpr, Self::Error>;
    fn handle_attribute(
        &mut self,
        name: SmtKeyword,
        value: Option<SmtAttributeValue<Self>>,
    ) -> Result<Self::Attribute, Self::Error>;

    fn annotate_term(
        &mut self,
        term: Self::Term,
        attributes: Vec<Self::Attribute>,
    ) -> Result<Self::Term, Self::Error>;

    fn start_let(&mut self, bindings: Vec<(SmtSymbol, Self::Term)>) -> Result<(), Self::Error>;
    fn end_let(&mut self, term: Self::Term) -> Result<Self::Term, Self::Error>;

    fn start_quantifier(
        &mut self,
        kind: SmtQuantifierKind,
        name: SmtSymbol,
        sort: Self::Sort,
    ) -> Result<(), Self::Error>;
    fn end_quantifier(&mut self, term: Self::Term) -> Result<Self::Term, Self::Error>;

    fn start_lambda(&mut self, name: SmtSymbol, sort: Self::Sort) -> Result<(), Self::Error>;
    fn end_lambda(&mut self, term: Self::Term) -> Result<Self::Term, Self::Error>;
}

pub trait CommandHandler: SmtHandler {
    type NonstandardParser: ParseCommand<Self>;

    fn nonstandard_command(
        &mut self,
        name: SmtSymbolView<'_>,
    ) -> Result<Self::NonstandardParser, Self::Error>;

    fn command_echo(&mut self, value: SmtStringContent) -> Result<(), Self::Error>;

    fn command_get_option(&mut self, option: SmtKeyword) -> Result<(), Self::Error>;
    fn command_set_option(&mut self, option: Self::Attribute) -> Result<(), Self::Error>;
    fn command_get_info(&mut self, keyword: SmtKeyword) -> Result<(), Self::Error>;
    fn command_set_info(&mut self, attribute: Self::Attribute) -> Result<(), Self::Error>;

    fn command_set_logic(&mut self, logic: SmtSymbol) -> Result<(), Self::Error>;

    /// Adds a sort symbol with an associated arity.
    ///
    /// As per the standard, the handler should return an error if `name`
    /// is a sort symbol or parameter that is already present in the current signature.
    fn command_declare_sort(
        &mut self,
        name: SmtSymbol,
        arity: SmtNumeral,
    ) -> Result<(), Self::Error>;

    /// Adds a global sort parameter `name` to the current signature.
    ///
    /// As per the standard, the handler should return an error
    /// if `name` is a sort symbol, sort parameter, or theory symbol
    /// that is already present in the current signature.
    fn command_declare_sort_parameter(&mut self, name: SmtSymbol) -> Result<(), Self::Error>;

    /// Performs function declaration (`declare-fun` / `declare-const`).
    ///
    /// The command `declare-const` is just syntax sugar for
    /// `declare-fun` without parameters.
    fn command_declare_fun(
        &mut self,
        name: SmtSymbol,
        param_sorts: Vec<Self::Sort>,
        result_sort: Self::Sort,
    ) -> Result<(), Self::Error>;

    fn command_assert(&mut self, term: Self::Term) -> Result<(), Self::Error>;

    /// Checks satisfiability (`check-sat` / `check-sat-assuming`).
    ///
    /// The command `check-sat-assuming` triggers checking satisfiability
    /// of the conjunction of the assertions in the current context
    /// and additional assumptions given within the command.
    ///
    /// The command `check-sat` is just syntax sugar for
    /// `check-sat-assuming` without additional assumptions.
    fn command_check_sat(&mut self, assumptions: Vec<Self::Term>) -> Result<(), Self::Error>;

    fn command_reset(&mut self) -> Result<(), Self::Error>;

    fn command_reset_assertions(&mut self) -> Result<(), Self::Error>;

    fn command_exit(&mut self) -> Result<(), Self::Error>;

    /// Starts function definition body (in `define-fun` / `define-const`).
    ///
    /// The command `define-const` is just syntax sugar for
    /// `define-fun` without parameters.
    fn start_define_fun(
        &mut self,
        signature: SmtFunctionSignature<Self>,
    ) -> Result<(), Self::Error>;

    /// Ends function definition body (in `define-fun` / `define-const`).
    ///
    /// The command `define-const` is just syntax sugar for
    /// `define-fun` without parameters.
    fn end_define_fun(&mut self, term: Self::Term) -> Result<(), Self::Error>;
}

#[derive(Debug)]
pub struct CheckStandardSyntax;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NonstandardCommandError(pub SmtSymbol);

impl SmtHandler for CheckStandardSyntax {
    type Error = NonstandardCommandError;

    type SExpr = ();
    type Attribute = ();
    type Sort = ();
    type Term = ();

    fn handle_sort(&mut self, _sort: SmtSort<Self>) -> Result<Self::Sort, Self::Error> {
        Ok(())
    }

    fn handle_term(&mut self, _term: SmtTerm<Self>) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn handle_s_expr(&mut self, _expr: SmtSExpr<Self>) -> Result<Self::SExpr, Self::Error> {
        Ok(())
    }

    fn handle_attribute(
        &mut self,
        _name: SmtKeyword,
        _value: Option<SmtAttributeValue<Self>>,
    ) -> Result<Self::Attribute, Self::Error> {
        Ok(())
    }

    fn annotate_term(
        &mut self,
        _term: Self::Term,
        _attributes: Vec<Self::Attribute>,
    ) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_let(&mut self, _bindings: Vec<(SmtSymbol, Self::Term)>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_let(&mut self, _term: Self::Term) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _name: SmtSymbol,
        _sort: Self::Sort,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_quantifier(&mut self, _term: Self::Term) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_lambda(&mut self, _name: SmtSymbol, _sort: Self::Sort) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_lambda(&mut self, _term: Self::Term) -> Result<Self::Term, Self::Error> {
        Ok(())
    }
}

impl CommandHandler for CheckStandardSyntax {
    type NonstandardParser = NoCommandParser;

    fn nonstandard_command(
        &mut self,
        name: SmtSymbolView<'_>,
    ) -> Result<Self::NonstandardParser, Self::Error> {
        // reject nonstandard command
        Err(NonstandardCommandError(name.into_owned()))
    }

    fn command_echo(&mut self, _value: SmtStringContent) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_option(&mut self, _option: SmtKeyword) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_option(&mut self, _option: Self::Attribute) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_info(&mut self, _keyword: SmtKeyword) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_info(&mut self, _attribute: Self::Attribute) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_logic(&mut self, _logic: SmtSymbol) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_sort(
        &mut self,
        _name: SmtSymbol,
        _arity: SmtNumeral,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_sort_parameter(&mut self, _name: SmtSymbol) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_fun(
        &mut self,
        _name: SmtSymbol,
        _param_sorts: Vec<Self::Sort>,
        _result_sort: Self::Sort,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_assert(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_check_sat(&mut self, _assumptions: Vec<Self::Term>) -> Result<(), Self::Error> {
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

    fn start_define_fun(
        &mut self,
        _signature: SmtFunctionSignature<Self>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_define_fun(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }
}

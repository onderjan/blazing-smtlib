use std::convert::Infallible;

use crate::{
    SmtAttributeValue, SmtFold, SmtFunctionSignature, SmtSExpr, SmtSort, SmtTerm, String8,
};

#[derive(Debug)]
pub struct OnlyCheckSyntax;

impl SmtFold for OnlyCheckSyntax {
    type Error = Infallible;
    type SExpr = ();
    type Attribute = ();
    type Sort = ();
    type Term = ();

    fn fold_s_expr(&mut self, _expr: SmtSExpr<Self::SExpr>) -> Result<Self::SExpr, Self::Error> {
        Ok(())
    }

    fn fold_attribute(
        &mut self,
        _name: String8,
        _value: Option<SmtAttributeValue<Self::SExpr>>,
    ) -> Result<Self::Attribute, Self::Error> {
        Ok(())
    }

    fn fold_sort(&mut self, _sort: SmtSort) -> Result<Self::Sort, Self::Error> {
        Ok(())
    }

    fn fold_term(&mut self, _term: SmtTerm<Self::Term>) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_let(&mut self, _bindings: Vec<(String8, Self::Term)>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_let(&mut self, _term: Self::Term) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn command_echo(&mut self, _echo: String8) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_option(&mut self, _option: String8) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_option(&mut self, _option: Self::Attribute) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_info(&mut self, _keyword: String8) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_info(&mut self, _attribute: Self::Attribute) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_logic(&mut self, _logic: String8) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_const(
        &mut self,
        _name: String8,
        _sort: Self::Sort,
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

    fn start_define_fun(
        &mut self,
        _signature: SmtFunctionSignature<Self::Sort>,
    ) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_define_fun(&mut self, _term: Self::Term) -> Result<(), Self::Error> {
        Ok(())
    }
}

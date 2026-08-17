use crate::{SmtAttributeValue, SmtFunctionSignature, SmtSExpr, SmtSort, SmtTerm};

pub struct Str8<'a>(&'a [u8]);

pub trait CategoryHandler {
    type Error;

    type Numeral;
    type Decimal;
    type Hexadecimal;
    type Binary;
    type String;

    type SExpr;
    type Attribute;
    type Sort;
    type Term;

    fn handle_numeral(value: Str8) -> Result<Self::Numeral, Self::Error>;
    fn handle_decimal(numerator: Str8, denominator: Str8) -> Result<Self::Decimal, Self::Error>;
    fn handle_hexadecimal(value: Str8) -> Result<Self::Hexadecimal, Self::Error>;
    fn handle_binary(value: Str8) -> Result<Self::Binary, Self::Error>;
    fn handle_string(str: Str8) -> Result<Self::String, Self::Error>;

    fn handle_sort(&mut self, _sort: SmtSort) -> Result<Self::Sort, Self::Error>;
    fn handle_term(&mut self, _term: SmtTerm<Self::Term>) -> Result<Self::Term, Self::Error>;
    fn start_let(&mut self, _bindings: Vec<(Self::String, Self::Term)>) -> Result<(), Self::Error>;
    fn end_let(&mut self, _term: Self::Term) -> Result<Self::Term, Self::Error>;

    fn handle_s_expr(&mut self, expr: SmtSExpr<Self::SExpr>) -> Result<Self::SExpr, Self::Error>;
    fn handle_attribute(
        &mut self,
        name: Self::String,
        value: Option<SmtAttributeValue<Self::SExpr>>,
    ) -> Result<Self::Attribute, Self::Error>;
}

pub trait CommandHandler: CategoryHandler {
    fn command_echo(&mut self, value: Self::String) -> Result<(), Self::Error>;

    fn command_get_option(&mut self, option: Self::String) -> Result<(), Self::Error>;

    fn command_set_option(&mut self, option: Self::Attribute) -> Result<(), Self::Error>;

    fn command_get_info(&mut self, keyword: Self::String) -> Result<(), Self::Error>;

    fn command_set_info(&mut self, attribute: Self::Attribute) -> Result<(), Self::Error>;

    fn command_set_logic(&mut self, logic: Self::String) -> Result<(), Self::Error>;

    fn command_declare_const(
        &mut self,
        name: Self::String,
        sort: Self::Sort,
    ) -> Result<(), Self::Error>;

    fn command_assert(&mut self, term: Self::Term) -> Result<(), Self::Error>;

    fn command_check_sat(&mut self) -> Result<(), Self::Error>;

    fn command_reset(&mut self) -> Result<(), Self::Error>;

    fn command_reset_assertions(&mut self) -> Result<(), Self::Error>;

    fn command_exit(&mut self) -> Result<(), Self::Error>;

    fn start_define_fun(
        &mut self,
        signature: SmtFunctionSignature<Self::Sort>,
    ) -> Result<(), Self::Error>;

    fn end_define_fun(&mut self, _term: Self::Term) -> Result<(), Self::Error>;
}

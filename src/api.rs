use std::convert::Infallible;

use crate::{
    Str8, String8,
    old::{SmtAttributeValue, SmtFunctionSignature, SmtSExpr},
};

#[derive(Debug, Clone)]
pub enum SmtIndex<'a> {
    Numeral(Str8<'a>),
    Symbol(Str8<'a>),
}

#[derive(Debug, Clone)]
pub struct SmtIdent<'a> {
    pub name: Str8<'a>,
    pub indices: Vec<SmtIndex<'a>>,
}

#[derive(Debug, Clone)]

pub enum SmtSort<H: SmtHandler + ?Sized> {
    Ident(H::Ident),
}

#[derive(Debug, Clone)]
pub enum SmtQualifiedIdent<'a> {
    Ident(SmtIdent<'a>), // 'as' qualified idents not implemented
}

/// Application. There must be at least one term.
#[derive(Debug, Clone)]
pub struct SmtApplication<'a, H: SmtHandler + ?Sized> {
    pub function: SmtQualifiedIdent<'a>,
    pub args: Vec<H::Term>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum SmtSpecialConstant {
    Numeral(String8),
    Decimal {
        numerator: String8,
        denominator: String8,
    },
    Hexadecimal(String8),
    Binary(String8),
    String(String8),
}

pub enum SmtTerm<'a, H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstant),
    QualifiedIdent(SmtQualifiedIdent<'a>),
    Application(SmtApplication<'a, H>),
}

pub trait SmtHandler: 'static {
    type Error;

    type Numeral;
    type Decimal;
    type Hexadecimal;
    type Binary;
    type String;

    type Symbol;
    type Index;
    type Ident;

    type SExpr;
    type Attribute;
    type Sort;
    type Term;

    fn handle_numeral(&mut self, value: Str8) -> Result<Self::Numeral, Self::Error>;
    fn handle_decimal(
        &mut self,
        numerator: Str8,
        denominator: Str8,
    ) -> Result<Self::Decimal, Self::Error>;
    fn handle_hexadecimal(&mut self, value: Str8) -> Result<Self::Hexadecimal, Self::Error>;
    fn handle_binary(&mut self, value: Str8) -> Result<Self::Binary, Self::Error>;
    fn handle_string(&mut self, str: Str8) -> Result<Self::String, Self::Error>;

    fn handle_symbol(&mut self, str: Str8) -> Result<Self::Symbol, Self::Error>;
    fn handle_index(&mut self, index: SmtIndex) -> Result<Self::Index, Self::Error>;
    fn handle_ident(
        &mut self,
        symbol: Str8,
        indices: Vec<Self::Index>,
    ) -> Result<Self::Ident, Self::Error>;

    fn handle_sort(&mut self, _sort: SmtSort<Self>) -> Result<Self::Sort, Self::Error>;
    fn handle_term(&mut self, _term: SmtTerm<Self>) -> Result<Self::Term, Self::Error>;
    fn start_let(&mut self, _bindings: Vec<(Self::String, Self::Term)>) -> Result<(), Self::Error>;
    fn end_let(&mut self, _term: Self::Term) -> Result<Self::Term, Self::Error>;

    fn handle_s_expr(&mut self, expr: SmtSExpr<Self::SExpr>) -> Result<Self::SExpr, Self::Error>;
    fn handle_attribute(
        &mut self,
        name: Str8,
        value: Option<SmtAttributeValue<Self::SExpr>>,
    ) -> Result<Self::Attribute, Self::Error>;
}

pub trait CommandHandler: SmtHandler {
    fn command_echo(&mut self, value: Self::String) -> Result<(), Self::Error>;

    fn command_get_option(&mut self, option: Self::String) -> Result<(), Self::Error>;

    fn command_set_option(&mut self, option: Self::Attribute) -> Result<(), Self::Error>;

    fn command_get_info(&mut self, keyword: Self::Symbol) -> Result<(), Self::Error>;

    fn command_set_info(&mut self, attribute: Self::Attribute) -> Result<(), Self::Error>;

    fn command_set_logic(&mut self, logic: Str8) -> Result<(), Self::Error>;

    fn command_declare_const(&mut self, name: Str8, sort: Self::Sort) -> Result<(), Self::Error>;

    fn command_assert(&mut self, term: Self::Term) -> Result<(), Self::Error>;

    fn command_check_sat(&mut self) -> Result<(), Self::Error>;

    fn command_reset(&mut self) -> Result<(), Self::Error>;

    fn command_reset_assertions(&mut self) -> Result<(), Self::Error>;

    fn command_exit(&mut self) -> Result<(), Self::Error>;

    fn start_define_fun(
        &mut self,
        signature: SmtFunctionSignature<Self::Sort>,
    ) -> Result<(), Self::Error>;

    fn end_define_fun(&mut self, term: Self::Term) -> Result<(), Self::Error>;
}

#[derive(Debug)]
pub struct OnlyCheckSyntax;

impl SmtHandler for OnlyCheckSyntax {
    type Error = Infallible;
    type Numeral = ();
    type Decimal = ();
    type Hexadecimal = ();
    type Binary = ();
    type String = ();

    type Symbol = ();
    type Index = ();
    type Ident = ();

    type SExpr = ();
    type Attribute = ();
    type Sort = ();
    type Term = ();

    fn handle_numeral(&mut self, _value: Str8) -> Result<Self::Numeral, Self::Error> {
        Ok(())
    }

    fn handle_decimal(
        &mut self,
        _numerator: Str8,
        _denominator: Str8,
    ) -> Result<Self::Decimal, Self::Error> {
        Ok(())
    }

    fn handle_hexadecimal(&mut self, _value: Str8) -> Result<Self::Hexadecimal, Self::Error> {
        Ok(())
    }

    fn handle_binary(&mut self, _value: Str8) -> Result<Self::Binary, Self::Error> {
        Ok(())
    }

    fn handle_string(&mut self, _str: Str8) -> Result<Self::String, Self::Error> {
        Ok(())
    }

    fn handle_symbol(&mut self, _str: Str8) -> Result<Self::Symbol, Self::Error> {
        Ok(())
    }

    fn handle_index(&mut self, _index: SmtIndex) -> Result<Self::Index, Self::Error> {
        Ok(())
    }

    fn handle_ident(
        &mut self,
        _symbol: Str8,
        _indices: Vec<Self::Index>,
    ) -> Result<Self::Ident, Self::Error> {
        Ok(())
    }

    fn handle_sort(&mut self, _sort: SmtSort<Self>) -> Result<Self::Sort, Self::Error> {
        Ok(())
    }

    fn handle_term(&mut self, _term: SmtTerm<Self>) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_let(&mut self, _bindings: Vec<(Self::String, Self::Term)>) -> Result<(), Self::Error> {
        Ok(())
    }

    fn end_let(&mut self, _term: Self::Term) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn handle_s_expr(&mut self, _expr: SmtSExpr<Self::SExpr>) -> Result<Self::SExpr, Self::Error> {
        Ok(())
    }

    fn handle_attribute(
        &mut self,
        _name: Str8,
        _value: Option<SmtAttributeValue<Self::SExpr>>,
    ) -> Result<Self::Attribute, Self::Error> {
        Ok(())
    }
}

impl CommandHandler for OnlyCheckSyntax {
    fn command_echo(&mut self, _value: Self::String) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_option(&mut self, _option: Self::String) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_option(&mut self, _option: Self::Attribute) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_get_info(&mut self, _keyword: Self::String) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_info(&mut self, _attribute: Self::Attribute) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_set_logic(&mut self, _logic: Str8) -> Result<(), Self::Error> {
        Ok(())
    }

    fn command_declare_const(&mut self, _name: Str8, _sort: Self::Sort) -> Result<(), Self::Error> {
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

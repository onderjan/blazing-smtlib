use crate::{
    SmtBinDigits, SmtDecimal, SmtHexDigits, SmtKeyword, SmtNumeral, SmtStringContent, SmtSymbol,
    parser::{NoCommandParser, ParseCommand},
    token::Reserved,
};

#[derive(Debug, Clone)]
pub enum SmtIndex {
    Numeral(SmtNumeral),
    Symbol(SmtSymbol),
}

#[derive(Debug, Clone)]
pub struct SmtIdent {
    pub name: SmtSymbol,
    pub indices: Vec<SmtIndex>,
}

#[derive(Debug, Clone)]

pub enum SmtSort {
    Ident(SmtIdent),
}

#[derive(Debug, Clone)]
pub enum SmtQualifiedIdent {
    Ident(SmtIdent), // 'as' qualified idents not implemented
}

/// Application. There must be at least one term.
#[derive(Debug, Clone)]
pub struct SmtApplication<H: SmtHandler + ?Sized> {
    pub function: SmtQualifiedIdent,
    pub args: Vec<H::Term>,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum SmtSpecialConstant {
    Numeral(SmtNumeral),
    Decimal(SmtDecimal),
    Hexadecimal(SmtHexDigits),
    Binary(SmtBinDigits),
    String(SmtStringContent),
}

pub enum SmtTerm<H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstant),
    QualifiedIdent(SmtQualifiedIdent),
    Application(SmtApplication<H>),
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum SmtAttributeValue<H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstant),
    Symbol(SmtSymbol),
    Exprs(Vec<H::SExpr>),
}

#[allow(dead_code)]
#[derive(Debug)]
pub struct SmtFunctionSignature<S> {
    pub name: SmtSymbol,
    pub parameters: Vec<(SmtSymbol, S)>,
    pub result_sort: S,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum SmtSExpr<E> {
    SpecialConstant(SmtSpecialConstant),
    Symbol(SmtSymbol),
    Reserved(Reserved),
    Keyword(SmtKeyword),
    Exprs(Vec<E>),
}

pub trait SmtHandler: 'static {
    type Error;

    type SExpr;
    type Attribute;
    type Sort;
    type Term;

    fn handle_sort(&mut self, _sort: SmtSort) -> Result<Self::Sort, Self::Error>;
    fn handle_term(&mut self, _term: SmtTerm<Self>) -> Result<Self::Term, Self::Error>;
    fn start_let(&mut self, _bindings: Vec<(SmtSymbol, Self::Term)>) -> Result<(), Self::Error>;
    fn end_let(&mut self, _term: Self::Term) -> Result<Self::Term, Self::Error>;

    fn handle_s_expr(&mut self, expr: SmtSExpr<Self::SExpr>) -> Result<Self::SExpr, Self::Error>;
    fn handle_attribute(
        &mut self,
        name: SmtKeyword,
        value: Option<SmtAttributeValue<Self>>,
    ) -> Result<Self::Attribute, Self::Error>;
}

pub trait CommandHandler: SmtHandler {
    type NonstandardParser: ParseCommand<Self>;

    fn nonstandard_command(
        &mut self,
        name: SmtSymbol,
    ) -> Result<Self::NonstandardParser, Self::Error>;

    fn command_echo(&mut self, value: SmtStringContent) -> Result<(), Self::Error>;

    fn command_get_option(&mut self, option: SmtKeyword) -> Result<(), Self::Error>;
    fn command_set_option(&mut self, option: Self::Attribute) -> Result<(), Self::Error>;
    fn command_get_info(&mut self, keyword: SmtKeyword) -> Result<(), Self::Error>;
    fn command_set_info(&mut self, attribute: Self::Attribute) -> Result<(), Self::Error>;

    fn command_set_logic(&mut self, logic: SmtSymbol) -> Result<(), Self::Error>;

    fn command_declare_const(
        &mut self,
        name: SmtSymbol,
        sort: Self::Sort,
    ) -> Result<(), Self::Error>;
    fn command_declare_fun(
        &mut self,
        name: SmtSymbol,
        param_sorts: Vec<Self::Sort>,
        result_sort: Self::Sort,
    ) -> Result<(), Self::Error>;
    fn command_define_fun(
        &mut self,
        name: SmtSymbol,
        params: Vec<(SmtSymbol, Self::Sort)>,
        result_sort: Self::Sort,
        definition: Self::Term,
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

    fn handle_sort(&mut self, _sort: SmtSort) -> Result<Self::Sort, Self::Error> {
        Ok(())
    }

    fn handle_term(&mut self, _term: SmtTerm<Self>) -> Result<Self::Term, Self::Error> {
        Ok(())
    }

    fn start_let(&mut self, _bindings: Vec<(SmtSymbol, Self::Term)>) -> Result<(), Self::Error> {
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
        _name: SmtKeyword,
        _value: Option<SmtAttributeValue<Self>>,
    ) -> Result<Self::Attribute, Self::Error> {
        Ok(())
    }
}

impl CommandHandler for CheckStandardSyntax {
    type NonstandardParser = NoCommandParser;

    fn nonstandard_command(
        &mut self,
        name: SmtSymbol,
    ) -> Result<Self::NonstandardParser, Self::Error> {
        // reject nonstandard command
        Err(NonstandardCommandError(name))
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

    fn command_declare_const(
        &mut self,
        _name: SmtSymbol,
        _sort: Self::Sort,
    ) -> Result<(), Self::Error> {
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

    fn command_define_fun(
        &mut self,
        _name: SmtSymbol,
        _params: Vec<(SmtSymbol, Self::Sort)>,
        _result_sort: Self::Sort,
        _definition: Self::Term,
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

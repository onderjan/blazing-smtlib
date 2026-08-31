use std::fmt::Debug;

use crate::{
    SmtBinDigits, SmtDecimal, SmtHandler, SmtHexDigits, SmtKeyword, SmtNumeral, SmtStringContent,
    SmtSymbol, token::Reserved,
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

impl SmtIdent {
    pub fn new_simple(name: SmtSymbol) -> SmtIdent {
        SmtIdent {
            name,
            indices: Vec::new(),
        }
    }
}

pub struct SmtQualifiedIdent<H: SmtHandler + ?Sized> {
    pub ident: SmtIdent,
    pub sort: Option<H::Sort>,
}

impl<H: SmtHandler> SmtQualifiedIdent<H> {
    pub fn new_simple(name: SmtSymbol) -> Self {
        Self::new_unqualified(SmtIdent::new_simple(name))
    }

    pub fn new_unqualified(ident: SmtIdent) -> Self {
        Self { ident, sort: None }
    }

    pub fn new_qualified(ident: SmtIdent, sort: H::Sort) -> Self {
        Self {
            ident,
            sort: Some(sort),
        }
    }
}

impl<H: SmtHandler + ?Sized> Debug for SmtQualifiedIdent<H>
where
    H::Sort: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtQualifiedIdent")
            .field("ident", &self.ident)
            .field("sort", &self.sort)
            .finish()
    }
}

impl<H: SmtHandler + ?Sized> Clone for SmtQualifiedIdent<H>
where
    H::Sort: Clone,
{
    fn clone(&self) -> Self {
        Self {
            ident: self.ident.clone(),
            sort: self.sort.clone(),
        }
    }
}

pub struct SmtSort<H: SmtHandler + ?Sized> {
    pub ident: SmtIdent,
    pub applied: Vec<H::Sort>,
}

impl<H: SmtHandler> SmtSort<H> {
    pub fn new(ident: SmtIdent, applied: Vec<H::Sort>) -> Self {
        Self { ident, applied }
    }

    pub fn new_simple(ident: SmtIdent) -> Self {
        Self::new(ident, Vec::new())
    }
}

impl<H: SmtHandler + ?Sized> Debug for SmtSort<H>
where
    H::Sort: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtSort")
            .field("ident", &self.ident)
            .field("applied", &self.applied)
            .finish()
    }
}

impl<H: SmtHandler + ?Sized> Clone for SmtSort<H>
where
    H::Sort: Clone,
{
    fn clone(&self) -> Self {
        Self {
            ident: self.ident.clone(),
            applied: self.applied.clone(),
        }
    }
}

/// Application. There must be at least one term.
pub struct SmtApplication<H: SmtHandler + ?Sized> {
    pub function: SmtQualifiedIdent<H>,
    pub args: Vec<H::Term>,
}

impl<H: SmtHandler + ?Sized> Debug for SmtApplication<H>
where
    H::Sort: Debug,
    H::Term: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtApplication")
            .field("function", &self.function)
            .field("args", &self.args)
            .finish()
    }
}

impl<H: SmtHandler + ?Sized> Clone for SmtApplication<H>
where
    H::Sort: Clone,
    H::Term: Clone,
{
    fn clone(&self) -> Self {
        Self {
            function: self.function.clone(),
            args: self.args.clone(),
        }
    }
}

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
    QualifiedIdent(SmtQualifiedIdent<H>),
    Application(SmtApplication<H>),
}

#[derive(Debug, Clone)]
pub enum SmtAttributeValue<H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstant),
    Symbol(SmtSymbol),
    SExprs(Vec<H::SExpr>),
}

#[derive(Debug)]
pub struct SmtFunctionSignature<S> {
    pub name: SmtSymbol,
    pub parameters: Vec<(SmtSymbol, S)>,
    pub result_sort: S,
}

#[derive(Debug, Clone)]
pub enum SmtSExpr<H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstant),
    Symbol(SmtSymbol),
    Reserved(Reserved),
    Keyword(SmtKeyword),
    SExprs(Vec<H::SExpr>),
}

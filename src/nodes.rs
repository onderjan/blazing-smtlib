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

impl<H: SmtHandler + ?Sized> SmtQualifiedIdent<H> {
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

impl<H: SmtHandler + ?Sized> SmtSort<H> {
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

#[derive(Debug, Clone, Copy)]
pub enum SmtQuantifierKind {
    Exists,
    Forall,
}

impl<H: SmtHandler + ?Sized> Debug for SmtTerm<H>
where
    H::Sort: Debug,
    H::Term: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SpecialConstant(arg0) => f.debug_tuple("SpecialConstant").field(arg0).finish(),
            Self::QualifiedIdent(arg0) => f.debug_tuple("QualifiedIdent").field(arg0).finish(),
            Self::Application(arg0) => f.debug_tuple("Application").field(arg0).finish(),
        }
    }
}

impl<H: SmtHandler + ?Sized> Clone for SmtTerm<H>
where
    H::Sort: Clone,
    H::Term: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::SpecialConstant(arg0) => Self::SpecialConstant(arg0.clone()),
            Self::QualifiedIdent(arg0) => Self::QualifiedIdent(arg0.clone()),
            Self::Application(arg0) => Self::Application(arg0.clone()),
        }
    }
}

pub enum SmtAttributeValue<H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstant),
    Symbol(SmtSymbol),
    SExprs(Vec<H::SExpr>),
}

impl<H: SmtHandler + ?Sized> Debug for SmtAttributeValue<H>
where
    H::SExpr: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SpecialConstant(arg0) => f.debug_tuple("SpecialConstant").field(arg0).finish(),
            Self::Symbol(arg0) => f.debug_tuple("Symbol").field(arg0).finish(),
            Self::SExprs(arg0) => f.debug_tuple("SExprs").field(arg0).finish(),
        }
    }
}

impl<H: SmtHandler + ?Sized> Clone for SmtAttributeValue<H>
where
    H::SExpr: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::SpecialConstant(arg0) => Self::SpecialConstant(arg0.clone()),
            Self::Symbol(arg0) => Self::Symbol(arg0.clone()),
            Self::SExprs(arg0) => Self::SExprs(arg0.clone()),
        }
    }
}

pub struct SmtFunctionSignature<H: SmtHandler + ?Sized> {
    pub name: SmtSymbol,
    pub params: Vec<(SmtSymbol, H::Sort)>,
    pub result_sort: H::Sort,
}

impl<H: SmtHandler + ?Sized> Debug for SmtFunctionSignature<H>
where
    H::Sort: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtFunctionSignature")
            .field("name", &self.name)
            .field("params", &self.params)
            .field("result_sort", &self.result_sort)
            .finish()
    }
}

impl<H: SmtHandler + ?Sized> Clone for SmtFunctionSignature<H>
where
    H::Sort: Clone,
{
    fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
            params: self.params.clone(),
            result_sort: self.result_sort.clone(),
        }
    }
}

pub struct SmtDatatypeConstructor<H: SmtHandler + ?Sized> {
    pub name: SmtSymbol,
    pub selectors: Vec<(SmtSymbol, H::Sort)>,
}

impl<H: SmtHandler + ?Sized> Debug for SmtDatatypeConstructor<H>
where
    H::Sort: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtDatatypeConstructor")
            .field("name", &self.name)
            .field("selectors", &self.selectors)
            .finish()
    }
}

impl<H: SmtHandler + ?Sized> Clone for SmtDatatypeConstructor<H>
where
    H::Sort: Clone,
{
    fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
            selectors: self.selectors.clone(),
        }
    }
}

/// Simple match pattern: a symbol or a wildcard.
#[derive(Debug, Clone)]
pub enum SmtSimplePattern {
    /// A symbol as a pattern.
    ///
    /// In the match pattern position, the symbol should be
    /// either a variable or a nullary constructor, and
    /// it is not possible to determine syntactically which one it is.
    /// In the constructor application argument position,
    /// it should be a variable.
    Symbol(SmtSymbol),
    /// A wildcard (reserved word underscore `_`) as a pattern.
    Wildcard,
}

/// Match pattern: a symbol, a wildcard, or a constructor application.
#[derive(Debug, Clone)]
pub enum SmtPattern {
    /// A simple match pattern, either a symbol or a wildcard.
    Simple(SmtSimplePattern),
    /// A constructor applied to at least one variable or wildcard.
    Application {
        constructor: SmtSymbol,
        args: Vec<SmtSimplePattern>,
    },
}

pub enum SmtSExpr<H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstant),
    Symbol(SmtSymbol),
    Reserved(Reserved),
    Keyword(SmtKeyword),
    SExprs(Vec<H::SExpr>),
}

impl<H: SmtHandler + ?Sized> Debug for SmtSExpr<H>
where
    H::SExpr: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SpecialConstant(arg0) => f.debug_tuple("SpecialConstant").field(arg0).finish(),
            Self::Symbol(arg0) => f.debug_tuple("Symbol").field(arg0).finish(),
            Self::Reserved(arg0) => f.debug_tuple("Reserved").field(arg0).finish(),
            Self::Keyword(arg0) => f.debug_tuple("Keyword").field(arg0).finish(),
            Self::SExprs(arg0) => f.debug_tuple("SExprs").field(arg0).finish(),
        }
    }
}

impl<H: SmtHandler + ?Sized> Clone for SmtSExpr<H>
where
    H::SExpr: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::SpecialConstant(arg0) => Self::SpecialConstant(arg0.clone()),
            Self::Symbol(arg0) => Self::Symbol(arg0.clone()),
            Self::Reserved(arg0) => Self::Reserved(*arg0),
            Self::Keyword(arg0) => Self::Keyword(arg0.clone()),
            Self::SExprs(arg0) => Self::SExprs(arg0.clone()),
        }
    }
}

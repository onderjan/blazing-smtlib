use num::BigUint;
use std::fmt::Debug;

use crate::{String8, token::Reserved};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Whole {
    pub value: BigUint,
    pub num_digits: BigUint,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Decimal {
    pub value: BigUint,
    pub num_numerator_digits: BigUint,
    pub num_denominator_digits: BigUint,
}

/// SMT-LIB2 index.
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum SmtIndex {
    Numeral(Whole),
    Symbol(String8),
}

/// SMT-LIB2 ident.
///
/// A simple ident has no indices, an indexed ident has at least one index.
#[derive(Debug, Clone)]
pub struct SmtIdent {
    pub name: String8,
    pub indices: Vec<SmtIndex>,
}

impl SmtIdent {
    pub fn simple(name: String8) -> Self {
        Self {
            name,
            indices: Vec::new(),
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum SmtSpecialConstant {
    Numeral(Whole),
    Decimal(Decimal),
    Hexadecimal(Whole),
    Binary(Whole),
    String(String8),
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum SmtSExpr<E> {
    SpecialConstant(SmtSpecialConstant),
    Symbol(String8),
    Reserved(Reserved),
    Keyword(String8),
    Exprs(Vec<E>),
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum SmtAttributeValue<E> {
    SpecialConstant(SmtSpecialConstant),
    Symbol(String8),
    Exprs(Vec<E>),
}

#[derive(Debug, Clone)]
pub enum SmtSort {
    Ident(SmtIdent),
    // sort applications not implemented
}

#[derive(Debug, Clone)]
pub enum SmtQualifiedIdent {
    Ident(SmtIdent), // 'as' qualified idents not implemented
}

/// Application. There must be at least one term.
#[derive(Debug, Clone)]
pub struct SmtApplication<T> {
    pub qualified: SmtQualifiedIdent,
    pub arguments: Vec<T>,
}

#[derive(Debug, Clone)]
pub enum SmtTerm<T> {
    SpecialConstant(SmtSpecialConstant),
    QualifiedIdent(SmtQualifiedIdent),
    Application(SmtApplication<T>),
}

#[derive(Debug)]
pub struct SmtFunctionSignature<S> {
    pub name: String8,
    pub parameters: Vec<(String8, S)>,
    #[allow(dead_code)]
    pub result_sort: S,
}

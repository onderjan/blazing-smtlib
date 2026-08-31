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

#[derive(Debug)]
pub struct SmtFunctionSignature<S> {
    pub name: SmtSymbol,
    pub parameters: Vec<(SmtSymbol, S)>,
    pub result_sort: S,
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

#[cfg(test)]
mod tests {
    use std::convert::Infallible;
    use std::fmt::Debug;

    use super::*;
    use crate::SmtHandler;

    /// Handler that is deliberately neither `Debug` nor `Clone`,
    /// while all of its associated types are both.
    struct OpaqueHandler;

    impl SmtHandler for OpaqueHandler {
        type Error = Infallible;
        type SExpr = String;
        type Attribute = String;
        type Sort = String;
        type Term = String;

        fn handle_sort(&mut self, _sort: SmtSort<Self>) -> Result<String, Infallible> {
            Ok(String::new())
        }
        fn handle_term(&mut self, _term: SmtTerm<Self>) -> Result<String, Infallible> {
            Ok(String::new())
        }
        fn start_let(&mut self, _bindings: Vec<(SmtSymbol, String)>) -> Result<(), Infallible> {
            Ok(())
        }
        fn end_let(&mut self, term: String) -> Result<String, Infallible> {
            Ok(term)
        }
        fn handle_s_expr(&mut self, _expr: SmtSExpr<Self>) -> Result<String, Infallible> {
            Ok(String::new())
        }
        fn handle_attribute(
            &mut self,
            _name: SmtKeyword,
            _value: Option<SmtAttributeValue<Self>>,
        ) -> Result<String, Infallible> {
            Ok(String::new())
        }
    }

    fn assert_debug_and_clone<T: Debug + Clone>() {}
    fn assert_debug<T: Debug>() {}

    /// The `H`-generic nodes must be `Debug` and `Clone` whenever the handler's
    /// associated types are, regardless of the handler type itself.
    ///
    /// This is a compile-time guard: it stops compiling if the manual impls are
    /// replaced with derives, which would wrongly bound `H` instead of the
    /// associated types actually stored in the nodes.
    #[test]
    fn nodes_are_debug_and_clone_with_an_opaque_handler() {
        assert_debug_and_clone::<SmtIndex>();
        assert_debug_and_clone::<SmtIdent>();
        assert_debug_and_clone::<SmtSpecialConstant>();
        assert_debug_and_clone::<SmtQualifiedIdent<OpaqueHandler>>();
        assert_debug_and_clone::<SmtSort<OpaqueHandler>>();
        assert_debug_and_clone::<SmtApplication<OpaqueHandler>>();
        assert_debug_and_clone::<SmtTerm<OpaqueHandler>>();
        assert_debug_and_clone::<SmtAttributeValue<OpaqueHandler>>();
        assert_debug_and_clone::<SmtSExpr<OpaqueHandler>>();
        // the signature is generic over the sort directly and is only `Debug`
        assert_debug::<SmtFunctionSignature<String>>();
    }
}

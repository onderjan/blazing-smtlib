use std::fmt::Debug;

use crate::{
    SmtBinDigits, SmtBinDigitsView, SmtDecimal, SmtDecimalView, SmtHandler, SmtHexDigits,
    SmtHexDigitsView, SmtKeywordView, SmtMultiple, SmtNumeral, SmtNumeralView, SmtStringContent,
    SmtStringContentView, SmtSymbol, SmtSymbolView,
    read::parser::{ArenaAccess, IndexHandle, SimplePatternHandle},
    token::SmtReserved,
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

/// Index of an identifier to be handled.
#[derive(Debug, Clone, Copy)]
pub enum SmtIndexView<'a> {
    Numeral(SmtNumeralView<'a>),
    Symbol(SmtSymbolView<'a>),
}

impl SmtIndexView<'_> {
    pub fn into_owned(self) -> SmtIndex {
        match self {
            SmtIndexView::Numeral(numeral) => SmtIndex::Numeral(numeral.into_owned()),
            SmtIndexView::Symbol(symbol) => SmtIndex::Symbol(symbol.into_owned()),
        }
    }
}

/// The indices of an identifier that is to be handled.
#[derive(Clone, Copy)]
pub struct SmtIndices<'a> {
    text: &'a [u8],
    handles: &'a [IndexHandle],
}

impl<'a> SmtIndices<'a> {
    pub(crate) fn new(_access: ArenaAccess, text: &'a [u8], handles: &'a [IndexHandle]) -> Self {
        Self { text, handles }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.handles.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.handles.is_empty()
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<SmtIndexView<'a>> {
        Some(self.handles.get(index)?.view(self.text))
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = SmtIndexView<'a>> {
        let text = self.text;
        self.handles.iter().map(move |handle| handle.view(text))
    }
}

impl Debug for SmtIndices<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Identifier to be handled.
#[derive(Debug, Clone, Copy)]
pub struct SmtIdentView<'a> {
    pub name: SmtSymbolView<'a>,
    pub indices: SmtIndices<'a>,
}

impl SmtIdentView<'_> {
    pub fn into_owned(self) -> SmtIdent {
        SmtIdent {
            name: self.name.into_owned(),
            indices: self.indices.iter().map(SmtIndexView::into_owned).collect(),
        }
    }
}

/// A qualified identifier to be handled.
pub struct SmtQualifiedIdentView<'a, H: SmtHandler + ?Sized> {
    pub ident: SmtIdentView<'a>,
    pub sort: Option<H::Sort>,
}

impl<H: SmtHandler + ?Sized> SmtQualifiedIdentView<'_, H> {
    pub fn into_owned(self) -> SmtQualifiedIdent<H> {
        SmtQualifiedIdent {
            ident: self.ident.into_owned(),
            sort: self.sort,
        }
    }
}

impl<H: SmtHandler + ?Sized> Debug for SmtQualifiedIdentView<'_, H>
where
    H::Sort: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtQualifiedIdentView")
            .field("ident", &self.ident)
            .field("sort", &self.sort)
            .finish()
    }
}

impl<H: SmtHandler + ?Sized> Clone for SmtQualifiedIdentView<'_, H>
where
    H::Sort: Clone,
{
    fn clone(&self) -> Self {
        Self {
            ident: self.ident,
            sort: self.sort.clone(),
        }
    }
}

/// Sorts to be handled.
pub type SmtSorts<'a, H> = SmtMultiple<'a, <H as SmtHandler>::Sort>;

/// A sort to be handled.
pub struct SmtSort<'a, H: SmtHandler + ?Sized> {
    pub ident: SmtIdentView<'a>,
    pub applied: SmtSorts<'a, H>,
}

impl<H: SmtHandler + ?Sized> Debug for SmtSort<'_, H>
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

/// Terms to be handled.
pub type SmtTerms<'a, H> = SmtMultiple<'a, <H as SmtHandler>::Term>;

/// A term that is an application.
///
/// It is guaranteed that `args` are nonempty.
pub struct SmtApplication<'a, H: SmtHandler + ?Sized> {
    pub function: SmtQualifiedIdentView<'a, H>,
    pub args: SmtTerms<'a, H>,
}

impl<H: SmtHandler + ?Sized> Debug for SmtApplication<'_, H>
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

#[derive(Debug, Clone)]
pub enum SmtSpecialConstant {
    Numeral(SmtNumeral),
    Decimal(SmtDecimal),
    Hexadecimal(SmtHexDigits),
    Binary(SmtBinDigits),
    String(SmtStringContent),
}

/// A special constant to be handled.
#[derive(Debug, Clone, Copy)]
pub enum SmtSpecialConstantView<'a> {
    Numeral(SmtNumeralView<'a>),
    Decimal(SmtDecimalView<'a>),
    Hexadecimal(SmtHexDigitsView<'a>),
    Binary(SmtBinDigitsView<'a>),
    String(SmtStringContentView<'a>),
}

impl SmtSpecialConstantView<'_> {
    pub fn into_owned(self) -> SmtSpecialConstant {
        match self {
            Self::Numeral(value) => SmtSpecialConstant::Numeral(value.into_owned()),
            Self::Decimal(value) => SmtSpecialConstant::Decimal(value.into_owned()),
            Self::Hexadecimal(value) => SmtSpecialConstant::Hexadecimal(value.into_owned()),
            Self::Binary(value) => SmtSpecialConstant::Binary(value.into_owned()),
            Self::String(value) => SmtSpecialConstant::String(value.into_owned()),
        }
    }
}

/// A term to be handled.
pub enum SmtTerm<'a, H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstantView<'a>),
    QualifiedIdent(SmtQualifiedIdentView<'a, H>),
    Application(SmtApplication<'a, H>),
}

#[derive(Debug, Clone, Copy)]
pub enum SmtQuantifierKind {
    Exists,
    Forall,
}

impl<H: SmtHandler + ?Sized> Debug for SmtTerm<'_, H>
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

/// S-expressions to be handled.
pub type SmtSExprs<'a, H> = SmtMultiple<'a, <H as SmtHandler>::SExpr>;

/// Attributes to be handled.
pub type SmtAttributes<'a, H> = SmtMultiple<'a, <H as SmtHandler>::Attribute>;

pub enum SmtAttributeValue<'a, H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstantView<'a>),
    Symbol(SmtSymbolView<'a>),
    SExprs(SmtSExprs<'a, H>),
}

impl<H: SmtHandler + ?Sized> Debug for SmtAttributeValue<'_, H>
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

pub enum SmtSExpr<'a, H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstantView<'a>),
    Symbol(SmtSymbolView<'a>),
    Reserved(SmtReserved),
    Keyword(SmtKeywordView<'a>),
    SExprs(SmtSExprs<'a, H>),
}

impl<H: SmtHandler + ?Sized> Debug for SmtSExpr<'_, H>
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

/// Simple match pattern to be handled: a symbol or a wildcard.
#[derive(Debug, Clone, Copy)]
pub enum SmtSimplePatternView<'a> {
    Symbol(SmtSymbolView<'a>),
    Wildcard,
}

impl SmtSimplePatternView<'_> {
    pub fn into_owned(self) -> SmtSimplePattern {
        match self {
            Self::Symbol(symbol) => SmtSimplePattern::Symbol(symbol.into_owned()),
            Self::Wildcard => SmtSimplePattern::Wildcard,
        }
    }
}

/// The arguments of a constructor pattern to be handled.
#[derive(Clone, Copy)]
pub struct SmtSimplePatterns<'a> {
    text: &'a [u8],
    handles: &'a [SimplePatternHandle],
}

impl<'a> SmtSimplePatterns<'a> {
    pub(crate) fn new(
        _access: ArenaAccess,
        text: &'a [u8],
        handles: &'a [SimplePatternHandle],
    ) -> Self {
        Self { text, handles }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.handles.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.handles.is_empty()
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<SmtSimplePatternView<'a>> {
        Some(self.handles.get(index)?.view(self.text))
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = SmtSimplePatternView<'a>> {
        let text = self.text;
        self.handles.iter().map(move |handle| handle.view(text))
    }
}

impl Debug for SmtSimplePatterns<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Match pattern to be handled: a symbol, a wildcard, or a constructor application.
#[derive(Debug, Clone, Copy)]
pub enum SmtPatternView<'a> {
    /// A simple match pattern, either a symbol or a wildcard.
    Simple(SmtSimplePatternView<'a>),
    /// A constructor applied to at least one variable or wildcard.
    Application {
        constructor: SmtSymbolView<'a>,
        args: SmtSimplePatterns<'a>,
    },
}

impl SmtPatternView<'_> {
    pub fn into_owned(self) -> SmtPattern {
        match self {
            Self::Simple(simple) => SmtPattern::Simple(simple.into_owned()),
            Self::Application { constructor, args } => SmtPattern::Application {
                constructor: constructor.into_owned(),
                args: args.iter().map(SmtSimplePatternView::into_owned).collect(),
            },
        }
    }
}

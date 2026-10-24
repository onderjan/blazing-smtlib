use std::fmt::Debug;

use crate::{
    SmtBinDigits, SmtBinDigitsBuf, SmtDecimal, SmtDecimalBuf, SmtHandler, SmtHexDigits,
    SmtHexDigitsBuf, SmtKeyword, SmtMultiple, SmtNumeral, SmtNumeralBuf, SmtStringContent,
    SmtStringContentBuf, SmtSymbol, SmtSymbolBuf,
    parser::{ArenaAccess, IndexHandle, SimplePatternHandle},
    token::SmtReserved,
};

#[derive(Debug, Clone)]
pub enum SmtIndexBuf {
    Numeral(SmtNumeralBuf),
    Symbol(SmtSymbolBuf),
}

impl SmtIndexBuf {
    pub fn view(&self) -> SmtIndex<'_> {
        match self {
            SmtIndexBuf::Numeral(numeral) => SmtIndex::Numeral(numeral.view()),
            SmtIndexBuf::Symbol(symbol) => SmtIndex::Symbol(symbol.view()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SmtIdentBuf {
    pub name: SmtSymbolBuf,
    pub indices: SmtIndicesBuf,
}

impl SmtIdentBuf {
    pub fn new_simple(name: SmtSymbolBuf) -> SmtIdentBuf {
        SmtIdentBuf {
            name,
            indices: SmtIndicesBuf::new(),
        }
    }

    pub fn view(&self) -> SmtIdent<'_> {
        SmtIdent {
            name: self.name.view(),
            indices: self.indices.view(),
        }
    }
}

pub struct SmtQualifiedIdentBuf<H: SmtHandler + ?Sized> {
    pub ident: SmtIdentBuf,
    pub sort: Option<H::Sort>,
}

impl<H: SmtHandler + ?Sized> SmtQualifiedIdentBuf<H> {
    pub fn new_simple(name: SmtSymbolBuf) -> Self {
        Self::new_unqualified(SmtIdentBuf::new_simple(name))
    }

    pub fn new_unqualified(ident: SmtIdentBuf) -> Self {
        Self { ident, sort: None }
    }

    pub fn new_qualified(ident: SmtIdentBuf, sort: H::Sort) -> Self {
        Self {
            ident,
            sort: Some(sort),
        }
    }
}

impl<H: SmtHandler + ?Sized> Debug for SmtQualifiedIdentBuf<H>
where
    H::Sort: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtQualifiedIdentBuf")
            .field("ident", &self.ident)
            .field("sort", &self.sort)
            .finish()
    }
}

impl<H: SmtHandler + ?Sized> Clone for SmtQualifiedIdentBuf<H>
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
pub enum SmtIndex<'a> {
    Numeral(SmtNumeral<'a>),
    Symbol(SmtSymbol<'a>),
}

impl SmtIndex<'_> {
    pub fn into_owned(self) -> SmtIndexBuf {
        match self {
            SmtIndex::Numeral(numeral) => SmtIndexBuf::Numeral(numeral.into_owned()),
            SmtIndex::Symbol(symbol) => SmtIndexBuf::Symbol(symbol.into_owned()),
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

    pub fn empty() -> Self {
        Self {
            text: &[],
            handles: &[],
        }
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
    pub fn get(&self, index: usize) -> Option<SmtIndex<'a>> {
        Some(self.handles.get(index)?.view(self.text))
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = SmtIndex<'a>> {
        let text = self.text;
        self.handles.iter().map(move |handle| handle.view(text))
    }
}

impl Debug for SmtIndices<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Owned indices of an identifier, from which [`SmtIndices`] is viewed.
#[derive(Clone)]
pub struct SmtIndicesBuf {
    text: Vec<u8>,
    handles: Vec<IndexHandle>,
}

impl SmtIndicesBuf {
    pub fn new() -> Self {
        Self {
            text: Vec::new(),
            handles: Vec::new(),
        }
    }

    pub fn push(&mut self, index: SmtIndex) {
        let index = IndexHandle::create_by_push(&mut self.text, index);
        self.handles.push(index);
    }

    pub fn clear(&mut self) {
        self.text.clear();
        self.handles.clear();
    }

    pub fn view(&self) -> SmtIndices<'_> {
        SmtIndices {
            text: &self.text,
            handles: &self.handles,
        }
    }

    pub fn len(&self) -> usize {
        self.handles.len()
    }

    pub fn is_empty(&self) -> bool {
        self.handles.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<SmtIndex<'_>> {
        Some(self.handles.get(index)?.view(&self.text))
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = SmtIndex<'_>> {
        let text = self.text.as_slice();
        self.handles.iter().map(move |handle| handle.view(text))
    }
}

impl Default for SmtIndicesBuf {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for SmtIndicesBuf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.view().iter()).finish()
    }
}

/// Identifier to be handled.
#[derive(Debug, Clone, Copy)]
pub struct SmtIdent<'a> {
    pub name: SmtSymbol<'a>,
    pub indices: SmtIndices<'a>,
}

impl SmtIdent<'_> {
    pub fn into_owned(self) -> SmtIdentBuf {
        let mut indices = SmtIndicesBuf::new();
        for index in self.indices.iter() {
            indices.push(index);
        }
        SmtIdentBuf {
            name: self.name.into_owned(),
            indices,
        }
    }
}

/// A qualified identifier to be handled.
pub struct SmtQualifiedIdent<'a, H: SmtHandler + ?Sized> {
    pub ident: SmtIdent<'a>,
    pub sort: Option<H::Sort>,
}

impl<H: SmtHandler + ?Sized> SmtQualifiedIdent<'_, H> {
    pub fn into_owned(self) -> SmtQualifiedIdentBuf<H> {
        SmtQualifiedIdentBuf {
            ident: self.ident.into_owned(),
            sort: self.sort,
        }
    }
}

impl<H: SmtHandler + ?Sized> Debug for SmtQualifiedIdent<'_, H>
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

impl<H: SmtHandler + ?Sized> Clone for SmtQualifiedIdent<'_, H>
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
    pub ident: SmtIdent<'a>,
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
    function: SmtQualifiedIdent<'a, H>,
    args: SmtTerms<'a, H>,
}

impl<'a, H: SmtHandler + ?Sized> SmtApplication<'a, H> {
    pub fn new(
        function: SmtQualifiedIdent<'a, H>,
        args: SmtTerms<'a, H>,
    ) -> Result<Self, SmtEmptyArgumentsError> {
        if args.is_empty() {
            return Err(SmtEmptyArgumentsError);
        }
        Ok(Self { function, args })
    }

    #[inline]
    pub(crate) fn new_unchecked(function: SmtQualifiedIdent<'a, H>, args: SmtTerms<'a, H>) -> Self {
        debug_assert!(!args.is_empty(), "an application without arguments");
        Self { function, args }
    }

    pub fn function(&self) -> &SmtQualifiedIdent<'a, H> {
        &self.function
    }

    pub fn function_mut(&mut self) -> &mut SmtQualifiedIdent<'a, H> {
        &mut self.function
    }

    pub fn args(&self) -> &SmtTerms<'a, H> {
        &self.args
    }

    pub fn args_mut(&mut self) -> &mut SmtTerms<'a, H> {
        &mut self.args
    }

    pub fn into_parts(self) -> (SmtQualifiedIdent<'a, H>, SmtTerms<'a, H>) {
        (self.function, self.args)
    }
}

/// An application or a constructor pattern was to be built without arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SmtEmptyArgumentsError;

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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SmtSpecialConstantBuf {
    Numeral(SmtNumeralBuf),
    Decimal(SmtDecimalBuf),
    Hexadecimal(SmtHexDigitsBuf),
    Binary(SmtBinDigitsBuf),
    String(SmtStringContentBuf),
}

impl SmtSpecialConstantBuf {
    pub fn view(&self) -> SmtSpecialConstant<'_> {
        match self {
            Self::Numeral(value) => SmtSpecialConstant::Numeral(value.view()),
            Self::Decimal(value) => SmtSpecialConstant::Decimal(value.view()),
            Self::Hexadecimal(value) => SmtSpecialConstant::Hexadecimal(value.view()),
            Self::Binary(value) => SmtSpecialConstant::Binary(value.view()),
            Self::String(value) => SmtSpecialConstant::String(value.view()),
        }
    }
}

/// A special constant to be handled.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtSpecialConstant<'a> {
    Numeral(SmtNumeral<'a>),
    Decimal(SmtDecimal<'a>),
    Hexadecimal(SmtHexDigits<'a>),
    Binary(SmtBinDigits<'a>),
    String(SmtStringContent<'a>),
}

impl SmtSpecialConstant<'_> {
    pub fn into_owned(self) -> SmtSpecialConstantBuf {
        match self {
            Self::Numeral(value) => SmtSpecialConstantBuf::Numeral(value.into_owned()),
            Self::Decimal(value) => SmtSpecialConstantBuf::Decimal(value.into_owned()),
            Self::Hexadecimal(value) => SmtSpecialConstantBuf::Hexadecimal(value.into_owned()),
            Self::Binary(value) => SmtSpecialConstantBuf::Binary(value.into_owned()),
            Self::String(value) => SmtSpecialConstantBuf::String(value.into_owned()),
        }
    }
}

/// A term to be handled.
pub enum SmtTerm<'a, H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstant<'a>),
    QualifiedIdent(SmtQualifiedIdent<'a, H>),
    Application(SmtApplication<'a, H>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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
    SpecialConstant(SmtSpecialConstant<'a>),
    Symbol(SmtSymbol<'a>),
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

/// Simple match pattern: a symbol or a wildcard.
#[derive(Debug, Clone)]
pub enum SmtSimplePatternBuf {
    /// A symbol as a pattern.
    ///
    /// In the match pattern position, the symbol should be
    /// either a variable or a nullary constructor, and
    /// it is not possible to determine syntactically which one it is.
    /// In the constructor application argument position,
    /// it should be a variable.
    Symbol(SmtSymbolBuf),
    /// A wildcard (reserved word underscore `_`) as a pattern.
    Wildcard,
}

impl SmtSimplePatternBuf {
    pub fn view(&self) -> SmtSimplePattern<'_> {
        match self {
            Self::Symbol(symbol) => SmtSimplePattern::Symbol(symbol.view()),
            Self::Wildcard => SmtSimplePattern::Wildcard,
        }
    }
}

/// Match pattern: a symbol, a wildcard, or a constructor application.
#[derive(Debug, Clone)]
pub enum SmtPatternBuf {
    /// A simple match pattern, either a symbol or a wildcard.
    Simple(SmtSimplePatternBuf),
    /// A constructor applied to at least one variable or wildcard.
    Application(SmtPatternApplicationBuf),
}

impl SmtPatternBuf {
    pub fn view(&self) -> SmtPattern<'_> {
        match self {
            Self::Simple(simple) => SmtPattern::Simple(simple.view()),
            Self::Application(application) => SmtPattern::Application(application.view()),
        }
    }
}

/// A constructor applied to at least one variable or wildcard, from which
/// [`SmtPatternApplication`] is viewed.
#[derive(Debug, Clone)]
pub struct SmtPatternApplicationBuf {
    constructor: SmtSymbolBuf,
    args: SmtSimplePatternsBuf,
}

impl SmtPatternApplicationBuf {
    pub fn new(
        constructor: SmtSymbolBuf,
        args: SmtSimplePatternsBuf,
    ) -> Result<Self, SmtEmptyArgumentsError> {
        if args.is_empty() {
            return Err(SmtEmptyArgumentsError);
        }
        Ok(Self { constructor, args })
    }

    pub fn constructor(&self) -> &SmtSymbolBuf {
        &self.constructor
    }

    pub fn args(&self) -> &SmtSimplePatternsBuf {
        &self.args
    }

    pub fn into_parts(self) -> (SmtSymbolBuf, SmtSimplePatternsBuf) {
        (self.constructor, self.args)
    }

    pub fn view(&self) -> SmtPatternApplication<'_> {
        SmtPatternApplication {
            constructor: self.constructor.view(),
            args: self.args.view(),
        }
    }
}

pub enum SmtSExpr<'a, H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstant<'a>),
    Symbol(SmtSymbol<'a>),
    Reserved(SmtReserved),
    Keyword(SmtKeyword<'a>),
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
pub enum SmtSimplePattern<'a> {
    Symbol(SmtSymbol<'a>),
    Wildcard,
}

impl SmtSimplePattern<'_> {
    pub fn into_owned(self) -> SmtSimplePatternBuf {
        match self {
            Self::Symbol(symbol) => SmtSimplePatternBuf::Symbol(symbol.into_owned()),
            Self::Wildcard => SmtSimplePatternBuf::Wildcard,
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
    pub fn get(&self, index: usize) -> Option<SmtSimplePattern<'a>> {
        Some(self.handles.get(index)?.view(self.text))
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = SmtSimplePattern<'a>> {
        let text = self.text;
        self.handles.iter().map(move |handle| handle.view(text))
    }
}

impl Debug for SmtSimplePatterns<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Owned arguments of a constructor pattern, from which [`SmtSimplePatterns`] is viewed.
#[derive(Clone)]
pub struct SmtSimplePatternsBuf {
    text: Vec<u8>,
    handles: Vec<SimplePatternHandle>,
}

impl SmtSimplePatternsBuf {
    pub fn new() -> Self {
        Self {
            text: Vec::new(),
            handles: Vec::new(),
        }
    }

    pub fn push(&mut self, pattern: SmtSimplePattern) {
        let pattern = SimplePatternHandle::create_by_push(&mut self.text, pattern);
        self.handles.push(pattern);
    }

    pub fn clear(&mut self) {
        self.text.clear();
        self.handles.clear();
    }

    pub fn view(&self) -> SmtSimplePatterns<'_> {
        SmtSimplePatterns {
            text: &self.text,
            handles: &self.handles,
        }
    }

    pub fn len(&self) -> usize {
        self.handles.len()
    }

    pub fn is_empty(&self) -> bool {
        self.handles.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<SmtSimplePattern<'_>> {
        Some(self.handles.get(index)?.view(&self.text))
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = SmtSimplePattern<'_>> {
        let text = self.text.as_slice();
        self.handles.iter().map(move |handle| handle.view(text))
    }
}

impl Default for SmtSimplePatternsBuf {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for SmtSimplePatternsBuf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.view().iter()).finish()
    }
}

/// Match pattern to be handled: a symbol, a wildcard, or a constructor application.
#[derive(Debug, Clone, Copy)]
pub enum SmtPattern<'a> {
    /// A simple match pattern, either a symbol or a wildcard.
    Simple(SmtSimplePattern<'a>),
    /// A constructor applied to at least one variable or wildcard.
    Application(SmtPatternApplication<'a>),
}

impl SmtPattern<'_> {
    pub fn into_owned(self) -> SmtPatternBuf {
        match self {
            Self::Simple(simple) => SmtPatternBuf::Simple(simple.into_owned()),
            Self::Application(application) => SmtPatternBuf::Application(application.into_owned()),
        }
    }
}

/// A constructor applied to at least one variable or wildcard, as a match pattern
/// to be handled.
#[derive(Debug, Clone, Copy)]
pub struct SmtPatternApplication<'a> {
    constructor: SmtSymbol<'a>,
    args: SmtSimplePatterns<'a>,
}

impl<'a> SmtPatternApplication<'a> {
    pub fn new(
        constructor: SmtSymbol<'a>,
        args: SmtSimplePatterns<'a>,
    ) -> Result<Self, SmtEmptyArgumentsError> {
        if args.is_empty() {
            return Err(SmtEmptyArgumentsError);
        }
        Ok(Self { constructor, args })
    }

    #[inline]
    pub(crate) fn new_unchecked(constructor: SmtSymbol<'a>, args: SmtSimplePatterns<'a>) -> Self {
        debug_assert!(!args.is_empty(), "a constructor pattern without arguments");
        Self { constructor, args }
    }

    pub fn constructor(&self) -> SmtSymbol<'a> {
        self.constructor
    }

    pub fn args(&self) -> SmtSimplePatterns<'a> {
        self.args
    }

    pub fn into_owned(self) -> SmtPatternApplicationBuf {
        let mut args = SmtSimplePatternsBuf::new();
        for arg in self.args.iter() {
            args.push(arg);
        }
        SmtPatternApplicationBuf {
            constructor: self.constructor.into_owned(),
            args,
        }
    }
}

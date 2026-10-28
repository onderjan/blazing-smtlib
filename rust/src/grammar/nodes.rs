use std::fmt::Debug;

use crate::{
    SmtNodeTypes,
    grammar::SmtMultiple,
    lexicon::{
        SmtBinDigits, SmtBinDigitsBuf, SmtDecimal, SmtDecimalBuf, SmtGeneralReserved, SmtHexDigits,
        SmtHexDigitsBuf, SmtKeyword, SmtKeywordBuf, SmtNumeral, SmtNumeralBuf, SmtReserved,
        SmtStringContent, SmtStringContentBuf, SmtSymbol, SmtSymbolBuf,
    },
    parser::{ArenaAccess, IndexHandle, SimplePatternHandle},
    token::{SmtAppendTokens, SmtToken, SmtTokensCursor},
};

/// Owned index of an identifier (numeral or symbol).
#[derive(Debug, Clone)]
pub enum SmtIndexBuf {
    /// Numeral, e.g. `32` in `(_ BitVec 32)`.
    Numeral(SmtNumeralBuf),
    /// Symbol, e.g. `up` in `(_ move up)`.
    Symbol(SmtSymbolBuf),
}

impl SmtIndexBuf {
    /// Views as [`SmtIndex`].
    pub fn view(&self) -> SmtIndex<'_> {
        match self {
            SmtIndexBuf::Numeral(numeral) => SmtIndex::Numeral(numeral.view()),
            SmtIndexBuf::Symbol(symbol) => SmtIndex::Symbol(symbol.view()),
        }
    }
}

/// Owned identifier.
#[derive(Debug, Clone)]
pub struct SmtIdentBuf {
    /// Name of the identifier.
    pub name: SmtSymbolBuf,
    /// Indices of the identifier.
    pub indices: SmtIndicesBuf,
}

impl SmtIdentBuf {
    /// Constructs a simple identifier: a name with no indices.
    pub fn new_simple(name: SmtSymbolBuf) -> SmtIdentBuf {
        SmtIdentBuf {
            name,
            indices: SmtIndicesBuf::new(),
        }
    }

    /// Views as [`SmtIdent`].
    pub fn view(&self) -> SmtIdent<'_> {
        SmtIdent {
            name: self.name.view(),
            indices: self.indices.view(),
        }
    }
}

/// Owned qualified identifier.
pub struct SmtQualifiedIdentBuf<N: SmtNodeTypes + ?Sized> {
    /// Identifier.
    pub ident: SmtIdentBuf,
    /// Sort that qualifies the identifier, if any.
    pub sort: Option<N::Sort>,
}

impl<N: SmtNodeTypes + ?Sized> SmtQualifiedIdentBuf<N> {
    /// Constructs a simple identifier with no sort.
    pub fn new_simple(name: SmtSymbolBuf) -> Self {
        Self::new_unqualified(SmtIdentBuf::new_simple(name))
    }

    /// Constructs an identifier with no sort.
    pub fn new_unqualified(ident: SmtIdentBuf) -> Self {
        Self { ident, sort: None }
    }

    /// Constructs an identifier qualified by the sort.
    pub fn new_qualified(ident: SmtIdentBuf, sort: N::Sort) -> Self {
        Self {
            ident,
            sort: Some(sort),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> Debug for SmtQualifiedIdentBuf<N>
where
    N::Sort: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtQualifiedIdentBuf")
            .field("ident", &self.ident)
            .field("sort", &self.sort)
            .finish()
    }
}

impl<N: SmtNodeTypes + ?Sized> Clone for SmtQualifiedIdentBuf<N>
where
    N::Sort: Clone,
{
    fn clone(&self) -> Self {
        Self {
            ident: self.ident.clone(),
            sort: self.sort.clone(),
        }
    }
}

/// View of an index of an identifier (numeral or symbol).
#[derive(Debug, Clone, Copy)]
pub enum SmtIndex<'a> {
    /// Numeral, e.g. `32` in `(_ BitVec 32)`.
    Numeral(SmtNumeral<'a>),
    /// Symbol, e.g. `up` in `(_ move up)`.
    Symbol(SmtSymbol<'a>),
}

impl SmtIndex<'_> {
    /// Converts into [`SmtIndexBuf`].
    pub fn into_owned(self) -> SmtIndexBuf {
        match self {
            SmtIndex::Numeral(numeral) => SmtIndexBuf::Numeral(numeral.into_owned()),
            SmtIndex::Symbol(symbol) => SmtIndexBuf::Symbol(symbol.into_owned()),
        }
    }
}

/// View of the indices of an identifier.
#[derive(Clone, Copy)]
pub struct SmtIndices<'a> {
    text: &'a [u8],
    handles: &'a [IndexHandle],
}

impl<'a> SmtIndices<'a> {
    pub(crate) fn new(_access: ArenaAccess, text: &'a [u8], handles: &'a [IndexHandle]) -> Self {
        Self { text, handles }
    }

    /// Constructs empty indices.
    pub fn empty() -> Self {
        Self {
            text: &[],
            handles: &[],
        }
    }

    /// Returns the number of indices.
    #[inline]
    pub fn len(&self) -> usize {
        self.handles.len()
    }

    /// Returns `true` if there are no indices.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.handles.is_empty()
    }

    /// Returns the index at the position, or [`None`] if it is out of bounds.
    #[inline]
    pub fn get(&self, index: usize) -> Option<SmtIndex<'a>> {
        Some(self.handles.get(index)?.view(self.text))
    }

    /// Returns an iterator over the indices.
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

/// Owned indices of an identifier.
#[derive(Clone)]
pub struct SmtIndicesBuf {
    text: Vec<u8>,
    handles: Vec<IndexHandle>,
}

impl SmtIndicesBuf {
    /// Constructs empty indices.
    pub fn new() -> Self {
        Self {
            text: Vec::new(),
            handles: Vec::new(),
        }
    }

    /// Copies the index after the others.
    pub fn push(&mut self, index: SmtIndex) {
        let index = IndexHandle::create_by_push(&mut self.text, index);
        self.handles.push(index);
    }

    /// Removes all indices.
    pub fn clear(&mut self) {
        self.text.clear();
        self.handles.clear();
    }

    /// Views as [`SmtIndices`].
    pub fn view(&self) -> SmtIndices<'_> {
        SmtIndices {
            text: &self.text,
            handles: &self.handles,
        }
    }

    /// Returns the number of indices.
    pub fn len(&self) -> usize {
        self.handles.len()
    }

    /// Returns `true` if there are no indices.
    pub fn is_empty(&self) -> bool {
        self.handles.is_empty()
    }

    /// Returns the index at the position, or [`None`] if it is out of bounds.
    pub fn get(&self, index: usize) -> Option<SmtIndex<'_>> {
        Some(self.handles.get(index)?.view(&self.text))
    }

    /// Returns an iterator over the indices.
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

/// View of an identifier.
#[derive(Debug, Clone, Copy)]
pub struct SmtIdent<'a> {
    /// Name of the identifier.
    pub name: SmtSymbol<'a>,
    /// Indices of the identifier.
    pub indices: SmtIndices<'a>,
}

impl SmtIdent<'_> {
    /// Converts into [`SmtIdentBuf`].
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

/// View of a qualified identifier.
pub struct SmtQualifiedIdent<'a, N: SmtNodeTypes + ?Sized> {
    /// Identifier.
    pub ident: SmtIdent<'a>,
    /// Sort that qualifies the identifier, if any.
    pub sort: Option<N::Sort>,
}

impl<N: SmtNodeTypes + ?Sized> SmtQualifiedIdent<'_, N> {
    /// Converts into [`SmtQualifiedIdentBuf`].
    pub fn into_owned(self) -> SmtQualifiedIdentBuf<N> {
        SmtQualifiedIdentBuf {
            ident: self.ident.into_owned(),
            sort: self.sort,
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> Debug for SmtQualifiedIdent<'_, N>
where
    N::Sort: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtQualifiedIdent")
            .field("ident", &self.ident)
            .field("sort", &self.sort)
            .finish()
    }
}

impl<N: SmtNodeTypes + ?Sized> Clone for SmtQualifiedIdent<'_, N>
where
    N::Sort: Clone,
{
    fn clone(&self) -> Self {
        Self {
            ident: self.ident,
            sort: self.sort.clone(),
        }
    }
}

/// Owned sort.
pub struct SmtSortBuf<N: SmtNodeTypes + ?Sized> {
    /// Identifier of the sort.
    pub ident: SmtIdentBuf,
    /// Arguments of the sort.
    pub args: Vec<N::Sort>,
}

impl<N: SmtNodeTypes + ?Sized> SmtSortBuf<N> {
    /// Views as [`SmtSort`], mutably.
    pub fn view_mut(&mut self) -> SmtSort<'_, N> {
        SmtSort {
            ident: self.ident.view(),
            args: SmtMultiple::new(&mut self.args),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> Debug for SmtSortBuf<N>
where
    N::Sort: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtSortBuf")
            .field("ident", &self.ident)
            .field("args", &self.args)
            .finish()
    }
}

impl<N: SmtNodeTypes + ?Sized> Clone for SmtSortBuf<N>
where
    N::Sort: Clone,
{
    fn clone(&self) -> Self {
        Self {
            ident: self.ident.clone(),
            args: self.args.clone(),
        }
    }
}

/// View of a sort.
pub struct SmtSort<'a, N: SmtNodeTypes + ?Sized> {
    /// Identifier of the sort.
    pub ident: SmtIdent<'a>,
    /// Arguments of the sort.
    pub args: SmtMultiple<'a, N::Sort>,
}

impl<N: SmtNodeTypes + ?Sized> SmtSort<'_, N> {
    /// Converts into [`SmtSortBuf`].
    pub fn into_owned(self) -> SmtSortBuf<N> {
        SmtSortBuf {
            ident: self.ident.into_owned(),
            args: self.args.into_iter().collect(),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> Debug for SmtSort<'_, N>
where
    N::Sort: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtSort")
            .field("ident", &self.ident)
            .field("args", &self.args)
            .finish()
    }
}

/// Owned application.
///
/// It is guaranteed that `args` are nonempty.
pub struct SmtApplicationBuf<N: SmtNodeTypes + ?Sized> {
    function: SmtQualifiedIdentBuf<N>,
    args: Vec<N::Term>,
}

impl<N: SmtNodeTypes + ?Sized> SmtApplicationBuf<N> {
    /// Constructs an application of `function` to `args` if `args` is nonempty.
    pub fn new(
        function: SmtQualifiedIdentBuf<N>,
        args: Vec<N::Term>,
    ) -> Result<Self, SmtEmptyArgumentsError> {
        if args.is_empty() {
            return Err(SmtEmptyArgumentsError);
        }
        Ok(Self { function, args })
    }

    /// Returns the applied function.
    pub fn function(&self) -> &SmtQualifiedIdentBuf<N> {
        &self.function
    }

    /// Returns the applied function, mutably.
    pub fn function_mut(&mut self) -> &mut SmtQualifiedIdentBuf<N> {
        &mut self.function
    }

    /// Returns the arguments of the application.
    pub fn args(&self) -> &[N::Term] {
        &self.args
    }

    /// Returns the arguments of the application, mutably.
    pub fn args_mut(&mut self) -> &mut [N::Term] {
        &mut self.args
    }

    /// Destructures into the function and the arguments.
    pub fn into_parts(self) -> (SmtQualifiedIdentBuf<N>, Vec<N::Term>) {
        (self.function, self.args)
    }
}

impl<N: SmtNodeTypes + ?Sized> Debug for SmtApplicationBuf<N>
where
    N::Sort: Debug,
    N::Term: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtApplicationBuf")
            .field("function", &self.function)
            .field("args", &self.args)
            .finish()
    }
}

impl<N: SmtNodeTypes + ?Sized> Clone for SmtApplicationBuf<N>
where
    N::Sort: Clone,
    N::Term: Clone,
{
    fn clone(&self) -> Self {
        Self {
            function: self.function.clone(),
            args: self.args.clone(),
        }
    }
}

/// View of an application.
///
/// It is guaranteed that `args` are nonempty.
pub struct SmtApplication<'a, N: SmtNodeTypes + ?Sized> {
    function: SmtQualifiedIdent<'a, N>,
    args: SmtMultiple<'a, N::Term>,
}

impl<'a, N: SmtNodeTypes + ?Sized> SmtApplication<'a, N> {
    /// Constructs an application of `function` to `args` if `args` is nonempty.
    pub fn new(
        function: SmtQualifiedIdent<'a, N>,
        args: SmtMultiple<'a, N::Term>,
    ) -> Result<Self, SmtEmptyArgumentsError> {
        if args.is_empty() {
            return Err(SmtEmptyArgumentsError);
        }
        Ok(Self { function, args })
    }

    #[inline]
    pub(crate) fn new_unchecked(
        function: SmtQualifiedIdent<'a, N>,
        args: SmtMultiple<'a, N::Term>,
    ) -> Self {
        debug_assert!(!args.is_empty(), "an application without arguments");
        Self { function, args }
    }

    /// Returns the applied function.
    pub fn function(&self) -> &SmtQualifiedIdent<'a, N> {
        &self.function
    }

    /// Returns the applied function, mutably.
    pub fn function_mut(&mut self) -> &mut SmtQualifiedIdent<'a, N> {
        &mut self.function
    }

    /// Returns the arguments of the application.
    pub fn args(&self) -> &SmtMultiple<'a, N::Term> {
        &self.args
    }

    /// Returns the arguments of the application, mutably.
    pub fn args_mut(&mut self) -> &mut [N::Term] {
        self.args.as_mut_slice()
    }

    /// Destructures into the function and the arguments.
    pub fn into_parts(self) -> (SmtQualifiedIdent<'a, N>, SmtMultiple<'a, N::Term>) {
        (self.function, self.args)
    }

    /// Converts into [`SmtApplicationBuf`].
    pub fn into_owned(self) -> SmtApplicationBuf<N> {
        SmtApplicationBuf {
            function: self.function.into_owned(),
            args: self.args.into_iter().collect(),
        }
    }
}

/// Error constructing an application or a constructor pattern without arguments.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SmtEmptyArgumentsError;

impl std::fmt::Display for SmtEmptyArgumentsError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("no arguments provided where at least one is required")
    }
}

impl std::error::Error for SmtEmptyArgumentsError {}

impl<N: SmtNodeTypes + ?Sized> Debug for SmtApplication<'_, N>
where
    N::Sort: Debug,
    N::Term: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtApplication")
            .field("function", &self.function)
            .field("args", &self.args)
            .finish()
    }
}

/// Owned special constant (numeral, decimal, hexadecimal, binary, or string).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SmtSpecialConstantBuf {
    /// Numeral, e.g. `0` or `42`.
    Numeral(SmtNumeralBuf),
    /// Decimal, e.g. `0.5` or `3.14`.
    Decimal(SmtDecimalBuf),
    /// Hexadecimal, e.g. `#xA04`.
    Hexadecimal(SmtHexDigitsBuf),
    /// Binary, e.g. `#b0101`.
    Binary(SmtBinDigitsBuf),
    /// String literal, e.g. `"hello"` or `""`.
    String(SmtStringContentBuf),
}

impl SmtSpecialConstantBuf {
    /// Views as [`SmtSpecialConstant`].
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

/// View of a special constant (numeral, decimal, hexadecimal, binary, or string).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtSpecialConstant<'a> {
    /// Numeral, e.g. `0` or `42`.
    Numeral(SmtNumeral<'a>),
    /// Decimal, e.g. `0.5` or `3.14`.
    Decimal(SmtDecimal<'a>),
    /// Hexadecimal, e.g. `#xA04`.
    Hexadecimal(SmtHexDigits<'a>),
    /// Binary, e.g. `#b0101`.
    Binary(SmtBinDigits<'a>),
    /// String literal, e.g. `"hello"` or `""`.
    String(SmtStringContent<'a>),
}

impl SmtSpecialConstant<'_> {
    /// Converts into [`SmtSpecialConstantBuf`].
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

/// Owned term (special constant, qualified identifier, or application).
pub enum SmtTermBuf<N: SmtNodeTypes + ?Sized> {
    /// Special constant, e.g. `42` or `"hello"`.
    SpecialConstant(SmtSpecialConstantBuf),
    /// Qualified identifier, e.g. `x`, `(_ bv0 32)` or `(as nil (List Int))`.
    QualifiedIdent(SmtQualifiedIdentBuf<N>),
    /// Application, e.g. `(+ x 1)`.
    Application(SmtApplicationBuf<N>),
}

impl<N: SmtNodeTypes + ?Sized> Debug for SmtTermBuf<N>
where
    N::Sort: Debug,
    N::Term: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SpecialConstant(arg0) => f.debug_tuple("SpecialConstant").field(arg0).finish(),
            Self::QualifiedIdent(arg0) => f.debug_tuple("QualifiedIdent").field(arg0).finish(),
            Self::Application(arg0) => f.debug_tuple("Application").field(arg0).finish(),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> Clone for SmtTermBuf<N>
where
    N::Sort: Clone,
    N::Term: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::SpecialConstant(constant) => Self::SpecialConstant(constant.clone()),
            Self::QualifiedIdent(ident) => Self::QualifiedIdent(ident.clone()),
            Self::Application(application) => Self::Application(application.clone()),
        }
    }
}

/// View of a term (special constant, qualified identifier, or application).
pub enum SmtTerm<'a, N: SmtNodeTypes + ?Sized> {
    /// Special constant, e.g. `42` or `"hello"`.
    SpecialConstant(SmtSpecialConstant<'a>),
    /// Qualified identifier, e.g. `x`, `(_ bv0 32)` or `(as nil (List Int))`.
    QualifiedIdent(SmtQualifiedIdent<'a, N>),
    /// Application, e.g. `(+ x 1)`.
    Application(SmtApplication<'a, N>),
}

impl<N: SmtNodeTypes + ?Sized> SmtTerm<'_, N> {
    /// Converts into [`SmtTermBuf`].
    pub fn into_owned(self) -> SmtTermBuf<N> {
        match self {
            Self::SpecialConstant(constant) => SmtTermBuf::SpecialConstant(constant.into_owned()),
            Self::QualifiedIdent(ident) => SmtTermBuf::QualifiedIdent(ident.into_owned()),
            Self::Application(application) => SmtTermBuf::Application(application.into_owned()),
        }
    }
}

/// Kind of a quantifier (existential or universal).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SmtQuantifierKind {
    /// Existential quantifier (`exists`).
    Exists,
    /// Universal quantifier (`forall`).
    Forall,
}

impl<N: SmtNodeTypes + ?Sized> Debug for SmtTerm<'_, N>
where
    N::Sort: Debug,
    N::Term: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SpecialConstant(arg0) => f.debug_tuple("SpecialConstant").field(arg0).finish(),
            Self::QualifiedIdent(arg0) => f.debug_tuple("QualifiedIdent").field(arg0).finish(),
            Self::Application(arg0) => f.debug_tuple("Application").field(arg0).finish(),
        }
    }
}

/// Owned attribute value (special constant, symbol, or a list of S-expressions).
pub enum SmtAttributeValueBuf<N: SmtNodeTypes + ?Sized> {
    /// Special constant, e.g. `2.6` in `:smt-lib-version 2.6`.
    SpecialConstant(SmtSpecialConstantBuf),
    /// Symbol, e.g. `sat` in `:status sat`.
    Symbol(SmtSymbolBuf),
    /// List of S-expressions, e.g. `(a 1)` in `:my-attribute (a 1)`.
    SExprs(Vec<N::SExpr>),
}

impl<N: SmtNodeTypes + ?Sized> SmtAttributeValueBuf<N> {
    /// Views as [`SmtAttributeValue`], mutably.
    pub fn view_mut(&mut self) -> SmtAttributeValue<'_, N> {
        match self {
            Self::SpecialConstant(constant) => SmtAttributeValue::SpecialConstant(constant.view()),
            Self::Symbol(symbol) => SmtAttributeValue::Symbol(symbol.view()),
            Self::SExprs(s_exprs) => SmtAttributeValue::SExprs(SmtMultiple::new(s_exprs)),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> Debug for SmtAttributeValueBuf<N>
where
    N::SExpr: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SpecialConstant(arg0) => f.debug_tuple("SpecialConstant").field(arg0).finish(),
            Self::Symbol(arg0) => f.debug_tuple("Symbol").field(arg0).finish(),
            Self::SExprs(arg0) => f.debug_tuple("SExprs").field(arg0).finish(),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> Clone for SmtAttributeValueBuf<N>
where
    N::SExpr: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::SpecialConstant(constant) => Self::SpecialConstant(constant.clone()),
            Self::Symbol(symbol) => Self::Symbol(symbol.clone()),
            Self::SExprs(s_exprs) => Self::SExprs(s_exprs.clone()),
        }
    }
}

/// View of an attribute value (special constant, symbol, or a list of S-expressions).
pub enum SmtAttributeValue<'a, N: SmtNodeTypes + ?Sized> {
    /// Special constant, e.g. `2.6` in `:smt-lib-version 2.6`.
    SpecialConstant(SmtSpecialConstant<'a>),
    /// Symbol, e.g. `sat` in `:status sat`.
    Symbol(SmtSymbol<'a>),
    /// List of S-expressions, e.g. `(a 1)` in `:my-attribute (a 1)`.
    SExprs(SmtMultiple<'a, N::SExpr>),
}

impl<N: SmtNodeTypes + ?Sized> SmtAttributeValue<'_, N> {
    /// Converts into [`SmtAttributeValueBuf`].
    pub fn into_owned(self) -> SmtAttributeValueBuf<N> {
        match self {
            Self::SpecialConstant(constant) => {
                SmtAttributeValueBuf::SpecialConstant(constant.into_owned())
            }
            Self::Symbol(symbol) => SmtAttributeValueBuf::Symbol(symbol.into_owned()),
            Self::SExprs(s_exprs) => SmtAttributeValueBuf::SExprs(s_exprs.into_iter().collect()),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> Debug for SmtAttributeValue<'_, N>
where
    N::SExpr: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SpecialConstant(arg0) => f.debug_tuple("SpecialConstant").field(arg0).finish(),
            Self::Symbol(arg0) => f.debug_tuple("Symbol").field(arg0).finish(),
            Self::SExprs(arg0) => f.debug_tuple("SExprs").field(arg0).finish(),
        }
    }
}

/// Owned simple match pattern (symbol or wildcard).
#[derive(Debug, Clone)]
pub enum SmtSimplePatternBuf {
    /// Symbol as a pattern, e.g. `x` or `nil`.
    ///
    /// In the match pattern position, the symbol should be
    /// either a variable or a nullary constructor, and
    /// it is not possible to determine syntactically which one it is.
    /// In the constructor application argument position,
    /// it should be a variable.
    Symbol(SmtSymbolBuf),
    /// Wildcard as a pattern.
    ///
    /// The wildcard is the reserved word `_`.
    Wildcard,
}

impl SmtSimplePatternBuf {
    /// Views as [`SmtSimplePattern`].
    pub fn view(&self) -> SmtSimplePattern<'_> {
        match self {
            Self::Symbol(symbol) => SmtSimplePattern::Symbol(symbol.view()),
            Self::Wildcard => SmtSimplePattern::Wildcard,
        }
    }
}

/// Owned match pattern (simple or constructor pattern).
#[derive(Debug, Clone)]
pub enum SmtPatternBuf {
    /// Simple match pattern, e.g. `x`, `nil` or `_`.
    Simple(SmtSimplePatternBuf),
    /// Constructor pattern, e.g. `(cons h t)`.
    Application(SmtPatternApplicationBuf),
}

impl SmtPatternBuf {
    /// Views as [`SmtPattern`].
    pub fn view(&self) -> SmtPattern<'_> {
        match self {
            Self::Simple(simple) => SmtPattern::Simple(simple.view()),
            Self::Application(application) => SmtPattern::Application(application.view()),
        }
    }
}

/// Owned constructor pattern.
///
/// It is a constructor applied to at least one variable or wildcard.
#[derive(Debug, Clone)]
pub struct SmtPatternApplicationBuf {
    constructor: SmtSymbolBuf,
    args: SmtSimplePatternsBuf,
}

impl SmtPatternApplicationBuf {
    /// Constructs a pattern that applies `constructor` to `args` if `args` is nonempty.
    pub fn new(
        constructor: SmtSymbolBuf,
        args: SmtSimplePatternsBuf,
    ) -> Result<Self, SmtEmptyArgumentsError> {
        if args.is_empty() {
            return Err(SmtEmptyArgumentsError);
        }
        Ok(Self { constructor, args })
    }

    /// Returns the applied constructor.
    pub fn constructor(&self) -> &SmtSymbolBuf {
        &self.constructor
    }

    /// Returns the arguments of the pattern.
    pub fn args(&self) -> &SmtSimplePatternsBuf {
        &self.args
    }

    /// Destructures into the constructor and the arguments.
    pub fn into_parts(self) -> (SmtSymbolBuf, SmtSimplePatternsBuf) {
        (self.constructor, self.args)
    }

    /// Views as [`SmtPatternApplication`].
    pub fn view(&self) -> SmtPatternApplication<'_> {
        SmtPatternApplication {
            constructor: self.constructor.view(),
            args: self.args.view(),
        }
    }
}

/// Owned S-expression (special constant, symbol, reserved word, keyword, or a list of
/// S-expressions).
pub enum SmtSExprBuf<N: SmtNodeTypes + ?Sized> {
    /// Special constant, e.g. `42` or `"hello"`.
    SpecialConstant(SmtSpecialConstantBuf),
    /// Symbol, e.g. `x` or `|a b|`.
    Symbol(SmtSymbolBuf),
    /// Reserved word, e.g. `let` or `_`.
    Reserved(SmtReserved),
    /// Keyword, e.g. `:named`.
    Keyword(SmtKeywordBuf),
    /// List of S-expressions, e.g. `(a (b 1))`.
    SExprs(Vec<N::SExpr>),
}

impl<N: SmtNodeTypes + ?Sized> SmtSExprBuf<N> {
    /// Views as [`SmtSExpr`], mutably.
    pub fn view_mut(&mut self) -> SmtSExpr<'_, N> {
        match self {
            Self::SpecialConstant(constant) => SmtSExpr::SpecialConstant(constant.view()),
            Self::Symbol(symbol) => SmtSExpr::Symbol(symbol.view()),
            Self::Reserved(reserved) => SmtSExpr::Reserved(*reserved),
            Self::Keyword(keyword) => SmtSExpr::Keyword(keyword.view()),
            Self::SExprs(s_exprs) => SmtSExpr::SExprs(SmtMultiple::new(s_exprs)),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> Debug for SmtSExprBuf<N>
where
    N::SExpr: Debug,
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

impl<N: SmtNodeTypes + ?Sized> Clone for SmtSExprBuf<N>
where
    N::SExpr: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::SpecialConstant(constant) => Self::SpecialConstant(constant.clone()),
            Self::Symbol(symbol) => Self::Symbol(symbol.clone()),
            Self::Reserved(reserved) => Self::Reserved(*reserved),
            Self::Keyword(keyword) => Self::Keyword(keyword.clone()),
            Self::SExprs(s_exprs) => Self::SExprs(s_exprs.clone()),
        }
    }
}

/// View of an S-expression (special constant, symbol, reserved word, keyword, or a list of
/// S-expressions).
pub enum SmtSExpr<'a, N: SmtNodeTypes + ?Sized> {
    /// Special constant, e.g. `42` or `"hello"`.
    SpecialConstant(SmtSpecialConstant<'a>),
    /// Symbol, e.g. `x` or `|a b|`.
    Symbol(SmtSymbol<'a>),
    /// Reserved word, e.g. `let` or `_`.
    Reserved(SmtReserved),
    /// Keyword, e.g. `:named`.
    Keyword(SmtKeyword<'a>),
    /// List of S-expressions, e.g. `(a (b 1))`.
    SExprs(SmtMultiple<'a, N::SExpr>),
}

impl<N: SmtNodeTypes + ?Sized> SmtSExpr<'_, N> {
    /// Converts into [`SmtSExprBuf`].
    pub fn into_owned(self) -> SmtSExprBuf<N> {
        match self {
            Self::SpecialConstant(constant) => SmtSExprBuf::SpecialConstant(constant.into_owned()),
            Self::Symbol(symbol) => SmtSExprBuf::Symbol(symbol.into_owned()),
            Self::Reserved(reserved) => SmtSExprBuf::Reserved(reserved),
            Self::Keyword(keyword) => SmtSExprBuf::Keyword(keyword.into_owned()),
            Self::SExprs(s_exprs) => SmtSExprBuf::SExprs(s_exprs.into_iter().collect()),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> Debug for SmtSExpr<'_, N>
where
    N::SExpr: Debug,
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

/// View of a simple match pattern (symbol or wildcard).
#[derive(Debug, Clone, Copy)]
pub enum SmtSimplePattern<'a> {
    /// Symbol as a pattern, e.g. `x` or `nil`.
    ///
    /// In the match pattern position, the symbol should be
    /// either a variable or a nullary constructor, and
    /// it is not possible to determine syntactically which one it is.
    /// In the constructor application argument position,
    /// it should be a variable.
    Symbol(SmtSymbol<'a>),
    /// Wildcard as a pattern.
    ///
    /// The wildcard is the reserved word `_`.
    Wildcard,
}

impl SmtSimplePattern<'_> {
    /// Converts into [`SmtSimplePatternBuf`].
    pub fn into_owned(self) -> SmtSimplePatternBuf {
        match self {
            Self::Symbol(symbol) => SmtSimplePatternBuf::Symbol(symbol.into_owned()),
            Self::Wildcard => SmtSimplePatternBuf::Wildcard,
        }
    }
}

/// View of the arguments of a constructor pattern.
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

    /// Returns the number of arguments.
    #[inline]
    pub fn len(&self) -> usize {
        self.handles.len()
    }

    /// Returns `true` if there are no arguments.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.handles.is_empty()
    }

    /// Returns the argument at the position, or [`None`] if it is out of bounds.
    #[inline]
    pub fn get(&self, index: usize) -> Option<SmtSimplePattern<'a>> {
        Some(self.handles.get(index)?.view(self.text))
    }

    /// Returns an iterator over the arguments.
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

/// Owned arguments of a constructor pattern.
#[derive(Clone)]
pub struct SmtSimplePatternsBuf {
    text: Vec<u8>,
    handles: Vec<SimplePatternHandle>,
}

impl SmtSimplePatternsBuf {
    /// Constructs empty arguments.
    pub fn new() -> Self {
        Self {
            text: Vec::new(),
            handles: Vec::new(),
        }
    }

    /// Copies the argument after the others.
    pub fn push(&mut self, pattern: SmtSimplePattern) {
        let pattern = SimplePatternHandle::create_by_push(&mut self.text, pattern);
        self.handles.push(pattern);
    }

    /// Removes all arguments.
    pub fn clear(&mut self) {
        self.text.clear();
        self.handles.clear();
    }

    /// Views as [`SmtSimplePatterns`].
    pub fn view(&self) -> SmtSimplePatterns<'_> {
        SmtSimplePatterns {
            text: &self.text,
            handles: &self.handles,
        }
    }

    /// Returns the number of arguments.
    pub fn len(&self) -> usize {
        self.handles.len()
    }

    /// Returns `true` if there are no arguments.
    pub fn is_empty(&self) -> bool {
        self.handles.is_empty()
    }

    /// Returns the argument at the position, or [`None`] if it is out of bounds.
    pub fn get(&self, index: usize) -> Option<SmtSimplePattern<'_>> {
        Some(self.handles.get(index)?.view(&self.text))
    }

    /// Returns an iterator over the arguments.
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

/// View of a match pattern (simple or constructor pattern).
#[derive(Debug, Clone, Copy)]
pub enum SmtPattern<'a> {
    /// Simple match pattern, e.g. `x`, `nil` or `_`.
    Simple(SmtSimplePattern<'a>),
    /// Constructor pattern, e.g. `(cons h t)`.
    Application(SmtPatternApplication<'a>),
}

impl SmtPattern<'_> {
    /// Converts into [`SmtPatternBuf`].
    pub fn into_owned(self) -> SmtPatternBuf {
        match self {
            Self::Simple(simple) => SmtPatternBuf::Simple(simple.into_owned()),
            Self::Application(application) => SmtPatternBuf::Application(application.into_owned()),
        }
    }
}

/// View of a constructor pattern.
///
/// It is a constructor applied to at least one variable or wildcard.
#[derive(Debug, Clone, Copy)]
pub struct SmtPatternApplication<'a> {
    constructor: SmtSymbol<'a>,
    args: SmtSimplePatterns<'a>,
}

impl<'a> SmtPatternApplication<'a> {
    /// Constructs a pattern that applies `constructor` to `args` if `args` is nonempty.
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

    /// Returns the applied constructor.
    pub fn constructor(&self) -> SmtSymbol<'a> {
        self.constructor
    }

    /// Returns the arguments of the pattern.
    pub fn args(&self) -> SmtSimplePatterns<'a> {
        self.args
    }

    /// Converts into [`SmtPatternApplicationBuf`].
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

fn append_index<'a>(index: SmtIndex<'a>, tokens: &mut SmtTokensCursor<'a>) {
    tokens.push(match index {
        SmtIndex::Numeral(numeral) => SmtToken::Numeral(numeral),
        SmtIndex::Symbol(symbol) => SmtToken::Symbol(symbol),
    });
}

fn append_indices<'a>(indices: SmtIndices<'a>, tokens: &mut SmtTokensCursor<'a>) {
    for index in indices.iter() {
        append_index(index, tokens);
    }
}

/// Appends an identifier.
fn append_ident<'a>(ident: SmtIdent<'a>, tokens: &mut SmtTokensCursor<'a>) {
    if ident.indices.is_empty() {
        // just the symbol
        tokens.push(SmtToken::Symbol(ident.name));
    } else {
        // indexed identifier: ( _ symbol index+ ).
        tokens.push(SmtToken::ParenOpen);
        tokens.push(SmtToken::Reserved(SmtReserved::General(
            SmtGeneralReserved::Underscore,
        )));
        tokens.push(SmtToken::Symbol(ident.name));
        append_indices(ident.indices, tokens);
        tokens.push(SmtToken::ParenClose);
    }
}

/// Appends a potentially qualified identifier.
fn append_qualified_ident<'a, S: SmtAppendTokens>(
    ident: SmtIdent<'a>,
    sort: Option<&'a S>,
    tokens: &mut SmtTokensCursor<'a>,
) {
    match sort {
        None => append_ident(ident, tokens),
        Some(sort) => {
            // use the qualification syntax: ( as identifier sort )
            tokens.push(SmtToken::ParenOpen);
            tokens.push(SmtToken::Reserved(SmtReserved::General(
                SmtGeneralReserved::As,
            )));
            append_ident(ident, tokens);
            sort.append_tokens(tokens);
            tokens.push(SmtToken::ParenClose);
        }
    }
}

fn append_special_constant<'a>(constant: SmtSpecialConstant<'a>, tokens: &mut SmtTokensCursor<'a>) {
    tokens.push(match constant {
        SmtSpecialConstant::Numeral(value) => SmtToken::Numeral(value),
        SmtSpecialConstant::Decimal(value) => SmtToken::Decimal(value),
        SmtSpecialConstant::Hexadecimal(value) => SmtToken::Hexadecimal(value),
        SmtSpecialConstant::Binary(value) => SmtToken::Binary(value),
        SmtSpecialConstant::String(value) => SmtToken::String(value),
    });
}

fn append_simple_pattern<'a>(pattern: SmtSimplePattern<'a>, tokens: &mut SmtTokensCursor<'a>) {
    tokens.push(match pattern {
        SmtSimplePattern::Symbol(symbol) => SmtToken::Symbol(symbol),
        SmtSimplePattern::Wildcard => {
            SmtToken::Reserved(SmtReserved::General(SmtGeneralReserved::Underscore))
        }
    });
}

fn append_simple_patterns<'a>(patterns: SmtSimplePatterns<'a>, tokens: &mut SmtTokensCursor<'a>) {
    for pattern in patterns.iter() {
        append_simple_pattern(pattern, tokens);
    }
}

/// Appends a pattern application.
fn append_pattern_application<'a>(
    application: SmtPatternApplication<'a>,
    tokens: &mut SmtTokensCursor<'a>,
) {
    // use the pattern application syntax: ( constructor pattern+ )
    tokens.push(SmtToken::ParenOpen);
    tokens.push(SmtToken::Symbol(application.constructor));
    append_simple_patterns(application.args, tokens);
    tokens.push(SmtToken::ParenClose);
}

fn append_pattern<'a>(pattern: SmtPattern<'a>, tokens: &mut SmtTokensCursor<'a>) {
    match pattern {
        SmtPattern::Simple(simple) => append_simple_pattern(simple, tokens),
        SmtPattern::Application(application) => append_pattern_application(application, tokens),
    }
}

/// Defines the appending of a node, viewed or owned, by the function that
/// appends its view.
macro_rules! append_tokens_by_view {
    ($view:ident, $buf:ty, $append:ident) => {
        impl SmtAppendTokens for $view<'_> {
            fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
                $append(*self, tokens);
            }
        }

        impl SmtAppendTokens for $buf {
            fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
                $append(self.view(), tokens);
            }
        }
    };
}

append_tokens_by_view!(SmtIndex, SmtIndexBuf, append_index);
append_tokens_by_view!(SmtIndices, SmtIndicesBuf, append_indices);
append_tokens_by_view!(SmtIdent, SmtIdentBuf, append_ident);
append_tokens_by_view!(
    SmtSpecialConstant,
    SmtSpecialConstantBuf,
    append_special_constant
);
append_tokens_by_view!(SmtSimplePattern, SmtSimplePatternBuf, append_simple_pattern);
append_tokens_by_view!(
    SmtSimplePatterns,
    SmtSimplePatternsBuf,
    append_simple_patterns
);
append_tokens_by_view!(
    SmtPatternApplication,
    SmtPatternApplicationBuf,
    append_pattern_application
);
append_tokens_by_view!(SmtPattern, SmtPatternBuf, append_pattern);

impl<N: SmtNodeTypes + ?Sized> SmtAppendTokens for SmtQualifiedIdent<'_, N>
where
    N::Sort: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        append_qualified_ident(self.ident, self.sort.as_ref(), tokens);
    }
}

impl<N: SmtNodeTypes + ?Sized> SmtAppendTokens for SmtQualifiedIdentBuf<N>
where
    N::Sort: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        append_qualified_ident(self.ident.view(), self.sort.as_ref(), tokens);
    }
}

/// Appends a sort of the identifier with the arguments.
fn append_sort<'a, S: SmtAppendTokens>(
    ident: SmtIdent<'a>,
    args: &'a [S],
    tokens: &mut SmtTokensCursor<'a>,
) {
    if args.is_empty() {
        // a sort without arguments is represented by its identifier
        append_ident(ident, tokens);
    } else {
        // use the syntax for a sort with arguments: ( identifier sort+ )
        tokens.push(SmtToken::ParenOpen);
        append_ident(ident, tokens);
        append_values(args, tokens);
        tokens.push(SmtToken::ParenClose);
    }
}

/// Appends an application of the potentially qualified identifier to the arguments.
fn append_application<'a, S: SmtAppendTokens, T: SmtAppendTokens>(
    function: SmtIdent<'a>,
    sort: Option<&'a S>,
    args: &'a [T],
    tokens: &mut SmtTokensCursor<'a>,
) {
    // use the application syntax: ( function term+ )
    tokens.push(SmtToken::ParenOpen);
    append_qualified_ident(function, sort, tokens);
    append_values(args, tokens);
    tokens.push(SmtToken::ParenClose);
}

/// Appends a list of S-expressions, enclosed in parentheses: ( s_expr* ).
fn append_s_exprs<'a, E: SmtAppendTokens>(s_exprs: &'a [E], tokens: &mut SmtTokensCursor<'a>) {
    tokens.push(SmtToken::ParenOpen);
    append_values(s_exprs, tokens);
    tokens.push(SmtToken::ParenClose);
}

/// Appends the values one after another.
fn append_values<'a, V: SmtAppendTokens>(values: &'a [V], tokens: &mut SmtTokensCursor<'a>) {
    for value in values {
        value.append_tokens(tokens);
    }
}

impl<N: SmtNodeTypes + ?Sized> SmtAppendTokens for SmtSort<'_, N>
where
    N::Sort: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        append_sort(self.ident, self.args.as_slice(), tokens);
    }
}

impl<N: SmtNodeTypes + ?Sized> SmtAppendTokens for SmtSortBuf<N>
where
    N::Sort: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        append_sort(self.ident.view(), &self.args, tokens);
    }
}

impl<N: SmtNodeTypes + ?Sized> SmtAppendTokens for SmtApplication<'_, N>
where
    N::Sort: SmtAppendTokens,
    N::Term: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        append_application(
            self.function.ident,
            self.function.sort.as_ref(),
            self.args.as_slice(),
            tokens,
        );
    }
}

impl<N: SmtNodeTypes + ?Sized> SmtAppendTokens for SmtApplicationBuf<N>
where
    N::Sort: SmtAppendTokens,
    N::Term: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        append_application(
            self.function.ident.view(),
            self.function.sort.as_ref(),
            &self.args,
            tokens,
        );
    }
}

impl<N: SmtNodeTypes + ?Sized> SmtAppendTokens for SmtTerm<'_, N>
where
    N::Sort: SmtAppendTokens,
    N::Term: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        match self {
            Self::SpecialConstant(constant) => append_special_constant(*constant, tokens),
            Self::QualifiedIdent(ident) => ident.append_tokens(tokens),
            Self::Application(application) => application.append_tokens(tokens),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> SmtAppendTokens for SmtTermBuf<N>
where
    N::Sort: SmtAppendTokens,
    N::Term: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        match self {
            Self::SpecialConstant(constant) => append_special_constant(constant.view(), tokens),
            Self::QualifiedIdent(ident) => ident.append_tokens(tokens),
            Self::Application(application) => application.append_tokens(tokens),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> SmtAppendTokens for SmtAttributeValue<'_, N>
where
    N::SExpr: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        match self {
            Self::SpecialConstant(constant) => append_special_constant(*constant, tokens),
            Self::Symbol(symbol) => tokens.push(SmtToken::Symbol(*symbol)),
            Self::SExprs(s_exprs) => append_s_exprs(s_exprs.as_slice(), tokens),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> SmtAppendTokens for SmtAttributeValueBuf<N>
where
    N::SExpr: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        match self {
            Self::SpecialConstant(constant) => append_special_constant(constant.view(), tokens),
            Self::Symbol(symbol) => tokens.push(SmtToken::Symbol(symbol.view())),
            Self::SExprs(s_exprs) => append_s_exprs(s_exprs, tokens),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> SmtAppendTokens for SmtSExpr<'_, N>
where
    N::SExpr: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        match self {
            Self::SpecialConstant(constant) => append_special_constant(*constant, tokens),
            Self::Symbol(symbol) => tokens.push(SmtToken::Symbol(*symbol)),
            Self::Reserved(reserved) => tokens.push(SmtToken::Reserved(*reserved)),
            Self::Keyword(keyword) => tokens.push(SmtToken::Keyword(*keyword)),
            Self::SExprs(s_exprs) => append_s_exprs(s_exprs.as_slice(), tokens),
        }
    }
}

impl<N: SmtNodeTypes + ?Sized> SmtAppendTokens for SmtSExprBuf<N>
where
    N::SExpr: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        match self {
            Self::SpecialConstant(constant) => append_special_constant(constant.view(), tokens),
            Self::Symbol(symbol) => tokens.push(SmtToken::Symbol(symbol.view())),
            Self::Reserved(reserved) => tokens.push(SmtToken::Reserved(*reserved)),
            Self::Keyword(keyword) => tokens.push(SmtToken::Keyword(keyword.view())),
            Self::SExprs(s_exprs) => append_s_exprs(s_exprs, tokens),
        }
    }
}

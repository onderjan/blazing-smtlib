use std::fmt::Debug;

use crate::{
    SmtHandler,
    grammar::SmtMultiple,
    lexicon::{
        SmtBinDigits, SmtBinDigitsBuf, SmtDecimal, SmtDecimalBuf, SmtHexDigits, SmtHexDigitsBuf,
        SmtKeyword, SmtNumeral, SmtNumeralBuf, SmtStringContent, SmtStringContentBuf, SmtSymbol,
        SmtSymbolBuf,
    },
    parser::{ArenaAccess, IndexHandle, SimplePatternHandle},
    token::{SmtAppendTokens, SmtGeneralReserved, SmtReserved, SmtToken, SmtTokensCursor},
};

/// Owned index of an identifier (numeral or symbol).
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

/// Owned identifier.
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

/// Owned qualified identifier.
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

/// View of an index of an identifier (numeral or symbol).
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

/// Owned indices of an identifier.
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

/// View of an identifier.
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

/// View of a qualified identifier.
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

/// View of a sort.
pub struct SmtSort<'a, H: SmtHandler + ?Sized> {
    pub ident: SmtIdent<'a>,
    pub args: SmtMultiple<'a, H::Sort>,
}

impl<H: SmtHandler + ?Sized> Debug for SmtSort<'_, H>
where
    H::Sort: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtSort")
            .field("ident", &self.ident)
            .field("args", &self.args)
            .finish()
    }
}

/// View of an application.
///
/// It is guaranteed that `args` are nonempty.
pub struct SmtApplication<'a, H: SmtHandler + ?Sized> {
    function: SmtQualifiedIdent<'a, H>,
    args: SmtMultiple<'a, H::Term>,
}

impl<'a, H: SmtHandler + ?Sized> SmtApplication<'a, H> {
    pub fn new(
        function: SmtQualifiedIdent<'a, H>,
        args: SmtMultiple<'a, H::Term>,
    ) -> Result<Self, SmtEmptyArgumentsError> {
        if args.is_empty() {
            return Err(SmtEmptyArgumentsError);
        }
        Ok(Self { function, args })
    }

    #[inline]
    pub(crate) fn new_unchecked(
        function: SmtQualifiedIdent<'a, H>,
        args: SmtMultiple<'a, H::Term>,
    ) -> Self {
        debug_assert!(!args.is_empty(), "an application without arguments");
        Self { function, args }
    }

    pub fn function(&self) -> &SmtQualifiedIdent<'a, H> {
        &self.function
    }

    pub fn function_mut(&mut self) -> &mut SmtQualifiedIdent<'a, H> {
        &mut self.function
    }

    pub fn args(&self) -> &SmtMultiple<'a, H::Term> {
        &self.args
    }

    pub fn args_mut(&mut self) -> &mut [H::Term] {
        self.args.as_mut_slice()
    }

    pub fn into_parts(self) -> (SmtQualifiedIdent<'a, H>, SmtMultiple<'a, H::Term>) {
        (self.function, self.args)
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

/// Owned special constant (numeral, decimal, hexadecimal, binary, or string).
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

/// View of a special constant (numeral, decimal, hexadecimal, binary, or string).
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

/// View of a term (special constant, qualified identifier, or application).
pub enum SmtTerm<'a, H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstant<'a>),
    QualifiedIdent(SmtQualifiedIdent<'a, H>),
    Application(SmtApplication<'a, H>),
}

/// Kind of a quantifier (existential or universal).
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

/// View of an attribute value (special constant, symbol, or a list of S-expressions).
pub enum SmtAttributeValue<'a, H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstant<'a>),
    Symbol(SmtSymbol<'a>),
    SExprs(SmtMultiple<'a, H::SExpr>),
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

/// Owned simple match pattern (symbol or wildcard).
#[derive(Debug, Clone)]
pub enum SmtSimplePatternBuf {
    /// Symbol as a pattern.
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
    /// Simple match pattern.
    Simple(SmtSimplePatternBuf),
    /// Constructor pattern.
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

/// Owned constructor pattern.
///
/// It is a constructor applied to at least one variable or wildcard.
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

/// View of an S-expression (special constant, symbol, reserved word, keyword, or a list of
/// S-expressions).
pub enum SmtSExpr<'a, H: SmtHandler + ?Sized> {
    SpecialConstant(SmtSpecialConstant<'a>),
    Symbol(SmtSymbol<'a>),
    Reserved(SmtReserved),
    Keyword(SmtKeyword<'a>),
    SExprs(SmtMultiple<'a, H::SExpr>),
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

/// View of a simple match pattern (symbol or wildcard).
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

/// Owned arguments of a constructor pattern.
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

/// View of a match pattern (simple or constructor pattern).
#[derive(Debug, Clone, Copy)]
pub enum SmtPattern<'a> {
    /// Simple match pattern.
    Simple(SmtSimplePattern<'a>),
    /// Constructor pattern.
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

/// View of a constructor pattern.
///
/// It is a constructor applied to at least one variable or wildcard.
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

impl<H: SmtHandler + ?Sized> SmtAppendTokens for SmtQualifiedIdent<'_, H>
where
    H::Sort: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        append_qualified_ident(self.ident, self.sort.as_ref(), tokens);
    }
}

impl<H: SmtHandler + ?Sized> SmtAppendTokens for SmtQualifiedIdentBuf<H>
where
    H::Sort: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        append_qualified_ident(self.ident.view(), self.sort.as_ref(), tokens);
    }
}

impl<H: SmtHandler + ?Sized> SmtAppendTokens for SmtSort<'_, H>
where
    H::Sort: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        if self.args.is_empty() {
            // a sort without arguments is represented by its identifier
            append_ident(self.ident, tokens);
        } else {
            // use the syntax for a sort with arguments: ( identifier sort+ )
            tokens.push(SmtToken::ParenOpen);
            append_ident(self.ident, tokens);
            self.args.append_tokens(tokens);
            tokens.push(SmtToken::ParenClose);
        }
    }
}

impl<H: SmtHandler + ?Sized> SmtAppendTokens for SmtApplication<'_, H>
where
    H::Sort: SmtAppendTokens,
    H::Term: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        // use the application syntax: ( function term+ )
        tokens.push(SmtToken::ParenOpen);
        self.function.append_tokens(tokens);
        self.args.append_tokens(tokens);
        tokens.push(SmtToken::ParenClose);
    }
}

impl<H: SmtHandler + ?Sized> SmtAppendTokens for SmtTerm<'_, H>
where
    H::Sort: SmtAppendTokens,
    H::Term: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        match self {
            Self::SpecialConstant(constant) => append_special_constant(*constant, tokens),
            Self::QualifiedIdent(ident) => ident.append_tokens(tokens),
            Self::Application(application) => application.append_tokens(tokens),
        }
    }
}

impl<H: SmtHandler + ?Sized> SmtAppendTokens for SmtAttributeValue<'_, H>
where
    H::SExpr: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        match self {
            Self::SpecialConstant(constant) => append_special_constant(*constant, tokens),
            Self::Symbol(symbol) => tokens.push(SmtToken::Symbol(*symbol)),
            Self::SExprs(s_exprs) => {
                // the S-expressions are enclosed in parentheses: ( s_expr* )
                tokens.push(SmtToken::ParenOpen);
                s_exprs.append_tokens(tokens);
                tokens.push(SmtToken::ParenClose);
            }
        }
    }
}

impl<H: SmtHandler + ?Sized> SmtAppendTokens for SmtSExpr<'_, H>
where
    H::SExpr: SmtAppendTokens,
{
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        match self {
            Self::SpecialConstant(constant) => append_special_constant(*constant, tokens),
            Self::Symbol(symbol) => tokens.push(SmtToken::Symbol(*symbol)),
            Self::Reserved(reserved) => tokens.push(SmtToken::Reserved(*reserved)),
            Self::Keyword(keyword) => tokens.push(SmtToken::Keyword(*keyword)),
            Self::SExprs(s_exprs) => {
                // the S-expressions are enclosed in parentheses: ( s_expr* )
                tokens.push(SmtToken::ParenOpen);
                s_exprs.append_tokens(tokens);
                tokens.push(SmtToken::ParenClose);
            }
        }
    }
}

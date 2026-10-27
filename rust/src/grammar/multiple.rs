use std::{
    fmt::Debug,
    iter::FusedIterator,
    ops::{Index, IndexMut},
    slice, vec,
};

use crate::{
    SmtHandler,
    grammar::SmtPattern,
    lexicon::{SmtNumeral, SmtSymbol},
    parser::{Arena, ArenaAccess, PatternHandleBuf, SimplePatternHandle, SymbolHandle, TextHandle},
    token::{SmtAppendTokens, SmtToken, SmtTokensCursor},
};

/// View of multiple values.
///
/// The values can be inspected and modified in place, and [IntoIterator]
/// moves them out in order.
pub struct SmtMultiple<'a, T> {
    stack: &'a mut Vec<T>,
    start: usize,
}

impl<'a, T> SmtMultiple<'a, T> {
    #[inline]
    pub fn new(stack: &'a mut Vec<T>) -> Self {
        Self { stack, start: 0 }
    }

    /// Hands over the values of `stack` above `start`.
    ///
    /// The values may or may not be removed from the vector.
    /// The caller must ensure that the vector is truncated
    /// after the handling returns.
    #[inline]
    pub(crate) fn new_starting(stack: &'a mut Vec<T>, start: usize) -> Self {
        debug_assert!(
            start <= stack.len(),
            "start of multiple values must not exceed stack length"
        );
        Self { stack, start }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.stack.len() - self.start
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn as_slice(&self) -> &[T] {
        &self.stack[self.start..]
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.stack[self.start..]
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.as_slice().get(index)
    }

    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.as_mut_slice().get_mut(index)
    }

    #[inline]
    pub fn iter(&self) -> slice::Iter<'_, T> {
        self.as_slice().iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> slice::IterMut<'_, T> {
        self.as_mut_slice().iter_mut()
    }
}

impl<T> Index<usize> for SmtMultiple<'_, T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &T {
        &self.as_slice()[index]
    }
}

impl<T> IndexMut<usize> for SmtMultiple<'_, T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut T {
        &mut self.as_mut_slice()[index]
    }
}

impl<'a, T> IntoIterator for SmtMultiple<'a, T> {
    type Item = T;
    type IntoIter = SmtMultipleIntoIter<'a, T>;

    /// Moves the values out in order.
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        SmtMultipleIntoIter(self.stack.drain(self.start..))
    }
}

/// Iterator that moves multiple values out in order.
pub struct SmtMultipleIntoIter<'a, T>(vec::Drain<'a, T>);

impl<T> Iterator for SmtMultipleIntoIter<'_, T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.0.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<T> ExactSizeIterator for SmtMultipleIntoIter<'_, T> {}

impl<T> FusedIterator for SmtMultipleIntoIter<'_, T> {}

impl<T: Debug> Debug for SmtMultipleIntoIter<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("SmtMultipleIntoIter")
            .field(&self.0.as_slice())
            .finish()
    }
}

impl<'b, T> IntoIterator for &'b SmtMultiple<'_, T> {
    type Item = &'b T;
    type IntoIter = slice::Iter<'b, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'b, T> IntoIterator for &'b mut SmtMultiple<'_, T> {
    type Item = &'b mut T;
    type IntoIter = slice::IterMut<'b, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: Debug> Debug for SmtMultiple<'_, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// View of named values.
///
/// Each value is named by a symbol, such as in let bindings or sorted variables.
///
/// The values can be inspected and modified in place, and [IntoIterator]
/// moves them out in order.
pub struct SmtNamedValues<'a, V> {
    text: &'a [u8],
    names: SmtMultiple<'a, SymbolHandle>,
    values: SmtMultiple<'a, V>,
}

/// View of let bindings.
///
/// It holds the names with their terms.
pub type SmtBindings<'a, T> = SmtNamedValues<'a, T>;

/// View of sorted variables.
///
/// It holds the names with their sorts.
pub type SmtSortedVars<'a, S> = SmtNamedValues<'a, S>;

impl<'a, V> SmtNamedValues<'a, V> {
    pub(crate) fn new(
        text: &'a [u8],
        names: SmtMultiple<'a, SymbolHandle>,
        values: SmtMultiple<'a, V>,
    ) -> Self {
        debug_assert!(
            names.len() == values.len(),
            "names and values must be aligned"
        );
        Self {
            text,
            names,
            values,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<(SmtSymbol<'a>, &V)> {
        let name = self.names.get(index)?.symbol_view(self.text);
        Some((name, &self.values[index]))
    }

    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<(SmtSymbol<'a>, &mut V)> {
        let name = self.names.get(index)?.symbol_view(self.text);
        Some((name, &mut self.values[index]))
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = (SmtSymbol<'a>, &V)> {
        let text = self.text;
        self.names
            .iter()
            .map(move |name| name.symbol_view(text))
            .zip(self.values.iter())
    }

    pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (SmtSymbol<'a>, &mut V)> {
        let text = self.text;
        self.names
            .iter()
            .map(move |name| name.symbol_view(text))
            .zip(self.values.iter_mut())
    }
}

impl<'a, V> IntoIterator for SmtNamedValues<'a, V> {
    type Item = (SmtSymbol<'a>, V);
    type IntoIter = SmtNamedValuesIntoIter<'a, V>;

    fn into_iter(self) -> Self::IntoIter {
        SmtNamedValuesIntoIter {
            text: self.text,
            names: self.names.into_iter(),
            values: self.values.into_iter(),
        }
    }
}

/// Iterator that moves named values out in order.
pub struct SmtNamedValuesIntoIter<'a, V> {
    text: &'a [u8],
    names: SmtMultipleIntoIter<'a, SymbolHandle>,
    values: SmtMultipleIntoIter<'a, V>,
}

impl<'a, V> Iterator for SmtNamedValuesIntoIter<'a, V> {
    type Item = (SmtSymbol<'a>, V);

    fn next(&mut self) -> Option<Self::Item> {
        let name = self.names.next()?.symbol_view(self.text);
        let value = self.values.next()?;
        Some((name, value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.values.size_hint()
    }
}

impl<V> ExactSizeIterator for SmtNamedValuesIntoIter<'_, V> {}

impl<V: Debug> Debug for SmtNamedValuesIntoIter<'_, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let text = self.text;
        let remaining: Vec<_> = self
            .names
            .0
            .as_slice()
            .iter()
            .map(|name| name.symbol_view(text))
            .zip(self.values.0.as_slice())
            .collect();
        f.debug_tuple("SmtNamedValuesIntoIter")
            .field(&remaining)
            .finish()
    }
}

impl<V: Debug> Debug for SmtNamedValues<'_, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Owned named values.
///
/// Each value is named by a symbol, such as in let bindings or sorted variables.
#[derive(Clone)]
pub struct SmtNamedValuesBuf<V> {
    text: Vec<u8>,
    names: Vec<SymbolHandle>,
    values: Vec<V>,
}

impl<V> SmtNamedValuesBuf<V> {
    pub fn new() -> Self {
        Self {
            text: Vec::new(),
            names: Vec::new(),
            values: Vec::new(),
        }
    }

    pub fn push(&mut self, name: SmtSymbol, value: V) {
        let name = SymbolHandle::create_by_push(&mut self.text, name);
        self.names.push(name);
        self.values.push(value);
    }

    pub fn clear(&mut self) {
        self.text.clear();
        self.names.clear();
        self.values.clear();
    }

    pub fn view_mut(&mut self) -> SmtNamedValues<'_, V> {
        SmtNamedValues::new(
            &self.text,
            SmtMultiple::new(&mut self.names),
            SmtMultiple::new(&mut self.values),
        )
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The names with their values, read in place.
    pub(crate) fn entries(&self) -> impl Iterator<Item = (SmtSymbol<'_>, &V)> {
        let text = &self.text;
        self.names
            .iter()
            .map(move |name| name.symbol_view(text))
            .zip(self.values.iter())
    }
}

impl<V> Default for SmtNamedValuesBuf<V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<V: Debug> Debug for SmtNamedValuesBuf<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.entries()).finish()
    }
}

/// View of match cases.
pub struct SmtMatchCases<'a, H: SmtHandler + ?Sized> {
    text: &'a [u8],
    simple_patterns: &'a [SimplePatternHandle],
    patterns: SmtMultiple<'a, PatternHandleBuf>,
    terms: SmtMultiple<'a, H::Term>,
}

impl<'a, H: SmtHandler + ?Sized> SmtMatchCases<'a, H> {
    pub(crate) fn new(
        _access: ArenaAccess,
        text: &'a [u8],
        simple_patterns: &'a [SimplePatternHandle],
        patterns: SmtMultiple<'a, PatternHandleBuf>,
        terms: SmtMultiple<'a, H::Term>,
    ) -> Self {
        debug_assert!(
            patterns.len() == terms.len(),
            "match term patterns and terms must be aligned"
        );
        Self {
            text,
            simple_patterns,
            patterns,
            terms,
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.terms.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<(SmtPattern<'a>, &H::Term)> {
        let pattern =
            Arena::<H>::pattern_view(self.text, self.simple_patterns, self.patterns.get(index)?);
        Some((pattern, &self.terms[index]))
    }

    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<(SmtPattern<'a>, &mut H::Term)> {
        let pattern =
            Arena::<H>::pattern_view(self.text, self.simple_patterns, self.patterns.get(index)?);
        Some((pattern, &mut self.terms[index]))
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = (SmtPattern<'a>, &H::Term)> {
        self.patterns
            .iter()
            .map(|pattern| Arena::<H>::pattern_view(self.text, self.simple_patterns, pattern))
            .zip(self.terms.iter())
    }

    pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (SmtPattern<'a>, &mut H::Term)> {
        self.patterns
            .iter()
            .map(|pattern| Arena::<H>::pattern_view(self.text, self.simple_patterns, pattern))
            .zip(self.terms.iter_mut())
    }
}

/// Iterator that moves match cases out in order.
pub struct SmtMatchCasesIntoIter<'a, H: SmtHandler + ?Sized> {
    text: &'a [u8],
    simple_patterns: &'a [SimplePatternHandle],
    patterns: SmtMultipleIntoIter<'a, PatternHandleBuf>,
    terms: SmtMultipleIntoIter<'a, H::Term>,
}

impl<'a, H: SmtHandler + ?Sized> Iterator for SmtMatchCasesIntoIter<'a, H> {
    type Item = (SmtPattern<'a>, H::Term);

    fn next(&mut self) -> Option<Self::Item> {
        let pattern =
            Arena::<H>::pattern_view(self.text, self.simple_patterns, &self.patterns.next()?);
        let term = self.terms.next()?;
        Some((pattern, term))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.terms.size_hint()
    }
}

impl<H: SmtHandler + ?Sized> ExactSizeIterator for SmtMatchCasesIntoIter<'_, H> {}

impl<H: SmtHandler + ?Sized> Debug for SmtMatchCasesIntoIter<'_, H>
where
    H::Term: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let remaining: Vec<_> = self
            .patterns
            .0
            .as_slice()
            .iter()
            .map(|pattern| Arena::<H>::pattern_view(self.text, self.simple_patterns, pattern))
            .zip(self.terms.0.as_slice())
            .collect();
        f.debug_tuple("SmtMatchCasesIntoIter")
            .field(&remaining)
            .finish()
    }
}

impl<H: SmtHandler + ?Sized> Debug for SmtMatchCases<'_, H>
where
    H::Term: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<'a, H: SmtHandler + ?Sized> IntoIterator for SmtMatchCases<'a, H> {
    type Item = (SmtPattern<'a>, H::Term);
    type IntoIter = SmtMatchCasesIntoIter<'a, H>;

    fn into_iter(self) -> Self::IntoIter {
        SmtMatchCasesIntoIter {
            text: self.text,
            simple_patterns: self.simple_patterns,
            patterns: self.patterns.into_iter(),
            terms: self.terms.into_iter(),
        }
    }
}

/// Owned match cases.
pub struct SmtMatchCasesBuf<H: SmtHandler + ?Sized> {
    text: Vec<u8>,
    simple_patterns: Vec<SimplePatternHandle>,
    patterns: Vec<PatternHandleBuf>,
    terms: Vec<H::Term>,
}

impl<H: SmtHandler + ?Sized> SmtMatchCasesBuf<H> {
    pub fn new() -> Self {
        Self {
            text: Vec::new(),
            simple_patterns: Vec::new(),
            patterns: Vec::new(),
            terms: Vec::new(),
        }
    }

    pub fn push(&mut self, pattern: SmtPattern, term: H::Term) {
        let pattern = match pattern {
            SmtPattern::Simple(simple) => PatternHandleBuf::Simple(
                SimplePatternHandle::create_by_push(&mut self.text, simple),
            ),
            SmtPattern::Application(application) => {
                let constructor =
                    SymbolHandle::create_by_push(&mut self.text, application.constructor());
                let args_start = self.simple_patterns.len();
                for arg in application.args().iter() {
                    let arg = SimplePatternHandle::create_by_push(&mut self.text, arg);
                    self.simple_patterns.push(arg);
                }
                PatternHandleBuf::Application {
                    constructor,
                    args_start,
                    args_end: self.simple_patterns.len(),
                }
            }
        };
        self.patterns.push(pattern);
        self.terms.push(term);
    }

    pub fn clear(&mut self) {
        self.text.clear();
        self.simple_patterns.clear();
        self.patterns.clear();
        self.terms.clear();
    }

    pub fn view_mut(&mut self) -> SmtMatchCases<'_, H> {
        SmtMatchCases {
            text: &self.text,
            simple_patterns: &self.simple_patterns,
            patterns: SmtMultiple::new(&mut self.patterns),
            terms: SmtMultiple::new(&mut self.terms),
        }
    }

    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn is_empty(&self) -> bool {
        self.terms.is_empty()
    }
}

impl<H: SmtHandler + ?Sized> Default for SmtMatchCasesBuf<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler + ?Sized> Clone for SmtMatchCasesBuf<H>
where
    H::Term: Clone,
{
    fn clone(&self) -> Self {
        Self {
            text: self.text.clone(),
            simple_patterns: self.simple_patterns.clone(),
            patterns: self.patterns.clone(),
            terms: self.terms.clone(),
        }
    }
}

impl<H: SmtHandler + ?Sized> Debug for SmtMatchCasesBuf<H>
where
    H::Term: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let cases = self
            .patterns
            .iter()
            .map(|pattern| Arena::<H>::pattern_view(&self.text, &self.simple_patterns, pattern))
            .zip(self.terms.iter());
        f.debug_list().entries(cases).finish()
    }
}

/// View of symbols.
///
/// For example, the parameters of a sort definition.
#[derive(Clone, Copy)]
pub struct SmtSymbols<'a> {
    text: &'a [u8],
    names: &'a [SymbolHandle],
}

impl<'a> SmtSymbols<'a> {
    #[inline]
    pub fn len(&self) -> usize {
        self.names.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<SmtSymbol<'a>> {
        Some(self.names.get(index)?.symbol_view(self.text))
    }

    pub fn iter(&self) -> SmtSymbolsIter<'a> {
        SmtSymbolsIter {
            text: self.text,
            names: self.names.iter(),
        }
    }
}

impl<'a> IntoIterator for SmtSymbols<'a> {
    type Item = SmtSymbol<'a>;
    type IntoIter = SmtSymbolsIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Iterator over symbols.
pub struct SmtSymbolsIter<'a> {
    text: &'a [u8],
    names: slice::Iter<'a, SymbolHandle>,
}

impl<'a> Iterator for SmtSymbolsIter<'a> {
    type Item = SmtSymbol<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.names.next()?.symbol_view(self.text))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.names.size_hint()
    }
}

impl ExactSizeIterator for SmtSymbolsIter<'_> {}

impl Debug for SmtSymbolsIter<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let text = self.text;
        let remaining: Vec<_> = self
            .names
            .as_slice()
            .iter()
            .map(|name| name.symbol_view(text))
            .collect();
        f.debug_tuple("SmtSymbolsIter").field(&remaining).finish()
    }
}

impl Debug for SmtSymbols<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Owned symbols.
///
/// For example, the parameters of a sort definition.
#[derive(Clone)]
pub struct SmtSymbolsBuf {
    text: Vec<u8>,
    names: Vec<SymbolHandle>,
}

impl SmtSymbolsBuf {
    pub fn new() -> Self {
        Self {
            text: Vec::new(),
            names: Vec::new(),
        }
    }

    pub fn push(&mut self, name: SmtSymbol) {
        let name = SymbolHandle::create_by_push(&mut self.text, name);
        self.names.push(name);
    }

    pub fn clear(&mut self) {
        self.text.clear();
        self.names.clear();
    }

    pub fn view(&self) -> SmtSymbols<'_> {
        SmtSymbols {
            text: &self.text,
            names: &self.names,
        }
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

impl Default for SmtSymbolsBuf {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for SmtSymbolsBuf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.view(), f)
    }
}

/// View of a function signature.
///
/// It holds the name, the parameters with their sorts, and the result sort.
///
/// The sorts are handed over by reference.
pub struct SmtFunctionSignature<'a, S> {
    text: &'a [u8],
    name: SymbolHandle,
    param_names: &'a [SymbolHandle],
    param_sorts: &'a [S],
    result_sort: &'a S,
}

impl<S> Clone for SmtFunctionSignature<'_, S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<S> Copy for SmtFunctionSignature<'_, S> {}

impl<'a, S> SmtFunctionSignature<'a, S> {
    #[inline]
    pub fn name(&self) -> SmtSymbol<'a> {
        self.name.symbol_view(self.text)
    }

    /// The parameters with their sorts, in order.
    pub fn params(&self) -> impl ExactSizeIterator<Item = (SmtSymbol<'a>, &'a S)> + use<'a, S> {
        let text = self.text;
        self.param_names
            .iter()
            .map(move |name| name.symbol_view(text))
            .zip(self.param_sorts.iter())
    }

    #[inline]
    pub fn result_sort(&self) -> &'a S {
        self.result_sort
    }
}

impl<S: Debug> Debug for SmtFunctionSignature<'_, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SmtFunctionSignature")
            .field("name", &self.name())
            .field("params", &self.params().collect::<Vec<_>>())
            .field("result_sort", self.result_sort)
            .finish()
    }
}

/// View of function signatures.
///
/// For example, those of `define-funs-rec`.
///
/// The sorts are handed over by reference.
pub struct SmtFunctionSignatures<'a, S> {
    buf: &'a SmtFunctionSignaturesBuf<S>,
}

impl<S> Clone for SmtFunctionSignatures<'_, S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<S> Copy for SmtFunctionSignatures<'_, S> {}

impl<'a, S> SmtFunctionSignatures<'a, S> {
    #[inline]
    pub fn len(&self) -> usize {
        self.buf.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.buf.is_empty()
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<SmtFunctionSignature<'a, S>> {
        self.buf.get(index)
    }

    pub fn iter(&self) -> SmtFunctionSignaturesIter<'a, S> {
        SmtFunctionSignaturesIter {
            buf: self.buf,
            next: 0,
        }
    }
}

impl<'a, S> IntoIterator for SmtFunctionSignatures<'a, S> {
    type Item = SmtFunctionSignature<'a, S>;
    type IntoIter = SmtFunctionSignaturesIter<'a, S>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Iterator over function signatures.
pub struct SmtFunctionSignaturesIter<'a, S> {
    buf: &'a SmtFunctionSignaturesBuf<S>,
    next: usize,
}

impl<'a, S> Iterator for SmtFunctionSignaturesIter<'a, S> {
    type Item = SmtFunctionSignature<'a, S>;

    fn next(&mut self) -> Option<Self::Item> {
        let signature = self.buf.get(self.next)?;
        self.next += 1;
        Some(signature)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.buf.len() - self.next;
        (remaining, Some(remaining))
    }
}

impl<S> ExactSizeIterator for SmtFunctionSignaturesIter<'_, S> {}

impl<S: Debug> Debug for SmtFunctionSignaturesIter<'_, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let remaining: Vec<_> = (self.next..self.buf.len())
            .filter_map(|index| self.buf.get(index))
            .collect();
        f.debug_tuple("SmtFunctionSignaturesIter")
            .field(&remaining)
            .finish()
    }
}

impl<S: Debug> Debug for SmtFunctionSignatures<'_, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Owned function signatures.
///
/// For example, those of `define-funs-rec`.
#[derive(Clone)]
pub struct SmtFunctionSignaturesBuf<S> {
    text: Vec<u8>,
    names: Vec<SymbolHandle>,
    result_sorts: Vec<S>,
    /// Where the parameters of each signature start.
    param_starts: Vec<usize>,
    param_names: Vec<SymbolHandle>,
    param_sorts: Vec<S>,
}

impl<S> SmtFunctionSignaturesBuf<S> {
    pub fn new() -> Self {
        Self {
            text: Vec::new(),
            names: Vec::new(),
            result_sorts: Vec::new(),
            param_starts: Vec::new(),
            param_names: Vec::new(),
            param_sorts: Vec::new(),
        }
    }

    /// Starts a signature with no parameters; [Self::push_param] adds them.
    pub fn push(&mut self, name: SmtSymbol, result_sort: S) {
        let name = SymbolHandle::create_by_push(&mut self.text, name);
        self.names.push(name);
        self.result_sorts.push(result_sort);
        self.param_starts.push(self.param_names.len());
    }

    /// Adds a parameter to the last signature pushed.
    pub fn push_param(&mut self, name: SmtSymbol, sort: S) {
        assert!(
            !self.names.is_empty(),
            "a parameter must be pushed after its signature"
        );
        let name = SymbolHandle::create_by_push(&mut self.text, name);
        self.param_names.push(name);
        self.param_sorts.push(sort);
    }

    pub fn clear(&mut self) {
        self.text.clear();
        self.names.clear();
        self.result_sorts.clear();
        self.param_starts.clear();
        self.param_names.clear();
        self.param_sorts.clear();
    }

    pub fn view(&self) -> SmtFunctionSignatures<'_, S> {
        SmtFunctionSignatures { buf: self }
    }

    pub fn get(&self, index: usize) -> Option<SmtFunctionSignature<'_, S>> {
        let name = *self.names.get(index)?;
        let start = self.param_starts[index];
        let end = self
            .param_starts
            .get(index + 1)
            .copied()
            .unwrap_or(self.param_names.len());
        Some(SmtFunctionSignature {
            text: &self.text,
            name,
            param_names: &self.param_names[start..end],
            param_sorts: &self.param_sorts[start..end],
            result_sort: &self.result_sorts[index],
        })
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

impl<S> Default for SmtFunctionSignaturesBuf<S> {
    fn default() -> Self {
        Self::new()
    }
}

impl<S: Debug> Debug for SmtFunctionSignaturesBuf<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.view(), f)
    }
}

/// View of sort names with their arities.
///
/// For example, those declared by `declare-datatypes`.
#[derive(Clone, Copy)]
pub struct SmtSortArities<'a> {
    text: &'a [u8],
    names: &'a [SymbolHandle],
    arities: &'a [TextHandle],
}

impl<'a> SmtSortArities<'a> {
    #[inline]
    pub fn len(&self) -> usize {
        self.names.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<(SmtSymbol<'a>, SmtNumeral<'a>)> {
        let name = self.names.get(index)?.symbol_view(self.text);
        Some((name, self.arities[index].numeral_view(self.text)))
    }

    pub fn iter(&self) -> SmtSortAritiesIter<'a> {
        SmtSortAritiesIter {
            arities: *self,
            next: 0,
        }
    }
}

impl<'a> IntoIterator for SmtSortArities<'a> {
    type Item = (SmtSymbol<'a>, SmtNumeral<'a>);
    type IntoIter = SmtSortAritiesIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// Iterator over sort names with their arities.
pub struct SmtSortAritiesIter<'a> {
    arities: SmtSortArities<'a>,
    next: usize,
}

impl<'a> Iterator for SmtSortAritiesIter<'a> {
    type Item = (SmtSymbol<'a>, SmtNumeral<'a>);

    fn next(&mut self) -> Option<Self::Item> {
        let item = self.arities.get(self.next)?;
        self.next += 1;
        Some(item)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.arities.len() - self.next;
        (remaining, Some(remaining))
    }
}

impl ExactSizeIterator for SmtSortAritiesIter<'_> {}

impl Debug for SmtSortAritiesIter<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let remaining: Vec<_> = (self.next..self.arities.len())
            .filter_map(|index| self.arities.get(index))
            .collect();
        f.debug_tuple("SmtSortAritiesIter")
            .field(&remaining)
            .finish()
    }
}

impl Debug for SmtSortArities<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Owned sort names with their arities.
///
/// For example, those declared by `declare-datatypes`.
#[derive(Clone)]
pub struct SmtSortAritiesBuf {
    text: Vec<u8>,
    names: Vec<SymbolHandle>,
    arities: Vec<TextHandle>,
}

impl SmtSortAritiesBuf {
    pub fn new() -> Self {
        Self {
            text: Vec::new(),
            names: Vec::new(),
            arities: Vec::new(),
        }
    }

    pub fn push(&mut self, name: SmtSymbol, arity: SmtNumeral) {
        let name = SymbolHandle::create_by_push(&mut self.text, name);
        let start = self.text.len();
        self.text.extend_from_slice(arity.as_slice());
        self.names.push(name);
        self.arities.push(TextHandle {
            start,
            len: self.text.len() - start,
        });
    }

    pub fn clear(&mut self) {
        self.text.clear();
        self.names.clear();
        self.arities.clear();
    }

    pub fn view(&self) -> SmtSortArities<'_> {
        SmtSortArities {
            text: &self.text,
            names: &self.names,
            arities: &self.arities,
        }
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

impl Default for SmtSortAritiesBuf {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for SmtSortAritiesBuf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.view(), f)
    }
}

/// View of datatype constructors.
///
/// Each constructor has a name and selectors, the selectors as sorted variables.
///
/// [IntoIterator] hands over each constructor with its selectors,
/// whose sorts can be moved out.
pub struct SmtConstructors<'a, S> {
    text: &'a [u8],
    names: &'a [SymbolHandle],
    selectors: &'a mut [SmtNamedValuesBuf<S>],
}

impl<'a, S> SmtConstructors<'a, S> {
    #[inline]
    pub fn len(&self) -> usize {
        self.names.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }

    /// The constructors with their selectors, which can be modified in place.
    pub fn iter_mut(&mut self) -> SmtConstructorsIter<'_, S> {
        SmtConstructorsIter {
            text: self.text,
            names: self.names.iter(),
            selectors: self.selectors.iter_mut(),
        }
    }
}

impl<'a, S> IntoIterator for SmtConstructors<'a, S> {
    type Item = (SmtSymbol<'a>, SmtNamedValues<'a, S>);
    type IntoIter = SmtConstructorsIter<'a, S>;

    fn into_iter(self) -> Self::IntoIter {
        SmtConstructorsIter {
            text: self.text,
            names: self.names.iter(),
            selectors: self.selectors.iter_mut(),
        }
    }
}

/// Iterator over datatype constructors with their selectors.
pub struct SmtConstructorsIter<'a, S> {
    text: &'a [u8],
    names: slice::Iter<'a, SymbolHandle>,
    selectors: slice::IterMut<'a, SmtNamedValuesBuf<S>>,
}

impl<'a, S> Iterator for SmtConstructorsIter<'a, S> {
    type Item = (SmtSymbol<'a>, SmtNamedValues<'a, S>);

    fn next(&mut self) -> Option<Self::Item> {
        let name = self.names.next()?.symbol_view(self.text);
        let selectors = self.selectors.next()?.view_mut();
        Some((name, selectors))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.names.size_hint()
    }
}

impl<S> ExactSizeIterator for SmtConstructorsIter<'_, S> {}

impl<S: Debug> Debug for SmtConstructorsIter<'_, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let text = self.text;
        let remaining: Vec<_> = self
            .names
            .as_slice()
            .iter()
            .zip(self.selectors.as_slice())
            .map(|(name, selectors)| {
                let selectors: Vec<_> = selectors.entries().collect();
                (name.symbol_view(text), selectors)
            })
            .collect();
        f.debug_tuple("SmtConstructorsIter")
            .field(&remaining)
            .finish()
    }
}

impl<S: Debug> Debug for SmtConstructors<'_, S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();
        for (name, selectors) in self.names.iter().zip(self.selectors.iter()) {
            let selectors: Vec<_> = selectors.entries().collect();
            list.entry(&(name.symbol_view(self.text), selectors));
        }
        list.finish()
    }
}

/// Owned datatype constructors.
///
/// Each constructor has a name and selectors, the selectors as sorted variables.
///
/// Each constructor's selectors are kept in storage of their own,
/// which is reused when the constructors are cleared.
#[derive(Clone)]
pub struct SmtConstructorsBuf<S> {
    text: Vec<u8>,
    names: Vec<SymbolHandle>,
    /// Selector storage, the first `names.len()` in use.
    selectors: Vec<SmtNamedValuesBuf<S>>,
}

impl<S> SmtConstructorsBuf<S> {
    pub fn new() -> Self {
        Self {
            text: Vec::new(),
            names: Vec::new(),
            selectors: Vec::new(),
        }
    }

    /// Starts a constructor with no selectors; [Self::push_selector] adds them.
    pub fn push(&mut self, name: SmtSymbol) {
        let index = self.names.len();
        let name = SymbolHandle::create_by_push(&mut self.text, name);
        self.names.push(name);
        if index == self.selectors.len() {
            self.selectors.push(SmtNamedValuesBuf::new());
        }
    }

    /// Adds a selector to the last constructor pushed.
    pub fn push_selector(&mut self, name: SmtSymbol, sort: S) {
        let index = self
            .names
            .len()
            .checked_sub(1)
            .expect("a selector must be pushed after its constructor");
        self.selectors[index].push(name, sort);
    }

    pub fn clear(&mut self) {
        for selectors in &mut self.selectors[..self.names.len()] {
            selectors.clear();
        }
        self.text.clear();
        self.names.clear();
    }

    pub fn view_mut(&mut self) -> SmtConstructors<'_, S> {
        let len = self.names.len();
        SmtConstructors {
            text: &self.text,
            names: &self.names,
            selectors: &mut self.selectors[..len],
        }
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

impl<S> Default for SmtConstructorsBuf<S> {
    fn default() -> Self {
        Self::new()
    }
}

impl<S: Debug> Debug for SmtConstructorsBuf<S> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut list = f.debug_list();
        for (name, selectors) in self.names.iter().zip(self.selectors.iter()) {
            let selectors: Vec<_> = selectors.entries().collect();
            list.entry(&(name.symbol_view(&self.text), selectors));
        }
        list.finish()
    }
}

/// Appends the values in order, without enclosing parentheses.
impl<T: SmtAppendTokens> SmtAppendTokens for SmtMultiple<'_, T> {
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        for value in self.iter() {
            value.append_tokens(tokens);
        }
    }
}

/// Appends each named value as ( name value ).
fn append_named<'a, V: SmtAppendTokens + 'a>(
    named: impl Iterator<Item = (SmtSymbol<'a>, &'a V)>,
    tokens: &mut SmtTokensCursor<'a>,
) {
    for (name, value) in named {
        tokens.push(SmtToken::ParenOpen);
        tokens.push(SmtToken::Symbol(name));
        value.append_tokens(tokens);
        tokens.push(SmtToken::ParenClose);
    }
}

/// Appends each name with its value as `(name value)`, in order, without
/// enclosing parentheses.
impl<V: SmtAppendTokens> SmtAppendTokens for SmtNamedValues<'_, V> {
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        append_named(self.iter(), tokens);
    }
}

/// Appends each name with its value as `(name value)`, in order, without
/// enclosing parentheses.
impl<V: SmtAppendTokens> SmtAppendTokens for SmtNamedValuesBuf<V> {
    fn append_tokens<'a>(&'a self, tokens: &mut SmtTokensCursor<'a>) {
        let text = self.text.as_slice();
        let names = self.names.iter().map(|name| name.symbol_view(text));
        append_named(names.zip(self.values.iter()), tokens);
    }
}

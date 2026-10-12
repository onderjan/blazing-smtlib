use std::{
    fmt::Debug,
    iter::FusedIterator,
    ops::{Index, IndexMut},
    slice, vec,
};

use crate::{
    SmtHandler, SmtPattern, SmtSymbol,
    parser::{Arena, ArenaAccess, PatternHandleBuf, SimplePatternHandle, SymbolHandle},
};

/// Multiple values to be handled.
///
/// The values can be inspected and modified in place, and [`IntoIterator`]
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

/// Iterator over multiple values.
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

/// Named values to be handled: each a symbol with a value,
/// such as let bindings or sorted variables.
///
/// The values can be inspected and modified in place, and [`IntoIterator`]
/// moves them out in order.
pub struct SmtNamed<'a, V> {
    text: &'a [u8],
    names: SmtMultiple<'a, SymbolHandle>,
    values: SmtMultiple<'a, V>,
}

/// Let bindings to be handled: the names with their terms.
pub type SmtBindings<'a, T> = SmtNamed<'a, T>;

/// Sorted variables to be handled: the names with their sorts.
pub type SmtSortedVars<'a, S> = SmtNamed<'a, S>;

impl<'a, V> SmtNamed<'a, V> {
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

impl<'a, V> IntoIterator for SmtNamed<'a, V> {
    type Item = (SmtSymbol<'a>, V);
    type IntoIter = SmtNamedIntoIter<'a, V>;

    fn into_iter(self) -> Self::IntoIter {
        SmtNamedIntoIter {
            text: self.text,
            names: self.names.into_iter(),
            values: self.values.into_iter(),
        }
    }
}

/// Iterator moving named values out in order.
pub struct SmtNamedIntoIter<'a, V> {
    text: &'a [u8],
    names: SmtMultipleIntoIter<'a, SymbolHandle>,
    values: SmtMultipleIntoIter<'a, V>,
}

impl<'a, V> Iterator for SmtNamedIntoIter<'a, V> {
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

impl<V> ExactSizeIterator for SmtNamedIntoIter<'_, V> {}

impl<V: Debug> Debug for SmtNamed<'_, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// Owned named values, from which [`SmtNamed`] is viewed.
pub struct SmtNamedBuf<V> {
    text: Vec<u8>,
    names: Vec<SymbolHandle>,
    values: Vec<V>,
}

/// Owned let bindings.
pub type SmtBindingsBuf<T> = SmtNamedBuf<T>;

/// Owned sorted variables.
pub type SmtSortedVarsBuf<S> = SmtNamedBuf<S>;

impl<V> SmtNamedBuf<V> {
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

    pub fn view(&mut self) -> SmtNamed<'_, V> {
        SmtNamed::new(
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
}

impl<V> Default for SmtNamedBuf<V> {
    fn default() -> Self {
        Self::new()
    }
}

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

/// Iterator over let bindings.
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

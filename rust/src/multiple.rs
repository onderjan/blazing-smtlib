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

pub struct SmtSortedVars<'a, H: SmtHandler + ?Sized> {
    text: &'a [u8],
    names: SmtMultiple<'a, SymbolHandle>,
    sorts: SmtMultiple<'a, H::Sort>,
}

impl<'a, H: SmtHandler + ?Sized> SmtSortedVars<'a, H> {
    pub(crate) fn new(
        _access: ArenaAccess,
        text: &'a [u8],
        names: SmtMultiple<'a, SymbolHandle>,
        sorts: SmtMultiple<'a, H::Sort>,
    ) -> Self {
        debug_assert!(
            names.len() == sorts.len(),
            "variable names and sorts must be aligned"
        );
        Self { text, names, sorts }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.sorts.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.sorts.is_empty()
    }

    #[inline]
    pub fn get(&self, index: usize) -> Option<(SmtSymbol<'a>, &H::Sort)> {
        let name = self.names.get(index)?.symbol_view(self.text);
        Some((name, &self.sorts[index]))
    }

    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<(SmtSymbol<'a>, &mut H::Sort)> {
        let name = self.names.get(index)?.symbol_view(self.text);
        Some((name, &mut self.sorts[index]))
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = (SmtSymbol<'a>, &H::Sort)> {
        let text = self.text;
        self.names
            .iter()
            .map(move |name| name.symbol_view(text))
            .zip(self.sorts.iter())
    }

    pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (SmtSymbol<'a>, &mut H::Sort)> {
        let text = self.text;
        self.names
            .iter()
            .map(move |name| name.symbol_view(text))
            .zip(self.sorts.iter_mut())
    }
}

pub struct SmtSortedVarsBuf<S> {
    text: Vec<u8>,
    names: Vec<SymbolHandle>,
    sorts: Vec<S>,
}

impl<S> SmtSortedVarsBuf<S> {
    pub fn new() -> Self {
        Self {
            text: Vec::new(),
            names: Vec::new(),
            sorts: Vec::new(),
        }
    }

    pub fn push(&mut self, name: SmtSymbol, sort: S) {
        let name = SymbolHandle::create_by_push(&mut self.text, name);
        self.names.push(name);
        self.sorts.push(sort);
    }

    pub fn clear(&mut self) {
        self.text.clear();
        self.names.clear();
        self.sorts.clear();
    }

    pub fn view<H: SmtHandler<Sort = S>>(&mut self) -> SmtSortedVars<'_, H> {
        SmtSortedVars {
            text: &self.text,
            names: SmtMultiple::new(&mut self.names),
            sorts: SmtMultiple::new(&mut self.sorts),
        }
    }

    pub fn len(&self) -> usize {
        self.sorts.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<S> Default for SmtSortedVarsBuf<S> {
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

/// Let bindings to be handled.
///
/// The values can be inspected and modified in place, and [`IntoIterator`]
/// moves them out in order.
pub struct SmtBindings<'a, H: SmtHandler + ?Sized> {
    text: &'a [u8],
    names: SmtMultiple<'a, SymbolHandle>,
    terms: SmtMultiple<'a, H::Term>,
}

impl<'a, H: SmtHandler + ?Sized> SmtBindings<'a, H> {
    pub(crate) fn new(
        _access: ArenaAccess,
        text: &'a [u8],
        names: SmtMultiple<'a, SymbolHandle>,
        terms: SmtMultiple<'a, H::Term>,
    ) -> Self {
        debug_assert!(
            names.len() == terms.len(),
            "binding names and terms must be aligned"
        );
        Self { text, names, terms }
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
    pub fn get(&self, index: usize) -> Option<(SmtSymbol<'a>, &H::Term)> {
        let name = self.names.get(index)?.symbol_view(self.text);
        Some((name, &self.terms[index]))
    }

    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<(SmtSymbol<'a>, &mut H::Term)> {
        let name = self.names.get(index)?.symbol_view(self.text);
        Some((name, &mut self.terms[index]))
    }

    pub fn iter(&self) -> impl ExactSizeIterator<Item = (SmtSymbol<'a>, &H::Term)> {
        let text = self.text;
        self.names
            .iter()
            .map(move |name| name.symbol_view(text))
            .zip(self.terms.iter())
    }

    pub fn iter_mut(&mut self) -> impl ExactSizeIterator<Item = (SmtSymbol<'a>, &mut H::Term)> {
        let text = self.text;
        self.names
            .iter()
            .map(move |name| name.symbol_view(text))
            .zip(self.terms.iter_mut())
    }
}

impl<'a, H: SmtHandler + ?Sized> IntoIterator for SmtBindings<'a, H> {
    type Item = (SmtSymbol<'a>, H::Term);
    type IntoIter = SmtBindingsIntoIter<'a, H>;

    fn into_iter(self) -> Self::IntoIter {
        SmtBindingsIntoIter {
            text: self.text,
            names: self.names.into_iter(),
            terms: self.terms.into_iter(),
        }
    }
}

/// Iterator over let bindings.
pub struct SmtBindingsIntoIter<'a, H: SmtHandler + ?Sized> {
    text: &'a [u8],
    names: SmtMultipleIntoIter<'a, SymbolHandle>,
    terms: SmtMultipleIntoIter<'a, H::Term>,
}

impl<'a, H: SmtHandler + ?Sized> Iterator for SmtBindingsIntoIter<'a, H> {
    type Item = (SmtSymbol<'a>, H::Term);

    fn next(&mut self) -> Option<Self::Item> {
        let name = self.names.next()?.symbol_view(self.text);
        let term = self.terms.next()?;
        Some((name, term))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.terms.size_hint()
    }
}

impl<H: SmtHandler + ?Sized> ExactSizeIterator for SmtBindingsIntoIter<'_, H> {}

impl<H: SmtHandler + ?Sized> Debug for SmtBindings<'_, H>
where
    H::Term: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

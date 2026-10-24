use std::fmt::{Debug, Write};

use crate::{SmtBytes, SmtBytesBuf, lexer::CharClass};

/// SMT-LIB string content.
///
/// May be empty.
/// Must contain only SMT-LIB printable or whitespace bytes.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtStringContentBuf(SmtBytesBuf);

impl SmtStringContentBuf {
    pub fn is_allowed(value: &[u8]) -> bool {
        value
            .iter()
            .copied()
            .all(|c| CharClass::from(c).is_printable_or_whitespace())
    }
}

/// An owned SMT-LIB symbol, quoted or unquoted.
///
/// The symbol carries its bytes and whether it is quoted.
///
/// May be empty if quoted.
/// Must contain only SMT-LIB printable or whitespace bytes
/// except for pipe (|) and backslash (\), with an additional
/// restriction for unquoted symbols: they must contain
/// a nonempty sequence of simple-symbol bytes not starting
/// with a digit.
///
/// Equality and hash are intentionally not implemented:
/// quoted and unquoted symbols refer to the same value semantically,
/// so the value without the quoted flag should be compared in that case,
/// obtained through [`SmtSymbolBuf::bytes`] or [`SmtSymbolBuf::into_bytes_buf`].
#[derive(Clone)]
pub struct SmtSymbolBuf {
    is_quoted: bool,
    value: SmtBytesBuf,
}

impl SmtSymbolBuf {
    pub fn is_unquoted_allowed(value: &[u8]) -> bool {
        !value.is_empty()
            && !value[0].is_ascii_digit()
            && value
                .iter()
                .all(|c| CharClass::from(*c).is_allowed_in_simple_symbol())
    }

    pub fn is_quoted_allowed(value: &[u8]) -> bool {
        value
            .iter()
            .copied()
            .all(|c| CharClass::from(c).is_printable_or_whitespace() && c != b'|' && c != b'\\')
    }

    /// Whether this is a quoted symbol enclosed in pipes, e.g. `|x|`, or a simple symbol, e.g. `x`.
    pub fn is_quoted(&self) -> bool {
        self.is_quoted
    }

    pub fn new_unquoted(value: Vec<u8>) -> Result<Self, SmtDisallowedByteVecError> {
        let value = SmtBytesBuf::from_vec(value);
        if Self::is_unquoted_allowed(value.as_slice()) {
            Ok(Self {
                is_quoted: false,
                value,
            })
        } else {
            Err(SmtDisallowedByteVecError(value))
        }
    }

    pub fn new_quoted(value: Vec<u8>) -> Result<Self, SmtDisallowedByteVecError> {
        let value = SmtBytesBuf::from_vec(value);
        if Self::is_quoted_allowed(value.as_slice()) {
            Ok(Self {
                is_quoted: true,
                value,
            })
        } else {
            Err(SmtDisallowedByteVecError(value))
        }
    }

    pub fn bytes(&self) -> SmtBytes<'_> {
        self.value.view()
    }

    pub fn as_slice(&self) -> &[u8] {
        self.bytes().as_slice()
    }

    pub fn view(&self) -> SmtSymbol<'_> {
        SmtSymbol {
            is_quoted: self.is_quoted,
            value: self.bytes(),
        }
    }
    pub fn into_bytes_buf(self) -> SmtBytesBuf {
        self.value
    }
    pub fn into_vec(self) -> Vec<u8> {
        self.value.into_vec()
    }
    pub fn len(&self) -> usize {
        self.value.len()
    }
    pub fn is_empty(&self) -> bool {
        self.value.is_empty()
    }
    pub fn iter(&self) -> impl Iterator<Item = u8> {
        self.value.iter()
    }
}

impl Debug for SmtSymbolBuf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.view(), f)
    }
}

/// A view of an SMT-LIB symbol, quoted or unquoted.
///
/// The symbol carries its bytes and whether it is quoted.
///
/// May be empty if quoted.
/// Must contain only SMT-LIB printable or whitespace bytes
/// except for pipe (|) and backslash (\), with additional
/// restrictions for unquoted symbols.
///
/// Equality and hash are intentionally not implemented:
/// quoted and unquoted symbols refer to the same value semantically,
/// so the value without the quoted flag should be compared in that case,
/// obtained through [`SmtSymbol::bytes`].
#[derive(Clone, Copy)]
pub struct SmtSymbol<'a> {
    is_quoted: bool,
    value: SmtBytes<'a>,
}

impl<'a> SmtSymbol<'a> {
    pub(crate) fn new_unchecked(is_quoted: bool, value: &'a [u8]) -> Self {
        if is_quoted {
            debug_assert!(
                SmtSymbolBuf::is_quoted_allowed(value),
                "invalid quoted symbol: {:?}",
                value
            );
        } else {
            debug_assert!(
                SmtSymbolBuf::is_unquoted_allowed(value),
                "invalid unquoted symbol: {:?}",
                value
            );
        }
        Self {
            is_quoted,
            value: SmtBytes::new(value),
        }
    }

    pub fn is_quoted(&self) -> bool {
        self.is_quoted
    }

    pub fn bytes(&self) -> SmtBytes<'a> {
        self.value
    }

    pub fn as_slice(&self) -> &'a [u8] {
        self.value.as_slice()
    }

    pub fn into_owned(self) -> SmtSymbolBuf {
        SmtSymbolBuf {
            is_quoted: self.is_quoted,
            value: self.bytes().into_owned(),
        }
    }

    pub fn len(&self) -> usize {
        self.value.len()
    }

    pub fn is_empty(&self) -> bool {
        self.value.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = u8> {
        self.value.iter()
    }
}

impl Debug for SmtSymbol<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_quoted {
            f.write_char('|')?;
            Debug::fmt(&self.value, f)?;
            f.write_char('|')
        } else {
            Debug::fmt(&self.value, f)
        }
    }
}

/// SMT-LIB keyword.
///
/// Cannot be empty.
/// Must contain only SMT-LIB simple-symbol-class bytes.
///
/// A keyword may start with a digit and may spell a reserved word.
/// It is defined in version 2.0 as a colon followed by a non-empty sequence
/// of simple-symbol-class bytes with no further restriction. From version 2.5 on,
/// the standard defines it as a colon followed by a simple symbol, which
/// read literally excludes a leading digit and the reserved words. We consider
/// this unintended and keep the 2.0 rule in every version: the standard's
/// own keyword examples include `:56`, and there is no need to exclude
/// reserved words as the colon already uniquely determines the category.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtKeywordBuf(SmtBytesBuf);

impl SmtKeywordBuf {
    pub fn is_allowed(value: &[u8]) -> bool {
        !value.is_empty()
            && value
                .iter()
                .copied()
                .all(|c| CharClass::from(c).is_allowed_in_simple_symbol())
    }
}

/// SMT-LIB numeral (base 10).
///
/// Cannot be empty.
/// Must contain only digits.
/// Cannot contain any leading zeros except for the constant "0" itself.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtNumeralBuf(SmtBytesBuf);

impl SmtNumeralBuf {
    pub fn is_allowed(value: &[u8]) -> bool {
        if value.is_empty() {
            return false;
        }
        // if the length is not 1, leading zeros must be rejected
        let mut zero_allowed = value.len() == 1;
        for c in value.iter().copied() {
            if !c.is_ascii_digit() {
                return false;
            }
            if !zero_allowed && c == b'0' {
                return false;
            }
            // leading non-zero, allow zeros in next positions
            zero_allowed = true;
        }
        true
    }
}

/// SMT-LIB hexadecimal digits (base 16).
///
/// Cannot be empty.
/// Must contain only digits, lower-case letters a-f or upper-case letters A-F.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtHexDigitsBuf(SmtBytesBuf);

impl SmtHexDigitsBuf {
    pub fn is_allowed(value: &[u8]) -> bool {
        !value.is_empty() && value.iter().all(|c| c.is_ascii_hexdigit())
    }
}

/// SMT-LIB binary digits (base 2).
///
/// Cannot be empty.
/// Must contain only the digits 0, 1.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtBinDigitsBuf(SmtBytesBuf);

impl SmtBinDigitsBuf {
    pub fn is_allowed(value: &[u8]) -> bool {
        !value.is_empty() && value.iter().copied().all(|c| c == b'0' || c == b'1')
    }
}

/// SMT-LIB decimal (a decimal number with whole part, a dot, then a fractional part)
///
/// A dot (the character '.') must be present. It divides the decimal into
/// a whole part (before it) and a fractional part (after it).
///  
/// The whole part follows the same rules as `SmtNumeral`:
/// cannot be empty, must contain only digits, the leading digit must not be zero.
///
/// The fractional part cannot be empty and must contain only digits.
///
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtDecimalBuf(SmtBytesBuf);

impl SmtDecimalBuf {
    pub fn is_allowed(value: &[u8]) -> bool {
        // split by the dot
        let mut dot_iter = value.split(|c| *c == b'.');

        let Some(whole_part) = dot_iter.next() else {
            // nothing present
            return false;
        };
        let Some(fractional_part) = dot_iter.next() else {
            // no dot present
            return false;
        };
        if dot_iter.next().is_some() {
            // multiple dots present
            return false;
        }
        // the whole part must form a numeral
        if !SmtNumeralBuf::is_allowed(whole_part) {
            return false;
        }

        // the fractional part must be a non-empty string of digits
        !fractional_part.is_empty() && fractional_part.iter().all(|c| c.is_ascii_digit())
    }
}

/// SMT-LIB whitespace (one or more whitespace bytes)
///
/// Cannot be empty.
/// Must contain only tabs, line feeds, carriage returns and spaces.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtWhitespaceBuf(SmtBytesBuf);

impl SmtWhitespaceBuf {
    pub fn is_allowed(value: &[u8]) -> bool {
        !value.is_empty()
            && value
                .iter()
                .copied()
                .all(|c| matches!(c, b'\t' | b'\n' | b'\r' | b' '))
    }
}

/// SMT-LIB comment (not including starting semicolon, including ending CR/LF)
///
/// The semicolon that starts the comment is not a part of it.
/// The content may be empty.
/// Only the last byte may be a carriage return (CR) or a line feed (LF).
/// If the comment runs to the end of the input, there is no ending CR/LF.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtCommentBuf(SmtBytesBuf);

impl SmtCommentBuf {
    pub fn is_allowed(value: &[u8]) -> bool {
        if value.is_empty() {
            // empty content is allowed (starting semicolon at the end of input)
            return true;
        };
        // not empty: it may not contain CR/LF except in the last position,
        // no other restrictions
        value[0..value.len() - 1]
            .iter()
            .all(|c| *c != b'\r' && *c != b'\n')
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SmtDisallowedByteVecError(SmtBytesBuf);

impl SmtDisallowedByteVecError {
    pub fn into_vec(self) -> Vec<u8> {
        self.0.into_vec()
    }
}

macro_rules! string8_newtype {
    ($buf:ident, $view:ident) => {
        impl $buf {
            pub fn new(value: Vec<u8>) -> Result<Self, SmtDisallowedByteVecError> {
                let value = SmtBytesBuf::from_vec(value);
                if Self::is_allowed(value.as_slice()) {
                    Ok(Self(value))
                } else {
                    Err(SmtDisallowedByteVecError(value))
                }
            }

            pub fn as_slice(&self) -> &[u8] {
                self.0.as_slice()
            }
            pub fn view(&self) -> $view<'_> {
                $view(self.0.as_slice())
            }
            pub fn into_bytes_buf(self) -> SmtBytesBuf {
                self.0
            }
            pub fn into_vec(self) -> Vec<u8> {
                self.0.into_vec()
            }
            pub fn len(&self) -> usize {
                self.0.len()
            }
            pub fn is_empty(&self) -> bool {
                self.0.is_empty()
            }
            pub fn iter(&self) -> impl Iterator<Item = u8> {
                self.0.iter()
            }
        }

        impl std::fmt::Debug for $buf {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Debug::fmt(&self.0, f)
            }
        }

        impl std::borrow::Borrow<[u8]> for $buf {
            fn borrow(&self) -> &[u8] {
                self.as_slice()
            }
        }

        impl PartialEq<[u8]> for $buf {
            fn eq(&self, other: &[u8]) -> bool {
                self.as_slice() == other
            }
        }

        impl PartialEq<&[u8]> for $buf {
            fn eq(&self, other: &&[u8]) -> bool {
                self.as_slice() == *other
            }
        }

        impl PartialEq<str> for $buf {
            fn eq(&self, other: &str) -> bool {
                self.as_slice() == other.as_bytes()
            }
        }

        impl PartialEq<&str> for $buf {
            fn eq(&self, other: &&str) -> bool {
                self.as_slice() == other.as_bytes()
            }
        }

        impl PartialEq<$view<'_>> for $buf {
            fn eq(&self, other: &$view<'_>) -> bool {
                self.as_slice() == other.as_slice()
            }
        }

        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        pub struct $view<'a>(&'a [u8]);

        impl<'a> $view<'a> {
            #[inline]
            pub(crate) fn new_unchecked(value: &'a [u8]) -> Self {
                debug_assert!(
                    $buf::is_allowed(value),
                    concat!("invalid ", stringify!($view), ": {:?}"),
                    value
                );
                Self(value)
            }

            #[inline]
            pub fn as_slice(&self) -> &'a [u8] {
                self.0
            }
            #[inline]
            pub fn into_owned(self) -> $buf {
                $buf(SmtBytes::new(self.0).into_owned())
            }
            pub fn len(&self) -> usize {
                self.0.len()
            }
            pub fn is_empty(&self) -> bool {
                self.0.is_empty()
            }
            pub fn iter(&self) -> impl Iterator<Item = u8> {
                self.0.iter().copied()
            }
        }

        impl std::fmt::Debug for $view<'_> {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Debug::fmt(&self.0, f)
            }
        }

        impl std::borrow::Borrow<[u8]> for $view<'_> {
            fn borrow(&self) -> &[u8] {
                self.as_slice()
            }
        }

        impl PartialEq<[u8]> for $view<'_> {
            fn eq(&self, other: &[u8]) -> bool {
                self.as_slice() == other
            }
        }

        impl PartialEq<&[u8]> for $view<'_> {
            fn eq(&self, other: &&[u8]) -> bool {
                self.as_slice() == *other
            }
        }

        impl PartialEq<str> for $view<'_> {
            fn eq(&self, other: &str) -> bool {
                self.as_slice() == other.as_bytes()
            }
        }

        impl PartialEq<&str> for $view<'_> {
            fn eq(&self, other: &&str) -> bool {
                self.as_slice() == other.as_bytes()
            }
        }

        impl PartialEq<$buf> for $view<'_> {
            fn eq(&self, other: &$buf) -> bool {
                self.as_slice() == other.as_slice()
            }
        }
    };
}

string8_newtype!(SmtStringContentBuf, SmtStringContent);
string8_newtype!(SmtKeywordBuf, SmtKeyword);
string8_newtype!(SmtNumeralBuf, SmtNumeral);
string8_newtype!(SmtHexDigitsBuf, SmtHexDigits);
string8_newtype!(SmtBinDigitsBuf, SmtBinDigits);
string8_newtype!(SmtDecimalBuf, SmtDecimal);
string8_newtype!(SmtWhitespaceBuf, SmtWhitespace);
string8_newtype!(SmtCommentBuf, SmtComment);

/// The numeral does not fit into the integer type it is converted to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SmtNumeralOverflow;

impl<'a> SmtNumeral<'a> {
    /// The value as `u32`, or `None` if it does not fit.
    pub fn to_u32(&self) -> Option<u32> {
        u32::try_from(self.to_u64()?).ok()
    }

    /// The value as `u64`, or `None` if it does not fit.
    pub fn to_u64(&self) -> Option<u64> {
        let mut value: u64 = 0;
        for digit in self.iter() {
            value = value
                .checked_mul(10)?
                .checked_add(u64::from(digit - b'0'))?;
        }
        Some(value)
    }

    /// The value as `u128`, or `None` if it does not fit.
    pub fn to_u128(&self) -> Option<u128> {
        let mut value: u128 = 0;
        for digit in self.iter() {
            value = value
                .checked_mul(10)?
                .checked_add(u128::from(digit - b'0'))?;
        }
        Some(value)
    }

    /// The value as `usize`, or `None` if it does not fit.
    ///
    /// Whether a value fits depends on the platform.
    pub fn to_usize(&self) -> Option<usize> {
        usize::try_from(self.to_u64()?).ok()
    }
}

impl SmtNumeralBuf {
    /// Construct from `u32`.
    pub fn from_u32(value: u32) -> Self {
        // the decimal string of an integer is a numeral
        Self(SmtBytesBuf::from_vec(value.to_string().into_bytes()))
    }

    /// Construct from `u64`.
    pub fn from_u64(value: u64) -> Self {
        // the decimal string of an integer is a numeral
        Self(SmtBytesBuf::from_vec(value.to_string().into_bytes()))
    }

    /// Construct from `u128`.
    pub fn from_u128(value: u128) -> Self {
        // the decimal string of an integer is a numeral
        Self(SmtBytesBuf::from_vec(value.to_string().into_bytes()))
    }

    /// Construct from `usize`.
    pub fn from_usize(value: usize) -> Self {
        // the decimal string of an integer is a numeral
        Self(SmtBytesBuf::from_vec(value.to_string().into_bytes()))
    }

    /// The value as `u32`, or `None` if it does not fit.
    pub fn to_u32(&self) -> Option<u32> {
        self.view().to_u32()
    }

    /// The value as `u64`, or `None` if it does not fit.
    pub fn to_u64(&self) -> Option<u64> {
        self.view().to_u64()
    }

    /// The value as `u128`, or `None` if it does not fit.
    pub fn to_u128(&self) -> Option<u128> {
        self.view().to_u128()
    }

    /// The value as `usize`, or `None` if it does not fit.
    ///
    /// Whether a value fits depends on the platform.
    pub fn to_usize(&self) -> Option<usize> {
        self.view().to_usize()
    }
}

macro_rules! numeral_try_from {
    ($int:ty, $method:ident) => {
        impl TryFrom<SmtNumeral<'_>> for $int {
            type Error = SmtNumeralOverflow;

            fn try_from(numeral: SmtNumeral<'_>) -> Result<Self, Self::Error> {
                numeral.$method().ok_or(SmtNumeralOverflow)
            }
        }

        impl TryFrom<&SmtNumeralBuf> for $int {
            type Error = SmtNumeralOverflow;

            fn try_from(numeral: &SmtNumeralBuf) -> Result<Self, Self::Error> {
                numeral.$method().ok_or(SmtNumeralOverflow)
            }
        }
    };
}

numeral_try_from!(u32, to_u32);
numeral_try_from!(u64, to_u64);
numeral_try_from!(u128, to_u128);
numeral_try_from!(usize, to_usize);

macro_rules! numeral_from {
    ($int:ty, $method:ident) => {
        impl From<$int> for SmtNumeralBuf {
            fn from(value: $int) -> Self {
                Self::$method(value)
            }
        }
    };
}

numeral_from!(u32, from_u32);
numeral_from!(u64, from_u64);
numeral_from!(u128, from_u128);
numeral_from!(usize, from_usize);

impl<'a> SmtDecimal<'a> {
    /// The whole part, before the dot.
    pub fn whole(&self) -> SmtNumeral<'a> {
        SmtNumeral::new_unchecked(&self.0[..self.dot()])
    }

    /// The digits of the fractional part, after the dot.
    ///
    /// They may have leading zeros, so they are not a numeral.
    pub fn fraction(&self) -> &'a [u8] {
        &self.0[self.dot() + 1..]
    }

    fn dot(&self) -> usize {
        self.0
            .iter()
            .position(|c| *c == b'.')
            .expect("a decimal contains a dot")
    }
}

impl SmtDecimalBuf {
    /// The whole part, before the dot.
    pub fn whole(&self) -> SmtNumeral<'_> {
        self.view().whole()
    }

    /// The digits of the fractional part, after the dot.
    ///
    /// They may have leading zeros, so they are not a numeral.
    pub fn fraction(&self) -> &[u8] {
        self.view().fraction()
    }
}

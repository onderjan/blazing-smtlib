use std::fmt::Debug;

use crate::{SmtBytes, SmtBytesView, lexer::CharClass};

/// SMT-LIB string content.
///
/// May be empty.
/// Must contain only SMT-LIB printable or whitespace bytes.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtStringContent(SmtBytes);

impl SmtStringContent {
    pub fn is_allowed(value: &[u8]) -> bool {
        value
            .iter()
            .copied()
            .all(|c| CharClass::from(c).is_printable_or_whitespace())
    }
}

/// SMT-LIB symbol, quoted or unquoted.
///
/// May be empty.
/// Must contain only SMT-LIB printable or whitespace bytes except for pipe (|) and backslash (\).
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtSymbol(SmtBytes);

impl SmtSymbol {
    pub fn is_allowed(value: &[u8]) -> bool {
        value
            .iter()
            .copied()
            .all(|c| CharClass::from(c).is_printable_or_whitespace() && c != b'|' && c != b'\\')
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
pub struct SmtKeyword(SmtBytes);

impl SmtKeyword {
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
pub struct SmtNumeral(SmtBytes);

impl SmtNumeral {
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

    /// Construct from `usize`.
    pub fn from_usize(value: usize) -> Self {
        // convert the value into a string and get its bytes
        // this is allowed since it produces digits without leading zeros
        // or the allowed special case of constant "0"
        Self(SmtBytes::from_vec(value.to_string().into_bytes()))
    }
}

/// SMT-LIB hexadecimal digits (base 16).
///
/// Cannot be empty.
/// Must contain only digits, lower-case letters a-f or upper-case letters A-F.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtHexDigits(SmtBytes);

impl SmtHexDigits {
    pub fn is_allowed(value: &[u8]) -> bool {
        !value.is_empty() && value.iter().all(|c| c.is_ascii_hexdigit())
    }
}

/// SMT-LIB binary digits (base 2).
///
/// Cannot be empty.
/// Must contain only the digits 0, 1.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtBinDigits(SmtBytes);

impl SmtBinDigits {
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
pub struct SmtDecimal(SmtBytes);

impl SmtDecimal {
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
        if !SmtNumeral::is_allowed(whole_part) {
            return false;
        }

        // the fractional part must be a non-empty string of digits
        !fractional_part.is_empty() && fractional_part.iter().all(|c| c.is_ascii_digit())
    }
}

#[derive(Debug)]
pub struct SmtDisallowedByteVecError(SmtBytes);

impl SmtDisallowedByteVecError {
    pub fn into_vec(self) -> Vec<u8> {
        self.0.into_vec()
    }
}

macro_rules! string8_newtype {
    ($name:ident, $view:ident) => {
        impl $name {
            pub fn new(value: Vec<u8>) -> Result<Self, SmtDisallowedByteVecError> {
                let value = SmtBytes::from_vec(value);
                if Self::is_allowed(value.as_slice()) {
                    Ok(Self(value))
                } else {
                    Err(SmtDisallowedByteVecError(value))
                }
            }

            pub fn as_slice(&self) -> &[u8] {
                self.0.as_slice()
            }
            pub fn as_view(&self) -> $view<'_> {
                $view(self.0.as_slice())
            }
            pub fn into_string8(self) -> SmtBytes {
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

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Debug::fmt(&self.0, f)
            }
        }

        impl std::borrow::Borrow<[u8]> for $name {
            fn borrow(&self) -> &[u8] {
                self.as_slice()
            }
        }

        impl PartialEq<[u8]> for $name {
            fn eq(&self, other: &[u8]) -> bool {
                self.as_slice() == other
            }
        }

        impl PartialEq<&[u8]> for $name {
            fn eq(&self, other: &&[u8]) -> bool {
                self.as_slice() == *other
            }
        }

        impl PartialEq<str> for $name {
            fn eq(&self, other: &str) -> bool {
                self.as_slice() == other.as_bytes()
            }
        }

        impl PartialEq<&str> for $name {
            fn eq(&self, other: &&str) -> bool {
                self.as_slice() == other.as_bytes()
            }
        }

        impl PartialEq<$view<'_>> for $name {
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
                    $name::is_allowed(value),
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
            pub fn into_owned(self) -> $name {
                $name(SmtBytesView::new(self.0).into_owned())
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

        impl PartialEq<$name> for $view<'_> {
            fn eq(&self, other: &$name) -> bool {
                self.as_slice() == other.as_slice()
            }
        }
    };
}

string8_newtype!(SmtStringContent, SmtStringContentView);
string8_newtype!(SmtSymbol, SmtSymbolView);
string8_newtype!(SmtKeyword, SmtKeywordView);
string8_newtype!(SmtNumeral, SmtNumeralView);
string8_newtype!(SmtHexDigits, SmtHexDigitsView);
string8_newtype!(SmtBinDigits, SmtBinDigitsView);
string8_newtype!(SmtDecimal, SmtDecimalView);

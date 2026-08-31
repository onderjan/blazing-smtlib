use std::fmt::{Debug, Write};

use crate::{String8, String8View, read::lexer::CharClass};

/// SMT-LIB string content.
///
/// May be empty.
/// Must contain only SMT-LIB printable or whitespace bytes.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtStringContent(String8);

impl SmtStringContent {
    pub fn is_allowed(value: &[u8]) -> bool {
        value
            .iter()
            .copied()
            .all(|c| CharClass::from(c).is_printable_or_whitespace())
    }
}

/// SMT-LIB symbol.
///
/// May be empty.
/// Must contain only SMT-LIB printable or whitespace bytes except for pipe (|) and backslash (\).
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtSymbol(String8);

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
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtKeyword(String8);

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
pub struct SmtNumeral(String8);

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
}

/// SMT-LIB digits (base 10).
///
/// Cannot be empty.
/// Must contain only digits.
///
/// Unlike `SmtNumeral`, there is no restriction on leading zeros.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtDigits(String8);

impl SmtDigits {
    pub fn is_allowed(value: &[u8]) -> bool {
        !value.is_empty() && value.iter().all(|c| c.is_ascii_digit())
    }
}

/// SMT-LIB hexadecimal digits (base 16).
///
/// Cannot be empty.
/// Must contain only digits, lower-case letters a-f or upper-case letters A-F.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtHexDigits(String8);

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
pub struct SmtBinDigits(String8);

impl SmtBinDigits {
    pub fn is_allowed(value: &[u8]) -> bool {
        !value.is_empty() && value.iter().copied().all(|c| c == b'0' || c == b'1')
    }
}

#[derive(Debug)]
pub struct SmtDisallowedByteVecError(String8);

impl SmtDisallowedByteVecError {
    pub fn into_vec(self) -> Vec<u8> {
        self.0.into_vec()
    }
}

macro_rules! string8_newtype {
    ($name:ident) => {
        impl $name {
            pub fn new(value: Vec<u8>) -> Result<Self, SmtDisallowedByteVecError> {
                let value = String8::from_vec(value);
                if Self::is_allowed(value.as_slice()) {
                    Ok(Self(value))
                } else {
                    Err(SmtDisallowedByteVecError(value))
                }
            }

            pub(crate) fn new_unchecked(value: String8) -> Self {
                debug_assert!(
                    Self::is_allowed(value.as_slice()),
                    concat!("invalid ", stringify!($name), ": {:?}"),
                    value
                );
                Self(value)
            }

            pub fn as_slice(&self) -> &[u8] {
                self.0.as_slice()
            }
            pub fn as_view(&self) -> String8View<'_> {
                self.0.as_view()
            }
            pub fn into_string8(self) -> String8 {
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
    };
}

string8_newtype!(SmtStringContent);
string8_newtype!(SmtSymbol);
string8_newtype!(SmtKeyword);
string8_newtype!(SmtNumeral);
string8_newtype!(SmtDigits);
string8_newtype!(SmtHexDigits);
string8_newtype!(SmtBinDigits);

/// SMT-LIB decimal (a decimal number with whole part + fractional part)
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtDecimal {
    pub whole_part: SmtNumeral,
    pub fractional_part: SmtDigits,
}

impl Debug for SmtDecimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // format manually to avoid extraneous quotes
        // all characters are digits, no escaping needed
        f.write_char('"')?;
        for c in self.whole_part.iter() {
            f.write_char(c as char)?;
        }
        f.write_char('.')?;
        for c in self.fractional_part.iter() {
            f.write_char(c as char)?;
        }
        f.write_char('"')
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn string_content_accepts_any_printable_or_whitespace_bytes() {
        assert!(SmtStringContent::is_allowed(b""));
        assert!(SmtStringContent::is_allowed(b"a-simple-symbol~!@$%^&*_-+=<>.?/"));
        assert!(SmtStringContent::is_allowed(b"A quick brown fox jumps over a lazy dog."));
        // any non-ASCII bytes are allowed, whether or not they form UTF-8
        assert!(SmtStringContent::is_allowed(
            "Příšerně žluťoučký kůň úpěl ďábelské ódy.".as_bytes()
        ));
        assert!(SmtStringContent::is_allowed(b"\xFF"));
        // unlike symbols, string content may contain pipes and backslashes
        assert!(SmtStringContent::is_allowed(b"a|b"));
        assert!(SmtStringContent::is_allowed(b"a\\b"));
    }

    #[test]
    fn symbol_accepts_everything_a_string_does_except_pipe_and_backslash() {
        assert!(SmtSymbol::is_allowed(b""));
        assert!(SmtSymbol::is_allowed(b"a-simple-symbol~!@$%^&*_-+=<>.?/"));
        assert!(SmtSymbol::is_allowed(b"A quick brown fox jumps over a lazy dog."));
        assert!(SmtSymbol::is_allowed(
            "Příšerně žluťoučký kůň úpěl ďábelské ódy.".as_bytes()
        ));
        assert!(SmtSymbol::is_allowed(b"\xFF"));

        assert!(!SmtSymbol::is_allowed(b"a|b"));
        assert!(!SmtSymbol::is_allowed(b"a\\b"));
    }

    #[test]
    fn keyword_accepts_only_nonempty_simple_symbol_bytes() {
        assert!(SmtKeyword::is_allowed(b"a-simple-symbol~!@$%^&*_-+=<>.?/"));
        assert!(SmtKeyword::is_allowed(b"quick"));
        assert!(SmtKeyword::is_allowed(b"let"));
        // TODO: clarify whether this is allowed by the standard
        assert!(SmtKeyword::is_allowed(b"0"));

        assert!(!SmtKeyword::is_allowed(b""));
        // no whitespace, UTF-8, or non-UTF-8 bytes, unlike strings and symbols
        assert!(!SmtKeyword::is_allowed(b"A quick brown fox jumps over a lazy dog."));
        assert!(!SmtKeyword::is_allowed(
            "Příšerně žluťoučký kůň úpěl ďábelské ódy.".as_bytes()
        ));
        assert!(!SmtKeyword::is_allowed("žluťoučký".as_bytes()));
        assert!(!SmtKeyword::is_allowed(b"\xFF"));
    }

    #[test]
    fn del_is_rejected_everywhere() {
        assert!(!SmtStringContent::is_allowed(b"a\x7Fb"));
        assert!(!SmtSymbol::is_allowed(b"a\x7Fb"));
        assert!(!SmtKeyword::is_allowed(b"a\x7Fb"));
    }

    #[test]
    fn digit_kinds_reject_the_empty_string_and_accept_zero() {
        assert!(!SmtNumeral::is_allowed(b""));
        assert!(!SmtDigits::is_allowed(b""));
        assert!(!SmtHexDigits::is_allowed(b""));
        assert!(!SmtBinDigits::is_allowed(b""));

        assert!(SmtNumeral::is_allowed(b"0"));
        assert!(SmtDigits::is_allowed(b"0"));
        assert!(SmtHexDigits::is_allowed(b"0"));
        assert!(SmtBinDigits::is_allowed(b"0"));
    }

    #[test]
    fn only_numeral_rejects_leading_zeros() {
        assert!(!SmtNumeral::is_allowed(b"00"));
        assert!(!SmtNumeral::is_allowed(b"01"));
        assert!(SmtDigits::is_allowed(b"00"));
        assert!(SmtDigits::is_allowed(b"01"));
        assert!(SmtHexDigits::is_allowed(b"00"));
        assert!(SmtHexDigits::is_allowed(b"01"));
        assert!(SmtBinDigits::is_allowed(b"00"));
        assert!(SmtBinDigits::is_allowed(b"01"));
    }

    #[test]
    fn numeral_accepts_numbers_without_leading_zeros() {
        assert!(SmtNumeral::is_allowed(b"10"));
        assert!(SmtNumeral::is_allowed(b"1024"));
        assert!(SmtNumeral::is_allowed(b"70"));
    }

    #[test]
    fn digit_kinds_accept_only_their_own_digits() {
        assert!(SmtDigits::is_allowed(b"1024"));
        assert!(SmtDigits::is_allowed(b"077"));
        assert!(!SmtDigits::is_allowed(b"aF"));

        assert!(SmtHexDigits::is_allowed(b"1024"));
        assert!(SmtHexDigits::is_allowed(b"077"));
        assert!(SmtHexDigits::is_allowed(b"aF"));
        assert!(!SmtHexDigits::is_allowed(b"g"));
        assert!(!SmtHexDigits::is_allowed(b"G"));

        assert!(SmtBinDigits::is_allowed(b"01101"));
        assert!(!SmtBinDigits::is_allowed(b"077"));
        assert!(!SmtBinDigits::is_allowed(b"aF"));
    }

    #[test]
    fn decimals_with_trailing_fractional_zeros_are_distinct() {
        fn dec(whole_part: &[u8], fractional_part: &[u8]) -> SmtDecimal {
            SmtDecimal {
                whole_part: SmtNumeral::new(whole_part.to_vec())
                    .expect("Whole part should succeed"),
                fractional_part: SmtDigits::new(fractional_part.to_vec())
                    .expect("Fractional part should succeed"),
            }
        }

        // SMT-LIB does not consider '3.50' an overlong encoding of '3.5',
        // but as two separate things syntactically
        assert_ne!(dec(b"1", b"0"), dec(b"1", b"0000"));
        assert_ne!(dec(b"3", b"5"), dec(b"3", b"50"));
    }
}

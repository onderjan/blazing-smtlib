use std::fmt::{Debug, Write};

use crate::{
    SmtVersion,
    lexer::CharClass,
    lexicon::{SmtBytes, SmtBytesBuf, SmtReserved},
};

impl SmtStringContentBuf {
    /// Returns `true` if the bytes are allowed as string content.
    pub fn is_allowed(value: &[u8]) -> bool {
        value
            .iter()
            .copied()
            .all(|c| CharClass::from(c).is_printable_or_whitespace())
    }
}

/// Owned symbol (quoted or unquoted).
///
/// The symbol carries its bytes and whether it is quoted.
///
/// A quoted symbol may be empty and contains only printable or whitespace bytes other than `|`
/// and `\`. An unquoted symbol is not empty, does not start with a digit, and contains only
/// ASCII letters, digits and the characters `~ ! @ $ % ^ & * _ - + = < > . ? /`.
///
/// Equality and hashing are not implemented, as a quoted and an unquoted symbol with the same
/// content are the same symbol: compare their content instead, e.g. from
/// [`bytes`](Self::bytes).
///
/// The content is stripped of the enclosing pipes if quoted, e.g. for the token `|a b|`,
/// [`as_slice`](Self::as_slice) returns `b"a b"`.
#[derive(Clone)]
pub struct SmtSymbolBuf {
    is_quoted: bool,
    value: SmtBytesBuf,
}

impl SmtSymbolBuf {
    /// Returns `true` if the bytes are allowed as the content of an unquoted symbol.
    pub fn is_unquoted_allowed(value: &[u8]) -> bool {
        !value.is_empty()
            && !value[0].is_ascii_digit()
            && value
                .iter()
                .all(|c| CharClass::from(*c).is_allowed_in_simple_symbol())
    }

    /// Returns `true` if the bytes are allowed as the content of a quoted symbol.
    pub fn is_quoted_allowed(value: &[u8]) -> bool {
        value
            .iter()
            .copied()
            .all(|c| CharClass::from(c).is_printable_or_whitespace() && c != b'|' && c != b'\\')
    }

    /// Returns `true` if the bytes are allowed in a simple symbol and are not a
    /// reserved word of the given version.
    pub fn is_simple_in(value: &[u8], version: SmtVersion) -> bool {
        Self::is_unquoted_allowed(value) && SmtReserved::from_bytes(value, version).is_none()
    }

    /// Returns `true` if this is a quoted symbol enclosed in pipes, e.g. `|x|`, and `false` if it
    /// is a simple symbol, e.g. `x`.
    pub fn is_quoted(&self) -> bool {
        self.is_quoted
    }

    /// Returns `true` if the symbol reads back as itself in the given version: it is
    /// quoted, or it is simple and not a reserved word of the version.
    pub fn is_symbol_in(&self, version: SmtVersion) -> bool {
        self.view().is_symbol_in(version)
    }

    /// Quotes the symbol if it is simple and a reserved word of the given
    /// version; any other symbol is returned as it is.
    pub fn into_versioned(self, version: SmtVersion) -> Self {
        Self {
            is_quoted: self.is_quoted
                || SmtReserved::from_bytes(self.as_slice(), version).is_some(),
            value: self.value,
        }
    }

    /// Creates an unquoted symbol if the bytes are allowed in one.
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

    /// Creates a quoted symbol if the bytes are allowed in one.
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

    /// Creates a symbol that reads back as itself in the given version.
    ///
    /// The symbol is simple if its bytes are allowed in a simple symbol and are
    /// not a reserved word of the version, and quoted otherwise.
    pub fn new_in(value: Vec<u8>, version: SmtVersion) -> Result<Self, SmtDisallowedByteVecError> {
        if Self::is_simple_in(&value, version) {
            Self::new_unquoted(value)
        } else {
            Self::new_quoted(value)
        }
    }

    /// Returns the content as [`SmtBytes`].
    pub fn bytes(&self) -> SmtBytes<'_> {
        self.value.view()
    }

    /// Returns the content as a byte slice.
    pub fn as_slice(&self) -> &[u8] {
        self.bytes().as_slice()
    }

    /// Views as [`SmtSymbol`].
    pub fn view(&self) -> SmtSymbol<'_> {
        SmtSymbol {
            is_quoted: self.is_quoted,
            value: self.bytes(),
        }
    }
    /// Converts into the content as [`SmtBytesBuf`].
    pub fn into_bytes_buf(self) -> SmtBytesBuf {
        self.value
    }
    /// Converts into the content as a byte vector.
    pub fn into_vec(self) -> Vec<u8> {
        self.value.into_vec()
    }
    /// Returns the length of the content in bytes.
    pub fn len(&self) -> usize {
        self.value.len()
    }
    /// Returns `true` if the content is empty.
    pub fn is_empty(&self) -> bool {
        self.value.is_empty()
    }
    /// Returns an iterator over the bytes of the content.
    pub fn iter(&self) -> impl Iterator<Item = u8> {
        self.value.iter()
    }
}

impl Debug for SmtSymbolBuf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.view(), f)
    }
}

/// View of a symbol (quoted or unquoted).
///
/// The symbol carries its bytes and whether it is quoted.
///
/// A quoted symbol may be empty and contains only printable or whitespace bytes other than `|`
/// and `\`. An unquoted symbol is not empty, does not start with a digit, and contains only
/// ASCII letters, digits and the characters `~ ! @ $ % ^ & * _ - + = < > . ? /`.
///
/// Equality and hashing are not implemented, as a quoted and an unquoted symbol with the same
/// content are the same symbol: compare their content instead, e.g. from
/// [`bytes`](Self::bytes).
///
/// The content is stripped of the enclosing pipes if quoted, e.g. for the token `|a b|`,
/// [`as_slice`](Self::as_slice) returns `b"a b"`.
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

    /// Creates an unquoted symbol if the bytes are allowed in one.
    pub fn new_unquoted(value: &'a [u8]) -> Result<Self, SmtDisallowedBytesError> {
        if SmtSymbolBuf::is_unquoted_allowed(value) {
            Ok(Self {
                is_quoted: false,
                value: SmtBytes::new(value),
            })
        } else {
            Err(SmtDisallowedBytesError)
        }
    }

    /// Creates a quoted symbol if the bytes are allowed in one.
    pub fn new_quoted(value: &'a [u8]) -> Result<Self, SmtDisallowedBytesError> {
        if SmtSymbolBuf::is_quoted_allowed(value) {
            Ok(Self {
                is_quoted: true,
                value: SmtBytes::new(value),
            })
        } else {
            Err(SmtDisallowedBytesError)
        }
    }

    /// Creates a symbol that reads back as itself in the given version.
    ///
    /// The symbol is simple if its bytes are allowed in a simple symbol and are
    /// not a reserved word of the version, and quoted otherwise.
    pub fn new_in(value: &'a [u8], version: SmtVersion) -> Result<Self, SmtDisallowedBytesError> {
        if SmtSymbolBuf::is_simple_in(value, version) {
            Self::new_unquoted(value)
        } else {
            Self::new_quoted(value)
        }
    }

    /// Returns `true` if this is a quoted symbol enclosed in pipes, e.g. `|x|`, and `false` if it
    /// is a simple symbol, e.g. `x`.
    pub fn is_quoted(&self) -> bool {
        self.is_quoted
    }

    /// Returns `true` if the symbol reads back as itself in the given version: it is
    /// quoted, or it is simple and not a reserved word of the version.
    pub fn is_symbol_in(&self, version: SmtVersion) -> bool {
        self.is_quoted || SmtReserved::from_bytes(self.as_slice(), version).is_none()
    }

    /// Quotes the symbol if it is simple and a reserved word of the given
    /// version; any other symbol is returned as it is.
    pub fn into_versioned(self, version: SmtVersion) -> Self {
        Self {
            is_quoted: self.is_quoted
                || SmtReserved::from_bytes(self.as_slice(), version).is_some(),
            value: self.value,
        }
    }

    /// Returns the content as [`SmtBytes`].
    pub fn bytes(&self) -> SmtBytes<'a> {
        self.value
    }

    /// Returns the content as a byte slice.
    pub fn as_slice(&self) -> &'a [u8] {
        self.value.as_slice()
    }

    /// Converts into [`SmtSymbolBuf`].
    pub fn into_owned(self) -> SmtSymbolBuf {
        SmtSymbolBuf {
            is_quoted: self.is_quoted,
            value: self.bytes().into_owned(),
        }
    }

    /// Returns the length of the content in bytes.
    pub fn len(&self) -> usize {
        self.value.len()
    }

    /// Returns `true` if the content is empty.
    pub fn is_empty(&self) -> bool {
        self.value.is_empty()
    }

    /// Returns an iterator over the bytes of the content.
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

impl SmtKeywordBuf {
    /// Returns `true` if the bytes are allowed as the content of a keyword.
    pub fn is_allowed(value: &[u8]) -> bool {
        !value.is_empty()
            && value
                .iter()
                .copied()
                .all(|c| CharClass::from(c).is_allowed_in_simple_symbol())
    }
}

impl SmtNumeralBuf {
    /// Returns `true` if the bytes are allowed as a numeral.
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

impl SmtHexDigitsBuf {
    /// Returns `true` if the bytes are allowed as hexadecimal digits.
    pub fn is_allowed(value: &[u8]) -> bool {
        !value.is_empty() && value.iter().all(|c| c.is_ascii_hexdigit())
    }
}

impl SmtBinDigitsBuf {
    /// Returns `true` if the bytes are allowed as binary digits.
    pub fn is_allowed(value: &[u8]) -> bool {
        !value.is_empty() && value.iter().copied().all(|c| c == b'0' || c == b'1')
    }
}

impl SmtDecimalBuf {
    /// Returns `true` if the bytes are allowed as a decimal.
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

impl SmtWhitespaceBuf {
    /// Returns `true` if the bytes are allowed as whitespace content.
    pub fn is_allowed(value: &[u8]) -> bool {
        !value.is_empty()
            && value
                .iter()
                .copied()
                .all(|c| matches!(c, b'\t' | b'\n' | b'\r' | b' '))
    }
}

impl SmtCommentBuf {
    /// Returns `true` if the bytes are allowed as the content of a comment.
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

/// Error constructing an owned value from disallowed bytes.
///
/// See the type being constructed for the validity condition. The bytes are
/// returned by [`into_vec`](Self::into_vec).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SmtDisallowedByteVecError(SmtBytesBuf);

impl SmtDisallowedByteVecError {
    /// Converts into the disallowed bytes.
    pub fn into_vec(self) -> Vec<u8> {
        self.0.into_vec()
    }
}

impl std::fmt::Display for SmtDisallowedByteVecError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("given byte vector is not allowed")
    }
}

impl std::error::Error for SmtDisallowedByteVecError {}

/// Error constructing a view from disallowed bytes.
///
/// See the type being constructed for the validity condition.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SmtDisallowedBytesError;

impl std::fmt::Display for SmtDisallowedBytesError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("given bytes are not allowed")
    }
}

impl std::error::Error for SmtDisallowedBytesError {}

macro_rules! string8_newtype {
    (
        $(#[$buf_doc:meta])*
        $buf:ident,
        $(#[$view_doc:meta])*
        $view:ident,
        $(#[$doc:meta])*
    ) => {
        $(#[$buf_doc])*
        ///
        $(#[$doc])*
        #[derive(Clone, PartialEq, Eq, Hash)]
        pub struct $buf(SmtBytesBuf);

        impl $buf {
            /// Creates from the bytes if they are allowed.
            pub fn new(value: Vec<u8>) -> Result<Self, SmtDisallowedByteVecError> {
                let value = SmtBytesBuf::from_vec(value);
                if Self::is_allowed(value.as_slice()) {
                    Ok(Self(value))
                } else {
                    Err(SmtDisallowedByteVecError(value))
                }
            }

            /// Returns the content as a byte slice.
            pub fn as_slice(&self) -> &[u8] {
                self.0.as_slice()
            }
            #[doc = concat!("Views as [`", stringify!($view), "`].")]
            pub fn view(&self) -> $view<'_> {
                $view(self.0.as_slice())
            }
            /// Converts into the content as [`SmtBytesBuf`].
            pub fn into_bytes_buf(self) -> SmtBytesBuf {
                self.0
            }
            /// Converts into the content as a byte vector.
            pub fn into_vec(self) -> Vec<u8> {
                self.0.into_vec()
            }
            /// Returns the length of the content in bytes.
            pub fn len(&self) -> usize {
                self.0.len()
            }
            /// Returns `true` if the content is empty.
            pub fn is_empty(&self) -> bool {
                self.0.is_empty()
            }
            /// Returns an iterator over the bytes of the content.
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

        $(#[$view_doc])*
        ///
        $(#[$doc])*
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

            /// Creates from the bytes if they are allowed.
            pub fn new(value: &'a [u8]) -> Result<Self, SmtDisallowedBytesError> {
                if $buf::is_allowed(value) {
                    Ok(Self(value))
                } else {
                    Err(SmtDisallowedBytesError)
                }
            }

            /// Returns the content as a byte slice.
            #[inline]
            pub fn as_slice(&self) -> &'a [u8] {
                self.0
            }
            #[doc = concat!("Converts into [`", stringify!($buf), "`].")]
            #[inline]
            pub fn into_owned(self) -> $buf {
                $buf(SmtBytes::new(self.0).into_owned())
            }
            /// Returns the length of the content in bytes.
            pub fn len(&self) -> usize {
                self.0.len()
            }
            /// Returns `true` if the content is empty.
            pub fn is_empty(&self) -> bool {
                self.0.is_empty()
            }
            /// Returns an iterator over the bytes of the content.
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

string8_newtype! {
    /// Owned string content.
    SmtStringContentBuf,
    /// View of string content.
    SmtStringContent,
    /// May be empty.
    /// Must contain only SMT-LIB printable or whitespace bytes.
    ///
    /// The content is stripped of the enclosing quotes and its escapes are resolved,
    /// e.g. for the token `"a""b"` in version 2.5 or later, [`as_slice`](Self::as_slice)
    /// returns `b"a\"b"`.
}

string8_newtype! {
    /// Owned keyword.
    SmtKeywordBuf,
    /// View of a keyword.
    SmtKeyword,
    /// Cannot be empty.
    /// Must contain only SMT-LIB simple-symbol-class bytes.
    ///
    /// A keyword may start with a digit and may spell a reserved word.
    /// It is defined in version 2.0 as a colon followed by a non-empty sequence
    /// of simple-symbol-class bytes with no further restriction. From version 2.5 on,
    /// the standard defines it as a colon followed by a simple symbol, which
    /// read literally excludes a leading digit and the reserved words. This crate
    /// takes this as unintended and keeps the 2.0 rule in every version: the standard's
    /// own keyword examples include `:56`, and there is no need to exclude
    /// reserved words as the colon already uniquely determines the category.
    ///
    /// The content is stripped of the starting colon, e.g. for the token `:named`,
    /// [`as_slice`](Self::as_slice) returns `b"named"`.
}

string8_newtype! {
    /// Owned numeral (base 10).
    SmtNumeralBuf,
    /// View of a numeral (base 10).
    SmtNumeral,
    /// Cannot be empty.
    /// Must contain only digits.
    /// Cannot contain any leading zeros except for the constant `0` itself.
}

string8_newtype! {
    /// Owned hexadecimal digits (base 16).
    SmtHexDigitsBuf,
    /// View of hexadecimal digits (base 16).
    SmtHexDigits,
    /// Cannot be empty.
    /// Must contain only digits, lower-case letters `a`-`f` or upper-case letters `A`-`F`.
    ///
    /// The content is stripped of the base declaration, e.g. for the token `#xA04`,
    /// [`as_slice`](Self::as_slice) returns `b"A04"`.
}

string8_newtype! {
    /// Owned binary digits (base 2).
    SmtBinDigitsBuf,
    /// View of binary digits (base 2).
    SmtBinDigits,
    /// Cannot be empty.
    /// Must contain only the digits `0`, `1`.
    ///
    /// The content is stripped of the base declaration, e.g. for the token `#b0101`,
    /// [`as_slice`](Self::as_slice) returns `b"0101"`.
}

string8_newtype! {
    /// Owned decimal (base 10).
    SmtDecimalBuf,
    /// View of a decimal (base 10).
    SmtDecimal,
    /// A dot (the character `.`) must be present. It divides the decimal into
    /// a whole part (before it) and a fractional part (after it).
    ///
    /// The whole part follows the same rules as [`SmtNumeral`]:
    /// cannot be empty, must contain only digits, and
    /// cannot contain any leading zeros except for the constant `0` itself.
    ///
    /// The fractional part cannot be empty and must contain only digits.
    ///
}

string8_newtype! {
    /// Owned whitespace content.
    SmtWhitespaceBuf,
    /// View of whitespace content.
    SmtWhitespace,
    /// Cannot be empty.
    /// Must contain only tabs, line feeds, carriage returns and spaces.
}

string8_newtype! {
    /// Owned comment.
    SmtCommentBuf,
    /// View of a comment.
    SmtComment,
    /// The content may be empty.
    /// Only the last byte may be a carriage return (CR) or a line feed (LF).
    /// If the comment runs to the end of the input, there is no ending CR/LF.
    ///
    /// The content is stripped of the starting semicolon, e.g. for the token `; note`
    /// followed by a line feed, [`as_slice`](Self::as_slice) returns `b" note\n"`.
}

/// Error converting into an unsigned type that cannot hold the numeric value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SmtNumericOverflowError;

impl std::fmt::Display for SmtNumericOverflowError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("value does not fit into integer type")
    }
}

impl std::error::Error for SmtNumericOverflowError {}

impl<'a> SmtNumeral<'a> {
    /// Returns the value as [`u32`], or [`None`] if it does not fit.
    pub fn to_u32(&self) -> Option<u32> {
        u32::try_from(self.to_u64()?).ok()
    }

    /// Returns the value as [`u64`], or [`None`] if it does not fit.
    pub fn to_u64(&self) -> Option<u64> {
        let mut value: u64 = 0;
        for digit in self.iter() {
            value = value
                .checked_mul(10)?
                .checked_add(u64::from(digit - b'0'))?;
        }
        Some(value)
    }

    /// Returns the value as [`u128`], or [`None`] if it does not fit.
    pub fn to_u128(&self) -> Option<u128> {
        let mut value: u128 = 0;
        for digit in self.iter() {
            value = value
                .checked_mul(10)?
                .checked_add(u128::from(digit - b'0'))?;
        }
        Some(value)
    }

    /// Returns the value as [`usize`], or [`None`] if it does not fit.
    ///
    /// Whether a value fits depends on the platform.
    pub fn to_usize(&self) -> Option<usize> {
        usize::try_from(self.to_u64()?).ok()
    }
}

impl SmtNumeralBuf {
    /// Converts from [`u32`].
    pub fn from_u32(value: u32) -> Self {
        // the decimal string of an integer is a numeral
        Self(SmtBytesBuf::from_vec(value.to_string().into_bytes()))
    }

    /// Converts from [`u64`].
    pub fn from_u64(value: u64) -> Self {
        // the decimal string of an integer is a numeral
        Self(SmtBytesBuf::from_vec(value.to_string().into_bytes()))
    }

    /// Converts from [`u128`].
    pub fn from_u128(value: u128) -> Self {
        // the decimal string of an integer is a numeral
        Self(SmtBytesBuf::from_vec(value.to_string().into_bytes()))
    }

    /// Converts from [`usize`].
    pub fn from_usize(value: usize) -> Self {
        // the decimal string of an integer is a numeral
        Self(SmtBytesBuf::from_vec(value.to_string().into_bytes()))
    }

    /// Returns the value as [`u32`], or [`None`] if it does not fit.
    pub fn to_u32(&self) -> Option<u32> {
        self.view().to_u32()
    }

    /// Returns the value as [`u64`], or [`None`] if it does not fit.
    pub fn to_u64(&self) -> Option<u64> {
        self.view().to_u64()
    }

    /// Returns the value as [`u128`], or [`None`] if it does not fit.
    pub fn to_u128(&self) -> Option<u128> {
        self.view().to_u128()
    }

    /// Returns the value as [`usize`], or [`None`] if it does not fit.
    ///
    /// Whether a value fits depends on the platform.
    pub fn to_usize(&self) -> Option<usize> {
        self.view().to_usize()
    }
}

/// Defines the fallible conversion of a numeric value, viewed or owned, into an
/// integer type by the method that converts it.
macro_rules! numeric_try_from {
    ($view:ident, $buf:ident, $int:ty, $method:ident) => {
        impl TryFrom<$view<'_>> for $int {
            type Error = SmtNumericOverflowError;

            fn try_from(value: $view<'_>) -> Result<Self, Self::Error> {
                value.$method().ok_or(SmtNumericOverflowError)
            }
        }

        impl TryFrom<&$buf> for $int {
            type Error = SmtNumericOverflowError;

            fn try_from(value: &$buf) -> Result<Self, Self::Error> {
                value.$method().ok_or(SmtNumericOverflowError)
            }
        }
    };
}

numeric_try_from!(SmtNumeral, SmtNumeralBuf, u32, to_u32);
numeric_try_from!(SmtNumeral, SmtNumeralBuf, u64, to_u64);
numeric_try_from!(SmtNumeral, SmtNumeralBuf, u128, to_u128);
numeric_try_from!(SmtNumeral, SmtNumeralBuf, usize, to_usize);
numeric_try_from!(SmtHexDigits, SmtHexDigitsBuf, u32, to_u32);
numeric_try_from!(SmtHexDigits, SmtHexDigitsBuf, u64, to_u64);
numeric_try_from!(SmtHexDigits, SmtHexDigitsBuf, u128, to_u128);
numeric_try_from!(SmtHexDigits, SmtHexDigitsBuf, usize, to_usize);
numeric_try_from!(SmtBinDigits, SmtBinDigitsBuf, u32, to_u32);
numeric_try_from!(SmtBinDigits, SmtBinDigitsBuf, u64, to_u64);
numeric_try_from!(SmtBinDigits, SmtBinDigitsBuf, u128, to_u128);
numeric_try_from!(SmtBinDigits, SmtBinDigitsBuf, usize, to_usize);

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

/// The value of an allowed hexadecimal digit.
fn hex_digit_value(digit: u8) -> u8 {
    match digit {
        b'0'..=b'9' => digit - b'0',
        b'a'..=b'f' => digit - b'a' + 10,
        // only the upper-case letters are left
        _ => digit - b'A' + 10,
    }
}

/// The value of an allowed binary digit.
fn bin_digit_value(digit: u8) -> u8 {
    digit - b'0'
}

/// Defines the conversions of digits of the radix into integers by their value.
macro_rules! digits_to_int {
    ($view:ident, $buf:ident, $radix:literal, $digit_value:ident) => {
        impl $view<'_> {
            /// Returns the value as [`u32`], or [`None`] if it does not fit.
            pub fn to_u32(&self) -> Option<u32> {
                u32::try_from(self.to_u64()?).ok()
            }

            /// Returns the value as [`u64`], or [`None`] if it does not fit.
            pub fn to_u64(&self) -> Option<u64> {
                let mut value: u64 = 0;
                for digit in self.iter() {
                    value = value
                        .checked_mul($radix)?
                        .checked_add(u64::from($digit_value(digit)))?;
                }
                Some(value)
            }

            /// Returns the value as [`u128`], or [`None`] if it does not fit.
            pub fn to_u128(&self) -> Option<u128> {
                let mut value: u128 = 0;
                for digit in self.iter() {
                    value = value
                        .checked_mul($radix)?
                        .checked_add(u128::from($digit_value(digit)))?;
                }
                Some(value)
            }

            /// Returns the value as [`usize`], or [`None`] if it does not fit.
            ///
            /// Whether a value fits depends on the platform.
            pub fn to_usize(&self) -> Option<usize> {
                usize::try_from(self.to_u64()?).ok()
            }
        }

        impl $buf {
            /// Returns the value as [`u32`], or [`None`] if it does not fit.
            pub fn to_u32(&self) -> Option<u32> {
                self.view().to_u32()
            }

            /// Returns the value as [`u64`], or [`None`] if it does not fit.
            pub fn to_u64(&self) -> Option<u64> {
                self.view().to_u64()
            }

            /// Returns the value as [`u128`], or [`None`] if it does not fit.
            pub fn to_u128(&self) -> Option<u128> {
                self.view().to_u128()
            }

            /// Returns the value as [`usize`], or [`None`] if it does not fit.
            ///
            /// Whether a value fits depends on the platform.
            pub fn to_usize(&self) -> Option<usize> {
                self.view().to_usize()
            }
        }
    };
}

digits_to_int!(SmtHexDigits, SmtHexDigitsBuf, 16, hex_digit_value);
digits_to_int!(SmtBinDigits, SmtBinDigitsBuf, 2, bin_digit_value);

impl<'a> SmtDecimal<'a> {
    /// Returns the whole part, before the dot.
    pub fn whole(&self) -> SmtNumeral<'a> {
        SmtNumeral::new_unchecked(&self.0[..self.dot()])
    }

    /// Returns the digits of the fractional part, after the dot.
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
    /// Returns the whole part, before the dot.
    pub fn whole(&self) -> SmtNumeral<'_> {
        self.view().whole()
    }

    /// Returns the digits of the fractional part, after the dot.
    ///
    /// They may have leading zeros, so they are not a numeral.
    pub fn fraction(&self) -> &[u8] {
        self.view().fraction()
    }
}

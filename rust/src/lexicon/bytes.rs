use std::fmt::{Debug, Write};

/// Owned byte content.
///
/// Content of a lexicon value without its kind, e.g. of a symbol without whether it is quoted.
/// It may hold any bytes.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtBytesBuf(Box<[u8]>);

impl SmtBytesBuf {
    /// Creates empty content.
    #[inline]
    pub fn new() -> SmtBytesBuf {
        SmtBytesBuf(Box::new([]))
    }

    /// Converts from a single byte.
    pub fn from_byte(byte: u8) -> Self {
        Self(Box::new([byte]))
    }

    /// Converts from a boxed byte slice.
    pub fn from_boxed_slice(boxed: Box<[u8]>) -> Self {
        Self(boxed)
    }

    /// Converts from a byte vector.
    pub fn from_vec(vec: Vec<u8>) -> Self {
        Self(vec.into_boxed_slice())
    }

    /// Converts into a boxed byte slice.
    pub fn into_boxed_slice(self) -> Box<[u8]> {
        self.0
    }

    /// Converts into a byte vector.
    pub fn into_vec(self) -> Vec<u8> {
        self.0.into_vec()
    }

    /// Returns the length of the content in bytes.
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the content is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the content as a byte slice.
    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        &self.0
    }

    /// Views as [`SmtBytes`].
    #[inline]
    pub fn view<'a>(&'a self) -> SmtBytes<'a> {
        SmtBytes(&self.0)
    }

    /// Returns an iterator over the bytes of the content.
    pub fn iter(&self) -> impl Iterator<Item = u8> {
        self.0.iter().copied()
    }
}

impl std::borrow::Borrow<[u8]> for SmtBytesBuf {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl PartialEq<[u8]> for SmtBytesBuf {
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<SmtBytes<'_>> for SmtBytesBuf {
    fn eq(&self, other: &SmtBytes<'_>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Default for SmtBytesBuf {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for SmtBytesBuf {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.view(), f)
    }
}

/// View of byte content.
///
/// Content of a lexicon value without its kind, e.g. of a symbol without whether it is quoted.
/// It may hold any bytes.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct SmtBytes<'a>(&'a [u8]);

impl<'a> SmtBytes<'a> {
    #[inline]
    pub(crate) fn new(slice: &'a [u8]) -> Self {
        Self(slice)
    }

    /// Returns the length of the content in bytes.
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns `true` if the content is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the content as a byte slice.
    #[inline]
    pub fn as_slice(&self) -> &'a [u8] {
        self.0
    }

    /// Converts into [`SmtBytesBuf`].
    pub fn into_owned(self) -> SmtBytesBuf {
        SmtBytesBuf::from_boxed_slice(self.as_slice().into())
    }

    /// Returns an iterator over the bytes of the content.
    pub fn iter(&self) -> impl Iterator<Item = u8> {
        self.0.iter().copied()
    }
}

impl std::borrow::Borrow<[u8]> for SmtBytes<'_> {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl PartialEq<[u8]> for SmtBytes<'_> {
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<SmtBytesBuf> for SmtBytes<'_> {
    fn eq(&self, other: &SmtBytesBuf) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Debug for SmtBytes<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // print in the manner of Rust str/String,
        // use byte escapes instead of Unicode escapes
        // as we store bytes, not UTF-8
        f.write_char('\"')?;
        for c in self.0.iter().copied() {
            // specially escape the same characters Rust does
            let escape = match c {
                b'\n' => Some("\\n"),
                b'\r' => Some("\\r"),
                b'\t' => Some("\\t"),
                b'\\' => Some("\\\\"),
                b'\0' => Some("\\0"),
                b'\"' => Some("\\\""),
                _ => None,
            };
            if let Some(escape) = escape {
                f.write_str(escape)?;
            } else if (32..127).contains(&c) {
                // not a control byte, DEL, nor non-ASCII
                // print as itself
                f.write_char(c as char)?;
            } else {
                // control byte, DEL, or non-ASCII
                // escape byte
                write!(f, "\\x{:X}{:X}", c / 16, c % 16)?;
            }
        }
        f.write_char('\"')?;
        Ok(())
    }
}

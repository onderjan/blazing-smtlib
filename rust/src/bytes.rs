use std::fmt::{Debug, Write};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct SmtBytes(Vec<u8>);

impl SmtBytes {
    #[inline]
    pub fn new() -> SmtBytes {
        SmtBytes(Vec::new())
    }

    pub fn from_vec(vec: Vec<u8>) -> Self {
        Self(vec)
    }

    pub fn from_byte(byte: u8) -> Self {
        Self::from_vec(vec![byte])
    }

    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        &self.0
    }

    #[inline]
    pub fn as_view<'a>(&'a self) -> SmtBytesView<'a> {
        SmtBytesView(&self.0)
    }

    pub fn into_vec(self) -> Vec<u8> {
        self.0
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn clear(&mut self) {
        self.0.clear();
    }

    #[inline]
    pub fn extend_from_slice(&mut self, slice: &[u8]) {
        self.0.extend_from_slice(slice);
    }

    #[inline]
    pub fn push(&mut self, byte: u8) {
        self.0.push(byte);
    }

    pub fn iter(&self) -> impl Iterator<Item = u8> {
        self.0.iter().copied()
    }
}

impl std::borrow::Borrow<[u8]> for SmtBytes {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl PartialEq<[u8]> for SmtBytes {
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<SmtBytesView<'_>> for SmtBytes {
    fn eq(&self, other: &SmtBytesView<'_>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Default for SmtBytes {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for SmtBytes {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.as_view(), f)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct SmtBytesView<'a>(&'a [u8]);

impl<'a> SmtBytesView<'a> {
    #[inline]
    pub(crate) fn new(slice: &'a [u8]) -> Self {
        Self(slice)
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn as_slice(self) -> &'a [u8] {
        self.0
    }

    pub fn into_owned(self) -> SmtBytes {
        SmtBytes::from_vec(self.as_slice().to_vec())
    }

    pub fn iter(&self) -> impl Iterator<Item = u8> {
        self.0.iter().copied()
    }
}

impl std::borrow::Borrow<[u8]> for SmtBytesView<'_> {
    fn borrow(&self) -> &[u8] {
        self.as_slice()
    }
}

impl PartialEq<[u8]> for SmtBytesView<'_> {
    fn eq(&self, other: &[u8]) -> bool {
        self.as_slice() == other
    }
}

impl PartialEq<SmtBytes> for SmtBytesView<'_> {
    fn eq(&self, other: &SmtBytes) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl Debug for SmtBytesView<'_> {
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

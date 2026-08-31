use std::fmt::{Debug, Write};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct String8(Vec<u8>);

impl String8 {
    pub fn new() -> String8 {
        String8(Vec::new())
    }

    pub fn from_vec(vec: Vec<u8>) -> Self {
        Self(vec)
    }

    pub fn from_byte(byte: u8) -> Self {
        Self::from_vec(vec![byte])
    }

    pub fn as_slice(&self) -> &[u8] {
        &self.0
    }

    pub fn as_view<'a>(&'a self) -> String8View<'a> {
        String8View(&self.0)
    }

    pub fn into_vec(self) -> Vec<u8> {
        self.0
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn clear(&mut self) {
        self.0.clear();
    }

    pub fn push(&mut self, byte: u8) {
        self.0.push(byte);
    }

    pub fn iter(&self) -> impl Iterator<Item = u8> {
        self.0.iter().copied()
    }
}

impl Default for String8 {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for String8 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.as_view(), f)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct String8View<'a>(&'a [u8]);

impl<'a> String8View<'a> {
    pub fn as_slice(self) -> &'a [u8] {
        self.0
    }
}

impl Debug for String8View<'_> {
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

use std::fmt::{Debug, Write};

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct String8(pub Vec<u8>);

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Str8<'a>(pub &'a [u8]);

impl String8 {
    pub fn new() -> String8 {
        String8(Vec::new())
    }

    pub fn bytes(&self) -> &[u8] {
        &self.0
    }

    pub fn as_str<'a>(&'a self) -> Str8<'a> {
        Str8(&self.0)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Default for String8 {
    fn default() -> Self {
        Self::new()
    }
}

impl Debug for String8 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.as_str(), f)
    }
}

impl Str8<'_> {
    pub fn bytes(&self) -> &[u8] {
        self.0
    }
}

impl Debug for Str8<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_char('\"')?;
        for c in self.0.iter().copied() {
            if c < 128 {
                f.write_char(c as char)?;
            } else {
                write!(f, "\\b{:X}{:X}", c / 16, c % 16)?;
            }
        }
        f.write_char('\"')?;
        Ok(())
    }
}

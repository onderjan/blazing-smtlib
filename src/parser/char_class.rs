#[derive(Clone, Copy)]
pub enum CharClass {
    /// any non-printable character except for TAB, LF, CR
    /// meaning from 0 to 32 except for those ones + 127 (DEL)
    OtherNonPrintable,
    /// TAB (9)
    Tab,
    /// LF (10) / CR (13)
    LineBreak,
    /// ' ' (32)
    Space,
    /// '"' (34)
    DoubleQuote,
    /// '#' (35)
    Hash,
    /// '(' (40)
    ParenOpen,
    /// ')' (41)
    ParenClose,
    /// '.' (45), this is also allowed in symbols
    Dot,
    /// ':' (58)
    Colon,
    /// ';' (59)
    Semicolon,
    /// '0'-'9' (48-57)
    Digit,
    /// 'A'-'Z' (65-90) or 'a'-'z' (97-122)
    Letter,
    /// '\' (92)
    Backslash,
    /// '|' (124)
    Pipe,
    /// not letters or digits or dot but allowed in symbols (all ASCII printable)
    Special,
    /// not in any interesting category but from 32 to 126
    OtherAsciiPrintable,
    /// any character greater or equal to 128
    NonAscii,
}

impl From<u8> for CharClass {
    fn from(c: u8) -> Self {
        if c.is_ascii_alphabetic() {
            CharClass::Letter
        } else if c.is_ascii_digit() {
            CharClass::Digit
        } else if c >= 128 {
            CharClass::NonAscii
        } else {
            match c {
                b'\t' => CharClass::Tab,
                b'\r' | b'\n' => CharClass::LineBreak,
                b' ' => CharClass::Space,
                b'#' => CharClass::Hash,
                b'"' => CharClass::DoubleQuote,
                b'(' => CharClass::ParenOpen,
                b')' => CharClass::ParenClose,
                b'.' => CharClass::Dot,
                b':' => CharClass::Colon,
                b';' => CharClass::Semicolon,
                b'\\' => CharClass::Backslash,
                b'|' => CharClass::Pipe,
                b'~' | b'!' | b'@' | b'$' | b'%' | b'^' | b'&' | b'*' | b'_' | b'-' | b'+'
                | b'=' | b'<' | b'>' | b'?' | b'/' => CharClass::Special,
                _ => {
                    // below 128 and not in any interesting class
                    if c < 32 {
                        CharClass::OtherNonPrintable
                    } else {
                        CharClass::OtherAsciiPrintable
                    }
                }
            }
        }
    }
}

#[derive(Clone, Copy)]
pub enum U8OrEof {
    U8(u8),
    Eof,
}

pub fn char_class_opt(c: U8OrEof) -> Option<(CharClass, u8)> {
    match c {
        U8OrEof::U8(c) => Some((CharClass::from(c), c)),
        U8OrEof::Eof => None,
    }
}

impl CharClass {
    pub fn is_printable_or_whitespace(self) -> bool {
        // everything except other non-printable
        !matches!(self, CharClass::OtherNonPrintable)
    }
}

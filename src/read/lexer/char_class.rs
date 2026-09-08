/// Class of a character following the SMT-LIB standard.
///
/// In SMT-LIB, the characters are encoded in 8-bit bytes,
/// with the bytes 0..=127 denoting US-ASCII characters.
/// The meaning of values 128..=255 is not lexically defined
/// but all are considered printable non-whitespace characters.
///
/// 'Non-printable' characters are US-ASCII control characters:
/// those with byte codes 0..=31 and 127 (DEL).
/// 'Printable' characters have byte codes 32..=126 and 128..=255.
///
/// 'Whitespace' characters are only TAB (9), LF (10), CR (13), SPACE (32).
/// 'Non-whitespace' characters are all the others.
///
/// Specially, 32 (SPACE) is both printable and whitespace.
/// 0..=31 except (9, 10, 13) and 127 (DEL) are neither printable nor whitespace.
#[derive(Clone, Copy)]
pub(crate) enum CharClass {
    /// any non-printable character except for TAB, LF, CR, and DEL
    /// meaning 0..=31 except (9, 10, 13)
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
    /// '.' (46), this is also allowed in symbols
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
    /// DEL (127)
    Del,
    /// not letters or digits or dot but allowed in symbols (all ASCII printable)
    Special,
    /// not in any interesting category, code in 33..=126
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
                127 => CharClass::Del,
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
pub(super) enum U8OrEof {
    U8(u8),
    Eof,
}

impl CharClass {
    pub fn is_printable_or_whitespace(self) -> bool {
        // everything except other non-printable and DEL
        !matches!(self, CharClass::OtherNonPrintable | CharClass::Del)
    }

    pub fn is_allowed_in_simple_symbol(self) -> bool {
        // letters, digits, special, dot
        matches!(
            self,
            CharClass::Letter | CharClass::Digit | CharClass::Special | CharClass::Dot
        )
    }
}

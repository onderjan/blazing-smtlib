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

impl CharClass {
    const fn classify(c: u8) -> Self {
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

    #[inline]
    pub const fn is_printable_or_whitespace(self) -> bool {
        // everything except other non-printable and DEL
        !matches!(self, CharClass::OtherNonPrintable | CharClass::Del)
    }

    #[inline]
    pub const fn is_allowed_in_simple_symbol(self) -> bool {
        // letters, digits, special, dot
        matches!(
            self,
            CharClass::Letter | CharClass::Digit | CharClass::Special | CharClass::Dot
        )
    }

    const fn flags(c: u8) -> u8 {
        let class = Self::classify(c);
        let mut flags = 0;
        if class.is_allowed_in_simple_symbol() {
            flags |= SIMPLE_SYMBOL;
        }
        if matches!(class, CharClass::Digit) {
            flags |= DIGIT;
        }
        // Letter does not separate a-f from the rest
        if matches!(class, CharClass::Digit) || matches!(c, b'a'..=b'f' | b'A'..=b'F') {
            flags |= HEX_DIGIT;
        }
        if matches!(c, b'0' | b'1') {
            flags |= BINARY_DIGIT;
        }
        if matches!(
            class,
            CharClass::Tab | CharClass::Space | CharClass::LineBreak
        ) && c != b'\n'
        {
            flags |= NON_LF_WHITESPACE;
        }
        // LineBreak covers CR too, and CR is plain inside strings and quoted symbols;
        // only LF ends the run (it has to be marked before the scan continues)
        let plain_text = class.is_printable_or_whitespace() && c != b'\n';
        if plain_text && !matches!(class, CharClass::Pipe | CharClass::Backslash) {
            flags |= QUOTED_PLAIN;
        }
        if plain_text && !matches!(class, CharClass::DoubleQuote) {
            flags |= STRING_PLAIN;
        }
        if !matches!(class, CharClass::LineBreak) {
            flags |= COMMENT_PLAIN;
        }
        flags
    }
}

impl From<u8> for CharClass {
    #[inline]
    fn from(c: u8) -> Self {
        Self::classify(c)
    }
}

pub(super) const SIMPLE_SYMBOL: u8 = 1u8 << 0;
pub(super) const DIGIT: u8 = 1u8 << 1;
pub(super) const HEX_DIGIT: u8 = 1u8 << 2;
pub(super) const BINARY_DIGIT: u8 = 1u8 << 3;
pub(super) const NON_LF_WHITESPACE: u8 = 1u8 << 4;
pub(super) const QUOTED_PLAIN: u8 = 1u8 << 5;
pub(super) const STRING_PLAIN: u8 = 1u8 << 6;
pub(super) const COMMENT_PLAIN: u8 = 1u8 << 7;

pub(super) static FLAGS: [u8; 256] = {
    let mut table = [0u8; 256];
    let mut i = 0;
    while i < 256 {
        table[i] = CharClass::flags(i as u8);
        i += 1;
    }
    table
};

#[inline]
pub(super) fn run_end(slice: &[u8], mask: u8) -> usize {
    // the run is over bytes which have at least one mask flag set
    // return the byte that ends the run or slice length if there is none
    slice
        .iter()
        .position(|c| FLAGS[*c as usize] & mask == 0)
        .unwrap_or(slice.len())
}

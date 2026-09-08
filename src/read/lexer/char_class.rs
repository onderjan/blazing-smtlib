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

#[cfg(test)]
mod tests {
    use super::*;

    const ALL_FLAGS: [(&str, u8); 8] = [
        ("SIMPLE_SYMBOL", SIMPLE_SYMBOL),
        ("DIGIT", DIGIT),
        ("HEX_DIGIT", HEX_DIGIT),
        ("BINARY_DIGIT", BINARY_DIGIT),
        ("NON_LF_WHITESPACE", NON_LF_WHITESPACE),
        ("QUOTED_PLAIN", QUOTED_PLAIN),
        ("STRING_PLAIN", STRING_PLAIN),
        ("COMMENT_PLAIN", COMMENT_PLAIN),
    ];

    /// The flag definitions written out longhand, independently of `CharClass`.
    fn expected_flags(c: u8) -> u8 {
        let special = b"~!@$%^&*_-+=<>?/".contains(&c);
        let simple_symbol = c.is_ascii_alphanumeric() || special || c == b'.';
        let non_printable = (c < 32 && !matches!(c, b'\t' | b'\n' | b'\r')) || c == 127;
        let printable_or_whitespace = !non_printable;
        let mut flags = 0;
        if simple_symbol {
            flags |= SIMPLE_SYMBOL;
        }
        if c.is_ascii_digit() {
            flags |= DIGIT;
        }
        if c.is_ascii_hexdigit() {
            flags |= HEX_DIGIT;
        }
        if c == b'0' || c == b'1' {
            flags |= BINARY_DIGIT;
        }
        if matches!(c, b' ' | b'\t' | b'\r') {
            flags |= NON_LF_WHITESPACE;
        }
        if printable_or_whitespace && !matches!(c, b'|' | b'\\' | b'\n') {
            flags |= QUOTED_PLAIN;
        }
        if printable_or_whitespace && !matches!(c, b'"' | b'\n') {
            flags |= STRING_PLAIN;
        }
        if !matches!(c, b'\n' | b'\r') {
            flags |= COMMENT_PLAIN;
        }
        flags
    }

    #[test]
    fn every_flag_matches_its_definition_for_every_byte() {
        for c in 0..=255u8 {
            for (name, flag) in ALL_FLAGS {
                assert_eq!(
                    FLAGS[c as usize] & flag != 0,
                    expected_flags(c) & flag != 0,
                    "{name} for byte {c:#04x} ({:?})",
                    c as char
                );
            }
        }
    }

    #[test]
    fn line_feed_continues_no_run_that_needs_it_marked() {
        // every scanner that can pass a line feed must see it end the run,
        // otherwise the line bookkeeping would miss it
        for (name, flag) in ALL_FLAGS {
            assert_eq!(
                FLAGS[b'\n' as usize] & flag,
                0,
                "{name} must not continue over a line feed"
            );
        }
    }

    /// The one-line reference `run_end` is checked against.
    fn reference_run_end(slice: &[u8], mask: u8) -> usize {
        slice
            .iter()
            .position(|c| FLAGS[*c as usize] & mask == 0)
            .unwrap_or(slice.len())
    }

    /// A byte that continues the run for the flag, and one that ends it
    /// while carrying as many other flags as possible.
    fn run_and_terminator_bytes(flag: u8) -> (u8, Vec<u8>) {
        let run_byte = (0..=255u8)
            .find(|&c| FLAGS[c as usize] & flag != 0)
            .expect("every flag has at least one byte");
        // all terminators for the flag, so that terminators which continue
        // other runs (a hex letter ending a decimal-digit run) are included
        let terminators: Vec<u8> = (0..=255u8)
            .filter(|&c| FLAGS[c as usize] & flag == 0)
            .collect();
        (run_byte, terminators)
    }

    #[test]
    fn run_end_matches_the_reference_for_every_length_prefix_and_terminator() {
        // lengths around 16- and 32-byte scanning windows, with the run
        // starting at every alignment within a window, so that a chunked
        // scan has to get every boundary right
        for (name, flag) in ALL_FLAGS {
            let (run_byte, terminators) = run_and_terminator_bytes(flag);
            for prefix in 0..4usize {
                for run_length in 0..=70usize {
                    let mut data = vec![b'('; prefix];
                    data.extend(std::iter::repeat_n(run_byte, run_length));
                    // no terminator: the run reaches the end of the slice
                    assert_eq!(
                        run_end(&data[prefix..], flag),
                        run_length,
                        "{name}: prefix {prefix}, run {run_length}, no terminator"
                    );
                    // every possible terminator, followed by more run bytes
                    // that must not be reached
                    for &terminator in &terminators {
                        let mut with_terminator = data.clone();
                        with_terminator.push(terminator);
                        with_terminator.extend(std::iter::repeat_n(run_byte, 40));
                        let slice = &with_terminator[prefix..];
                        assert_eq!(
                            run_end(slice, flag),
                            run_length,
                            "{name}: prefix {prefix}, run {run_length}, terminator {terminator:#04x}"
                        );
                        assert_eq!(run_end(slice, flag), reference_run_end(slice, flag));
                    }
                }
            }
        }
    }

    #[test]
    fn run_end_on_an_empty_slice_is_zero() {
        for (_, flag) in ALL_FLAGS {
            assert_eq!(run_end(&[], flag), 0);
        }
    }

    #[test]
    fn run_end_stops_at_the_slice_end_not_at_the_allocation_end() {
        // the bytes after the slice would continue or end the run differently;
        // scanning must never look at them
        for (name, flag) in ALL_FLAGS {
            let (run_byte, terminators) = run_and_terminator_bytes(flag);
            let terminator = terminators[0];
            for run_length in 0..=70usize {
                let mut buffer = vec![run_byte; run_length];
                // beyond the slice: first a terminator, then run bytes
                buffer.push(terminator);
                buffer.extend(std::iter::repeat_n(run_byte, 64));
                assert_eq!(
                    run_end(&buffer[..run_length], flag),
                    run_length,
                    "{name}: run {run_length} followed by a terminator outside the slice"
                );
                // beyond the slice: run bytes only
                let mut buffer = vec![run_byte; run_length + 64];
                buffer[run_length] = run_byte;
                assert_eq!(
                    run_end(&buffer[..run_length], flag),
                    run_length,
                    "{name}: run {run_length} followed by run bytes outside the slice"
                );
            }
        }
    }
}

//! Locations and spans in a byte stream, used in lexer tokens and errors.
//!
//! A location records an offset in bytes and line/column information, and a
//! span is a half-open range `[start, end)` between locations. The span can be
//! empty, which is usually the case if an error occured at the end of input due
//! to some unclosed item.
//!
//! The locations and spans are given by the [lexer](crate::lexer) for tokens
//! via [SmtLexerToken::span](crate::lexer::SmtLexerToken::span). Lexing and
//! reading produces the result value wrapped in [SmtLocated] on success and a
//! spanned error on failure. Parsers and handlers do not interact with
//! locations and spans.

/// Location in a byte stream.
///
/// All counts are in bytes. While SMT-LIB accepts both CR and LF as a comment
/// separator, we consider only LF to start a new line for location purposes as
/// that is compatible with both LF and CRLF conventions.
///
/// The offset, line, and column all start at zero, but are formatted one-based
/// using [Display](std::fmt::Display).
///
/// The location is guaranteed to be valid with respect to the offset and
/// line/column: as each terminated line must contain at least one byte (LF),
/// the offset must be equal to or greater than the sum of line and column.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct SmtLocation {
    /// Zero-based byte offset from the start of the stream.
    offset: u64,
    /// Zero-based line number.
    line: u64,
    /// Zero-based column number, measured in bytes.
    column: u64,
}

/// Error constructing a location that would be invalid.
///
/// See [SmtLocation] for the validity condition.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SmtInvalidLocationError;

impl std::fmt::Display for SmtInvalidLocationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("invalid location")
    }
}

impl std::error::Error for SmtInvalidLocationError {}

impl SmtLocation {
    #[inline]
    pub fn new(offset: u64, line: u64, column: u64) -> Result<Self, SmtInvalidLocationError> {
        if Self::is_allowed(offset, line, column) {
            Ok(Self {
                offset,
                line,
                column,
            })
        } else {
            Err(SmtInvalidLocationError)
        }
    }

    #[inline]
    pub(crate) fn new_unchecked(offset: u64, line: u64, column: u64) -> Self {
        debug_assert!(
            Self::is_allowed(offset, line, column),
            "inconsistent location at offset {offset}, line {line}, column {column}"
        );
        Self {
            offset,
            line,
            column,
        }
    }

    fn is_allowed(offset: u64, line: u64, column: u64) -> bool {
        // each terminated line ends with a line feed,
        // so it must consist of at least one byte,
        // and each column is an additional byte
        line.checked_add(column)
            .is_some_and(|bytes| bytes <= offset)
    }

    /// Zero-based byte offset.
    pub fn offset(&self) -> u64 {
        self.offset
    }

    /// Zero-based line number.
    pub fn line(&self) -> u64 {
        self.line
    }

    /// Zero-based column number, measured in bytes.
    pub fn column(&self) -> u64 {
        self.column
    }

    /// Location directly at the byte stream start.
    #[inline]
    pub fn initial() -> Self {
        Self {
            offset: 0,
            line: 0,
            column: 0,
        }
    }

    #[inline]
    pub fn after_byte(self, c: u8) -> Self {
        if c == b'\n' {
            Self {
                offset: self.next_offset(),
                line: self.line + 1,
                column: 0,
            }
        } else {
            self.after_column()
        }
    }

    #[inline]
    pub fn after_column(self) -> Self {
        Self {
            offset: self.next_offset(),
            line: self.line,
            column: self.column + 1,
        }
    }

    /// The offset of the next byte; the line and the column cannot overflow
    /// where it does not, as neither exceeds the offset.
    #[inline]
    fn next_offset(self) -> u64 {
        self.offset
            .checked_add(1)
            .expect("location offset must not overflow")
    }
}

/// Value located in a byte stream.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SmtLocated<V> {
    value: V,
    location: SmtLocation,
}

impl<V> SmtLocated<V> {
    #[inline]
    pub(crate) fn new(value: V, location: SmtLocation) -> Self {
        Self { value, location }
    }

    /// Returns a reference to the value.
    pub fn value(&self) -> &V {
        &self.value
    }

    /// Returns the location.
    pub fn location(&self) -> SmtLocation {
        self.location
    }

    /// Destructures into the value.
    pub fn into_value(self) -> V {
        self.value
    }
}

/// Span of an item in a byte stream.
///
/// The span is a half-open range `[start, end)` between locations.
///
/// The span is guaranteed to be valid with respect to the offsets and
/// line/column of its locations: the end is not before the start, and the bytes
/// between them hold what separates them. On the same line, the column advances
/// by exactly the number of bytes. On a later line, each line ended takes at
/// least one byte (LF), and each column before the end takes one byte.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct SmtSpan {
    start: SmtLocation,
    end: SmtLocation,
}

/// Error constructing a span that would be invalid.
///
/// See [SmtSpan] for the validity condition.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SmtInvalidSpanError;

impl std::fmt::Display for SmtInvalidSpanError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("invalid span")
    }
}

impl std::error::Error for SmtInvalidSpanError {}

impl SmtSpan {
    #[inline]
    pub fn new(start: SmtLocation, end: SmtLocation) -> Result<Self, SmtInvalidSpanError> {
        if Self::is_allowed(start, end) {
            Ok(Self { start, end })
        } else {
            Err(SmtInvalidSpanError)
        }
    }

    #[inline]
    pub(crate) fn new_unchecked(start: SmtLocation, end: SmtLocation) -> Self {
        debug_assert!(
            Self::is_allowed(start, end),
            "inconsistent span with start {start:?} and end {end:?}"
        );
        Self { start, end }
    }

    fn is_allowed(start: SmtLocation, end: SmtLocation) -> bool {
        // end offset must be greater than or equal to the start offset,
        // retain the difference
        let Some(difference) = end.offset.checked_sub(start.offset) else {
            return false;
        };
        match end.line.cmp(&start.line) {
            std::cmp::Ordering::Less => {
                // end line must not be less than start line
                false
            }
            std::cmp::Ordering::Equal => {
                // same line
                // the column difference must be exactly the byte difference
                end.column.checked_sub(start.column) == Some(difference)
            }
            std::cmp::Ordering::Greater => {
                // Compute the minimal possible difference that is implied by
                // line/column information: each terminated line is at least 1
                // byte (LF) and each column of the end line is 1 byte.
                // The computation cannot overflow as we know
                // start.line < end.line and end.line + end.column <= end.offset.
                let min_implied_difference = (end.line - start.line) + end.column;
                min_implied_difference <= difference
            }
        }
    }

    /// A span within one line: the line, the offset of its start, and the
    /// offsets of the span on it.
    #[inline]
    pub(crate) fn on_line(line: u64, line_start: u64, start: u64, end: u64) -> Self {
        debug_assert!(start <= end, "span start {start} is after end {end}");
        Self {
            start: SmtLocation::new_unchecked(start, line, start - line_start),
            end: SmtLocation::new_unchecked(end, line, end - line_start),
        }
    }

    #[inline]
    pub(crate) fn new_empty(location: SmtLocation) -> Self {
        Self {
            start: location,
            end: location,
        }
    }

    pub(crate) fn new_zero() -> Self {
        Self::new_empty(SmtLocation::initial())
    }

    pub fn start(&self) -> SmtLocation {
        self.start
    }
    pub fn end(&self) -> SmtLocation {
        self.end
    }

    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A location as `(offset, line, column)`.
    type Loc = (u64, u64, u64);

    fn loc(location: SmtLocation) -> Loc {
        (location.offset(), location.line(), location.column())
    }

    /// The location reached after consuming the whole input.
    fn location_after(input: &[u8]) -> SmtLocation {
        input.iter().fold(SmtLocation::initial(), |location, &c| {
            location.after_byte(c)
        })
    }

    /// The span between the locations reached after consuming each of the inputs.
    fn span_between(start: &[u8], end: &[u8]) -> SmtSpan {
        SmtSpan::new_unchecked(location_after(start), location_after(end))
    }

    #[test]
    fn initial_location_is_the_stream_start() {
        assert_eq!(loc(SmtLocation::initial()), (0, 0, 0));
        assert_eq!(loc(location_after(b"")), (0, 0, 0));
    }

    #[test]
    fn a_line_feed_starts_a_new_line_and_other_bytes_advance_the_column() {
        assert_eq!(loc(location_after(b"a")), (1, 0, 1));
        assert_eq!(loc(location_after(b"abc")), (3, 0, 3));
        // the line feed itself is the last byte of the line it ends
        assert_eq!(loc(location_after(b"abc\n")), (4, 1, 0));
        assert_eq!(loc(location_after(b"abc\nde")), (6, 1, 2));
        // consecutive line feeds each start a line of their own
        assert_eq!(loc(location_after(b"\n\n")), (2, 2, 0));
    }

    #[test]
    fn only_a_line_feed_starts_a_new_line() {
        // a carriage return is an ordinary byte, so CRLF counts as one line break
        assert_eq!(loc(location_after(b"a\r")), (2, 0, 2));
        assert_eq!(loc(location_after(b"a\r\n")), (3, 1, 0));
        // so is a tab, even though it is whitespace
        assert_eq!(loc(location_after(b"a\tb")), (3, 0, 3));
    }

    #[test]
    fn after_column_advances_without_ending_the_line() {
        let location = location_after(b"abc\nd").after_column();
        assert_eq!(loc(location), (6, 1, 2));
    }

    #[test]
    fn is_empty_holds_exactly_for_zero_width_spans() {
        assert!(SmtSpan::new_empty(location_after(b"ab")).is_empty());
        assert!(SmtSpan::new_zero().is_empty());
        assert_eq!(loc(SmtSpan::new_zero().start()), (0, 0, 0));
        // a span of a single byte is not empty
        assert!(!span_between(b"a", b"ab").is_empty());
    }

    #[test]
    fn locations_are_ordered_by_offset() {
        let early = location_after(b"a");
        let late = location_after(b"abc");
        assert_eq!(early.min(late), early);
        assert_eq!(late.min(early), early);
        assert_eq!(early.max(late), late);
        assert_eq!(late.max(early), late);
    }
}

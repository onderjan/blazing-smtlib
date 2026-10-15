/// A location in an SMT-LIB stream.
///
/// All counts are in bytes (SMT-LIB works on bytes).
/// While SMT-LIB accepts both CR and LF as a comment separator,
/// we consider only LF to start a new line for location purposes
/// as that is compatible with both LF and CRLF conventions.
///
/// The offset, line, and column all start at zero.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct SmtLocation {
    /// Zero-based byte offset from the start of the stream.
    offset: u64,
    /// Zero-based line number.
    line: u64,
    /// Zero-based column number, measured in bytes.
    column: u64,
}

/// The line and column cannot be at the offset: every line before
/// and every column on the line take at least one byte.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SmtInvalidLocation;

impl SmtLocation {
    #[inline]
    pub fn new(offset: u64, line: u64, column: u64) -> Result<Self, SmtInvalidLocation> {
        if Self::is_allowed(offset, line, column) {
            Ok(Self {
                offset,
                line,
                column,
            })
        } else {
            Err(SmtInvalidLocation)
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
        // each line before ends with a line feed, each column is a byte
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
                offset: self.offset + 1,
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
            offset: self.offset + 1,
            line: self.line,
            column: self.column + 1,
        }
    }
}

/// A value located in an SMT-LIB stream.
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

/// Span of an SMT-LIB element.
///
/// The span is a half-open range `[start, end)` between locations.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct SmtSpan {
    start: SmtLocation,
    end: SmtLocation,
}

/// The end location is not at or after the start location.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SmtInvalidSpan;

impl SmtSpan {
    #[inline]
    pub fn new(start: SmtLocation, end: SmtLocation) -> Result<Self, SmtInvalidSpan> {
        if Self::is_allowed(start, end) {
            Ok(Self { start, end })
        } else {
            Err(SmtInvalidSpan)
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
        // both offsets and line/column information must be consistent
        if end.offset < start.offset {
            return false;
        }
        match end.line.cmp(&start.line) {
            std::cmp::Ordering::Less => false,
            std::cmp::Ordering::Equal => start.column <= end.column,
            std::cmp::Ordering::Greater => true,
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

    pub fn start(self) -> SmtLocation {
        self.start
    }
    pub fn end(self) -> SmtLocation {
        self.end
    }

    pub fn is_empty(self) -> bool {
        self.start == self.end
    }

    pub fn join(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
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
    fn join_takes_the_earlier_start_and_the_later_end() {
        let first = span_between(b"", b"ab");
        let second = span_between(b"ab\nc", b"ab\ncde");
        let joined = first.join(second);

        assert_eq!(loc(joined.start()), (0, 0, 0));
        assert_eq!(loc(joined.end()), (6, 1, 3));
        // the order of the operands does not matter
        assert_eq!(second.join(first), joined);
        // joining a span with itself changes nothing
        assert_eq!(first.join(first), first);
    }

    #[test]
    fn join_with_a_contained_span_is_the_containing_one() {
        let outer = span_between(b"", b"ab\ncde");
        let inner = span_between(b"ab", b"ab\nc");
        assert_eq!(outer.join(inner), outer);
        assert_eq!(inner.join(outer), outer);
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

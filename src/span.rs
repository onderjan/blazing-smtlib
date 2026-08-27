/// A location in an SMT-LIB stream.
///
/// All counts are in bytes (SMT-LIB works on bytes).
/// While SMT-LIB accepts both CR and LF as a comment separator,
/// we consider only LF to start a new line for location purposes
/// as that is compatible with both LF and CRLF conventions.
///
/// The offset starts at zero.
/// Line and column start at one as usual.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SmtLocation {
    /// Zero-based byte offset from the start of the stream.
    offset: u64,
    /// One-based line number, measured in bytes.
    line: u64,
    /// One-based column number, measured in bytes.
    column: u64,
}

impl SmtLocation {
    /// Zero-based byte offset.
    pub fn offset(&self) -> u64 {
        self.offset
    }

    /// One-based line number.
    pub fn line(&self) -> u64 {
        self.line
    }

    /// One-based column number, measured in bytes.
    pub fn column(&self) -> u64 {
        self.column
    }

    pub fn min(self, other: Self) -> Self {
        if self.offset <= other.offset {
            self
        } else {
            other
        }
    }

    pub fn max(self, other: Self) -> Self {
        if self.offset >= other.offset {
            self
        } else {
            other
        }
    }

    /// Location directly at the byte stream start.
    pub(crate) fn initial() -> Self {
        Self {
            offset: 0,
            line: 1,
            column: 1,
        }
    }

    pub(crate) fn after_byte(self, c: u8) -> Self {
        if c == b'\n' {
            Self {
                offset: self.offset + 1,
                line: self.line + 1,
                column: 1,
            }
        } else {
            self.after_column()
        }
    }

    pub(crate) fn after_column(self) -> Self {
        Self {
            offset: self.offset + 1,
            line: self.line,
            column: self.column + 1,
        }
    }
}

/// Span of an SMT-LIB element.
///
/// The span is a half-open range `[start, end)` between locations.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SmtSpan {
    start: SmtLocation,
    end: SmtLocation,
}

impl SmtSpan {
    pub(crate) fn new_unchecked(start: SmtLocation, end: SmtLocation) -> Self {
        debug_assert!(
            start.offset <= end.offset,
            "span start {start:?} is after end {end:?}"
        );
        Self { start, end }
    }

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

/// A location in an SMT-LIB input / file.
///
/// The offset starts at zero.
/// Line and column start at one as usual.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SmtLocation {
    /// Zero-based byte offset.
    offset: u64,
    /// One-based line number.
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
}

/// Span of an SMT-LIB element, measured in bytes.
///
/// The span is a half-open byte range `[start, end)`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub(crate) struct SmtSpan {
    start: u64,
    end: u64,
}

impl SmtSpan {
    pub(crate) fn new_unchecked(start: u64, end: u64) -> Self {
        debug_assert!(start <= end, "span start {start} is after end {end}");
        Self { start, end }
    }

    pub(crate) fn new_exact(offset: u64) -> Self {
        Self {
            start: offset,
            end: offset,
        }
    }

    pub fn start(self) -> u64 {
        self.start
    }
    pub fn end(self) -> u64 {
        self.end
    }
    pub fn len(self) -> u64 {
        self.end - self.start
    }
    pub fn is_empty(self) -> bool {
        self.start == self.end
    }

    pub(crate) fn join(self, other: Self) -> Self {
        Self {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
        }
    }
}

pub(crate) struct LineIndex {
    // Offsets where lines start, must be sorted.
    line_starts: Vec<u64>,
}

impl LineIndex {
    pub fn new() -> Self {
        Self {
            line_starts: vec![0],
        }
    }

    /// Adds a new line.
    ///
    /// This should be called exactly every LF (10). Never on CR (13).
    /// This keeps the line count correct for both LF and CRLF line endings.
    pub(crate) fn add_newline(&mut self, line_feed_offset: u64) {
        let line_start = line_feed_offset + 1;
        // The current line start offset must be larger than the previous one
        // so that the line starts remain sorted.
        debug_assert!(
            self.line_starts
                .last()
                .is_some_and(|last_line_start| line_start > *last_line_start)
        );
        self.line_starts.push(line_start);
    }

    pub fn resolve(&self, offset: u64) -> SmtLocation {
        // If the binary search returns Err, it gives a location to insert
        // while maintaining sortedness.
        // As `line_starts` is always non-empty with the first offset 0,
        // Err(0) is never returned and the subtraction never overflows.
        let line_index = self
            .line_starts
            .binary_search(&offset)
            .unwrap_or_else(|i| i - 1);
        SmtLocation {
            offset,
            line: line_index as u64 + 1,
            column: offset - self.line_starts[line_index] + 1,
        }
    }
}

//! Public-API tests of locations and spans: the consistency their
//! constructors check, their order, the join of spans, and that a location
//! does not advance past the last offset.
//!
//! They check the Rust interface itself and call the library directly.

use blazing_smtlib::span::{SmtInvalidLocationError, SmtInvalidSpanError, SmtLocation, SmtSpan};

fn location(offset: u64, line: u64, column: u64) -> SmtLocation {
    SmtLocation::new(offset, line, column).unwrap_or_else(|_| {
        panic!("location at offset {offset}, line {line}, column {column} should be consistent")
    })
}

fn span(start: SmtLocation, end: SmtLocation) -> SmtSpan {
    SmtSpan::new(start, end)
        .unwrap_or_else(|_| panic!("span from {start:?} to {end:?} should be consistent"))
}

#[test]
fn a_location_is_consistent_exactly_when_its_lines_and_columns_fit_before_its_offset() {
    // every line before the location ends with a line feed and every column
    // before it on its line is a byte, so they cannot add up beyond the offset
    for (offset, line, column) in [
        (0, 0, 0),
        (1, 0, 1),
        (1, 1, 0),
        (5, 2, 3),
        (5, 0, 0),
        (5, 5, 0),
        (5, 0, 5),
        (u64::MAX, 0, u64::MAX),
        (u64::MAX, u64::MAX, 0),
        (u64::MAX, u64::MAX - 1, 1),
    ] {
        let built = SmtLocation::new(offset, line, column).unwrap_or_else(|_| {
            panic!("offset {offset}, line {line}, column {column} should be consistent")
        });
        assert_eq!(
            (built.offset(), built.line(), built.column()),
            (offset, line, column)
        );
    }
    for (offset, line, column) in [
        (0, 0, 1),
        (0, 1, 0),
        (5, 3, 3),
        (5, 6, 0),
        (5, 0, 6),
        // the sum of line and column overflows rather than fitting
        (u64::MAX, u64::MAX, 1),
        (u64::MAX, 1, u64::MAX),
        (u64::MAX, u64::MAX, u64::MAX),
    ] {
        assert_eq!(
            SmtLocation::new(offset, line, column),
            Err(SmtInvalidLocationError),
            "offset {offset}, line {line}, column {column}"
        );
    }
}

#[test]
fn a_span_must_not_end_before_it_starts() {
    let start = location(10, 2, 3);
    // empty, within a line, and across lines
    for end in [
        location(10, 2, 3),
        location(12, 2, 5),
        location(15, 3, 0),
        location(40, 9, 1),
    ] {
        let built = span(start, end);
        assert_eq!((built.start(), built.end()), (start, end));
        assert_eq!(built.is_empty(), start == end);
    }
    // ending earlier by offset, by line, or by column on the same line
    for end in [
        location(9, 2, 3),
        location(9, 2, 4),
        location(20, 1, 9),
        location(20, 2, 2),
    ] {
        assert_eq!(
            SmtSpan::new(start, end),
            Err(SmtInvalidSpanError),
            "end {end:?}"
        );
    }
}

#[test]
fn locations_are_ordered_by_offset() {
    // consistent locations can disagree on the order of their lines: the
    // later one by offset may still be on an earlier line, and only the
    // offset counts
    let ordered = [
        location(0, 0, 0),
        location(5, 1, 0),
        location(10, 0, 10),
        location(11, 1, 1),
        location(12, 0, 0),
    ];
    for (i, earlier) in ordered.iter().enumerate() {
        for later in &ordered[i + 1..] {
            assert!(earlier < later, "{earlier:?} should be before {later:?}");
            assert!(later > earlier, "{later:?} should be after {earlier:?}");
        }
    }
}

#[test]
fn spans_are_ordered_by_start_then_end() {
    let a = location(0, 0, 0);
    let b = location(5, 1, 0);
    let c = location(10, 1, 5);
    let d = location(12, 0, 0);
    // the start decides first, even against a later end
    let ordered = [span(a, a), span(a, b), span(a, d), span(b, c), span(c, c)];
    for (i, earlier) in ordered.iter().enumerate() {
        for later in &ordered[i + 1..] {
            assert!(earlier < later, "{earlier:?} should be before {later:?}");
        }
    }
}

#[test]
fn a_joined_span_runs_from_the_earlier_start_to_the_later_end() {
    let a = location(0, 0, 0);
    let b = location(5, 1, 0);
    let c = location(10, 1, 5);
    let d = location(12, 2, 0);
    for (first, second, joined) in [
        // apart
        (span(a, b), span(c, d), span(a, d)),
        // overlapping
        (span(a, c), span(b, d), span(a, d)),
        // nested
        (span(a, d), span(b, c), span(a, d)),
        // touching, and an empty span inside another
        (span(a, b), span(b, c), span(a, c)),
        (span(b, b), span(a, c), span(a, c)),
        // the same
        (span(b, c), span(b, c), span(b, c)),
    ] {
        assert_eq!(
            first.join(second),
            joined,
            "{first:?} joined with {second:?}"
        );
        assert_eq!(
            second.join(first),
            joined,
            "{second:?} joined with {first:?}"
        );
    }
}

#[test]
#[should_panic(expected = "location offset must not overflow")]
fn a_location_at_the_last_offset_does_not_advance_over_a_line_feed() {
    location(u64::MAX, 1, 0).after_byte(b'\n');
}

#[test]
#[should_panic(expected = "location offset must not overflow")]
fn a_location_at_the_last_offset_does_not_advance_over_a_column() {
    location(u64::MAX, 0, u64::MAX).after_column();
}

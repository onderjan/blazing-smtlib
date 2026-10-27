//! Public-API tests of locations and spans: the consistency their
//! constructors check, their order, and that a location does not advance
//! past the last offset.
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
fn a_span_is_consistent_exactly_when_its_bytes_hold_what_separates_its_locations() {
    // on the same line, the bytes between the locations are exactly the
    // columns between them; on a later line, they hold a line feed for each
    // line ended and the columns before the end
    let start = location(10, 2, 3);
    for end in [
        // empty, and within the line
        location(10, 2, 3),
        location(12, 2, 5),
        // across lines, with bytes to spare and with none
        location(15, 3, 0),
        location(40, 9, 1),
        location(11, 3, 0),
        location(13, 4, 1),
    ] {
        let built = span(start, end);
        assert_eq!((built.start(), built.end()), (start, end));
        assert_eq!(built.is_empty(), start == end);
    }
    for end in [
        // ending earlier by offset, by line, or by column on the same line
        location(9, 2, 3),
        location(9, 2, 4),
        location(20, 1, 9),
        location(20, 2, 2),
        // on the same line, more bytes than columns or more columns than bytes
        location(20, 2, 4),
        location(11, 2, 9),
        // on a later line, too few bytes for the line feeds and the columns
        location(10, 3, 0),
        location(12, 4, 1),
        location(13, 3, 3),
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
    let d = location(12, 1, 7);
    // the start decides first, even against a later end
    let ordered = [span(a, a), span(a, b), span(a, d), span(b, c), span(c, c)];
    for (i, earlier) in ordered.iter().enumerate() {
        for later in &ordered[i + 1..] {
            assert!(earlier < later, "{earlier:?} should be before {later:?}");
        }
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

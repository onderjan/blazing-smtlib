//! Tests of the single-token parsers.

use super::*;

#[test]
fn symbol_parser() {
    let symbol = parse_all::<SmtSymbolParser>(b"abc");
    assert_eq!(symbol.as_slice(), b"abc");
    let symbol = parse_all::<SmtSymbolParser>(b"|quoted symbol|");
    assert_eq!(symbol.as_slice(), b"quoted symbol");

    let err = assert_error::<SmtSymbolParser>(b"1", 0, 1);
    let expected_symbol = SmtSyntaxErrorKind::ExpectedSymbol;
    assert_eq!(err, expected_symbol, "{err:?}");
    let err = assert_error::<SmtSymbolParser>(b"(", 0, 1);
    assert_eq!(err, expected_symbol, "{err:?}");
    // reserved words are not symbols
    let err = assert_error::<SmtSymbolParser>(b"let", 0, 3);
    assert_eq!(err, expected_symbol, "{err:?}");
}

#[test]
fn symbol_parser_consumes_one_token() {
    let (symbol, left) = run::<SmtSymbolParser>(b"a b c").expect("valid");
    assert_eq!(symbol.as_slice(), b"a");
    assert_eq!(left, 2);
}

#[test]
fn open_paren_parser() {
    parse_all::<SmtOpenParenParser>(b"(");

    let expected_open = SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen]);
    let err = assert_error::<SmtOpenParenParser>(b")", 0, 1);
    assert_eq!(err, expected_open, "{err:?}");
    let err = assert_error::<SmtOpenParenParser>(b"x", 0, 1);
    assert_eq!(err, expected_open, "{err:?}");
}

#[test]
fn close_paren_parser() {
    parse_all::<SmtCloseParenParser>(b")");

    let expected_close = SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose]);
    let err = assert_error::<SmtCloseParenParser>(b"x", 0, 1);
    assert_eq!(err, expected_close, "{err:?}");
    // the end-of-file token does not match either; its span is zero-width
    let err = assert_error::<SmtCloseParenParser>(b"", 0, 0);
    assert_eq!(err, expected_close, "{err:?}");
}

#[test]
fn keyword_parser() {
    // the keyword content is stored without the leading colon
    let keyword = parse_all::<SmtKeywordParser>(b":status");
    assert_eq!(keyword.as_slice(), b"status");

    let expected_keyword = SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::Keyword]);
    // a bare symbol is not a keyword
    let err = assert_error::<SmtKeywordParser>(b"status", 0, 6);
    assert_eq!(err, expected_keyword, "{err:?}");
    let err = assert_error::<SmtKeywordParser>(b"(", 0, 1);
    assert_eq!(err, expected_keyword, "{err:?}");
}

#[test]
fn string_parser() {
    // the string content is stored without the enclosing quotes
    let string = parse_all::<SmtStringParser>(b"\"hello world\"");
    assert_eq!(string.as_slice(), b"hello world");
    // a doubled quote is the escape for a single quote
    let string = parse_all::<SmtStringParser>(b"\"a\"\"b\"");
    assert_eq!(string.as_slice(), b"a\"b");

    let expected_string = SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::String]);
    // neither a quoted symbol nor a numeral is a string literal
    let err = assert_error::<SmtStringParser>(b"|hello|", 0, 7);
    assert_eq!(err, expected_string, "{err:?}");
    let err = assert_error::<SmtStringParser>(b"1", 0, 1);
    assert_eq!(err, expected_string, "{err:?}");
}

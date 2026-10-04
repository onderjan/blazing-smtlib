//! Tests of the single-token parsers.

use super::*;

#[test]
fn symbol_parser() {
    let symbol = parse_all::<SymbolParser>(b"abc");
    assert_eq!(symbol.as_slice(), b"abc");
    let symbol = parse_all::<SymbolParser>(b"|quoted symbol|");
    assert_eq!(symbol.as_slice(), b"quoted symbol");

    let err = assert_error::<SymbolParser>(b"1", 0, 1);
    let expected_symbol = SyntaxErrorKind::ExpectedSymbol;
    assert_eq!(err, expected_symbol, "{err:?}");
    let err = assert_error::<SymbolParser>(b"(", 0, 1);
    assert_eq!(err, expected_symbol, "{err:?}");
    // reserved words are not symbols
    let err = assert_error::<SymbolParser>(b"let", 0, 3);
    assert_eq!(err, expected_symbol, "{err:?}");
}

#[test]
fn symbol_parser_consumes_one_token() {
    let (symbol, left) = run::<SymbolParser>(b"a b c").expect("valid");
    assert_eq!(symbol.as_slice(), b"a");
    assert_eq!(left, 2);
}

#[test]
fn open_paren_parser() {
    parse_all::<OpenParenParser>(b"(");

    let expected_open = SyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenOpen]);
    let err = assert_error::<OpenParenParser>(b")", 0, 1);
    assert_eq!(err, expected_open, "{err:?}");
    let err = assert_error::<OpenParenParser>(b"x", 0, 1);
    assert_eq!(err, expected_open, "{err:?}");
}

#[test]
fn close_paren_parser() {
    parse_all::<CloseParenParser>(b")");

    let expected_close = SyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose]);
    let err = assert_error::<CloseParenParser>(b"x", 0, 1);
    assert_eq!(err, expected_close, "{err:?}");
    // the end-of-file token does not match either; its span is zero-width
    let err = assert_error::<CloseParenParser>(b"", 0, 0);
    assert_eq!(err, expected_close, "{err:?}");
}

#[test]
fn keyword_parser() {
    // the keyword content is stored without the leading colon
    let keyword = parse_all::<KeywordParser>(b":status");
    assert_eq!(keyword.as_slice(), b"status");

    let expected_keyword = SyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::Keyword]);
    // a bare symbol is not a keyword
    let err = assert_error::<KeywordParser>(b"status", 0, 6);
    assert_eq!(err, expected_keyword, "{err:?}");
    let err = assert_error::<KeywordParser>(b"(", 0, 1);
    assert_eq!(err, expected_keyword, "{err:?}");
}

#[test]
fn string_parser() {
    // the string content is stored without the enclosing quotes
    let string = parse_all::<StringParser>(b"\"hello world\"");
    assert_eq!(string.as_slice(), b"hello world");
    // a doubled quote is the escape for a single quote
    let string = parse_all::<StringParser>(b"\"a\"\"b\"");
    assert_eq!(string.as_slice(), b"a\"b");

    let expected_string = SyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::String]);
    // neither a quoted symbol nor a numeral is a string literal
    let err = assert_error::<StringParser>(b"|hello|", 0, 7);
    assert_eq!(err, expected_string, "{err:?}");
    let err = assert_error::<StringParser>(b"1", 0, 1);
    assert_eq!(err, expected_string, "{err:?}");
}

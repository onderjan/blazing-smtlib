mod char_class;

use char_class::{U8OrEof, char_class_opt};

pub use char_class::CharClass;

use crate::{
    LinePositions, SmtBinDigits, SmtDecimal, SmtDigits, SmtHexDigits, SmtKeyword, SmtLocation,
    SmtNumeral, SmtSpan, SmtStringContent, SmtSymbol, String8, TokenSpan,
    token::{Reserved, Token, TokenKind},
};

pub enum LexerState {
    Normal,
    Fraction {
        whole_part: String8,
        fractional_part: String8,
    },
    NumeralOrDecimal(String8),
    Hexadecimal(String8),
    Binary(String8),
    HexadecimalOrBinary,
    StringLiteral(String8),
    StringLiteralDoubleQuote(String8),
    SimpleSymbol(String8),
    Keyword(String8),
    QuotedSymbol(String8),
    Comment,
}

pub struct Lexer {
    state: LexerState,
    // Current byte offset since start of reading.
    //
    // Increments after lexing, i.e. when lexing, points at the
    // "start" of the currently read character.
    offset: u64,
    // Byte offset of the start of the token being currently read.
    token_start: u64,
    // Line positions, used to add line and column offsets to internal spans.
    line_positions: LinePositions,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexerErrorKind {
    UnexpectedCharacter,
    FractionDigitExpected,
    HexadecimalDigitExpected,
    BinaryDigitExpected,
    BaseSelectionExpected,
    UnclosedStringLiteral,
    ForbiddenCharInString,
    KeywordNameExpected,
    KeywordReserved,
    BackslashInQuotedSymbol,
    ForbiddenCharInQuotedSymbol,
    UnclosedQuotedSymbol,
    NumeralLeadingZero,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexerError {
    kind: LexerErrorKind,
    span: SmtSpan,
}

impl Lexer {
    pub fn new() -> Self {
        Lexer {
            state: LexerState::Normal,
            token_start: 0,
            offset: 0,
            line_positions: LinePositions::new(),
        }
    }

    pub fn lex_next(&mut self, c: u8) -> Result<Vec<Token>, LexerError> {
        let tokens = self.lex_char(U8OrEof::U8(c))?;
        if c == b'\n' {
            self.line_positions.add_newline(self.offset);
        }
        self.offset += 1;
        Ok(tokens)
    }

    pub fn lex_eof(&mut self) -> Result<Vec<Token>, LexerError> {
        self.lex_char(U8OrEof::Eof)
    }

    pub fn current_location(&self) -> SmtLocation {
        self.line_positions.resolve(self.offset)
    }

    pub(crate) fn resolve_span(&self, span: TokenSpan) -> SmtSpan {
        let start = self.line_positions.resolve(span.start());
        let end = self.line_positions.resolve(span.end());
        SmtSpan::new_unchecked(start, end)
    }

    fn lex_normal(&mut self, mut tokens: Vec<Token>, c: U8OrEof) -> Result<Vec<Token>, LexerError> {
        let byte = match c {
            U8OrEof::U8(c) => c,
            U8OrEof::Eof => {
                // end without problems on EOF
                tokens.push(self.create_zero_byte_token(TokenKind::EndOfFile));
                return Ok(tokens);
            }
        };

        // start token span as we are in the normal state
        self.start_token_span();

        let state = match CharClass::from(byte) {
            // whitespace, just continue lexing
            CharClass::Tab | CharClass::Space | CharClass::LineBreak => LexerState::Normal,

            // parentheses are tokens of their own
            CharClass::ParenOpen => {
                let token = self.create_token_ending_now(TokenKind::ParenOpen);
                tokens.push(token);
                LexerState::Normal
            }
            CharClass::ParenClose => {
                let token = self.create_token_ending_now(TokenKind::ParenClose);
                tokens.push(token);
                LexerState::Normal
            }

            // semicolon starts a comment
            CharClass::Semicolon => LexerState::Comment,

            CharClass::Digit => {
                // digit starts a numeral or a decimal
                // and determines the first digit value
                LexerState::NumeralOrDecimal(String8::from_byte(byte))
            }

            CharClass::Hash => {
                // hash starts a hexadecimal or a binary
                // the token location includes the hash
                LexerState::HexadecimalOrBinary
            }

            CharClass::DoubleQuote => {
                // double quote starts a string literal
                LexerState::StringLiteral(String8::new())
            }

            CharClass::Colon => {
                // colon starts a keyword, which continues with a simple symbol string
                LexerState::Keyword(String8::new())
            }

            CharClass::Letter | CharClass::Special | CharClass::Dot => {
                // starts a simple symbol or a reserved word
                // the reserved words will be handled after the name is fully known
                LexerState::SimpleSymbol(String8::from_byte(byte))
            }

            CharClass::Pipe => {
                //  pipe starts a quoted symbol
                LexerState::QuotedSymbol(String8::new())
            }

            _ => {
                // class disallowed here
                return Err(self.current_token_error(LexerErrorKind::UnexpectedCharacter, c));
            }
        };
        self.state = state;
        Ok(tokens)
    }

    fn lex_char(&mut self, c: U8OrEof) -> Result<Vec<Token>, LexerError> {
        let mut state = LexerState::Normal;
        std::mem::swap(&mut self.state, &mut state);
        let mut tokens = Vec::new();
        let state = match state {
            LexerState::Normal => return self.lex_normal(tokens, c),
            LexerState::Fraction {
                whole_part,
                mut fractional_part,
            } => {
                match char_class_opt(c) {
                    Some((CharClass::Digit, c)) => {
                        // add one digit to the fractional part
                        fractional_part.push(c);

                        LexerState::Fraction {
                            whole_part,
                            fractional_part,
                        }
                    }
                    _ => {
                        if fractional_part.is_empty() {
                            // decimals of the form 7. without any digit in fractional part are disallowed
                            return Err(
                                self.current_token_error(LexerErrorKind::FractionDigitExpected, c)
                            );
                        }
                        // push new token and lex the character normally
                        let kind = TokenKind::Decimal(SmtDecimal {
                            whole_part: SmtNumeral::new_unchecked(whole_part),
                            fractional_part: SmtDigits::new_unchecked(fractional_part),
                        });
                        tokens.push(self.create_token_ending_before(kind));
                        return self.lex_normal(tokens, c);
                    }
                }
            }
            LexerState::NumeralOrDecimal(mut value) => {
                match char_class_opt(c) {
                    Some((CharClass::Digit, byte)) => {
                        // check that we are not in a leading zero condition
                        // this could not have been done when starting the numeral/decimal
                        // since just a single '0' is allowed
                        if value.as_slice() == b"0" {
                            return Err(
                                self.current_token_error(LexerErrorKind::NumeralLeadingZero, c)
                            );
                        }

                        // add one digit
                        value.push(byte);
                        LexerState::NumeralOrDecimal(value)
                    }

                    Some((CharClass::Dot, _)) => {
                        // decimal, the next character will start fraction
                        LexerState::Fraction {
                            whole_part: value,
                            fractional_part: String8::new(),
                        }
                    }

                    _ => {
                        // this was a numeral
                        // push new token and lex the character normally
                        let kind = TokenKind::Numeral(SmtNumeral::new_unchecked(value));
                        tokens.push(self.create_token_ending_before(kind));
                        return self.lex_normal(tokens, c);
                    }
                }
            }
            LexerState::Hexadecimal(mut whole) => {
                let hex_digit = if let U8OrEof::U8(c) = c {
                    match c {
                        b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F' => Some(c),
                        _ => None,
                    }
                } else {
                    None
                };

                if let Some(hex_digit) = hex_digit {
                    // add hexadecimal digit
                    whole.push(hex_digit);
                    LexerState::Hexadecimal(whole)
                } else {
                    if whole.is_empty() {
                        // had non-digit, zero digits disallowed
                        return Err(
                            self.current_token_error(LexerErrorKind::HexadecimalDigitExpected, c)
                        );
                    }
                    // had non-digit, nonzero digits
                    // push new token and lex the character normally
                    let kind = TokenKind::Hexadecimal(SmtHexDigits::new_unchecked(whole));
                    tokens.push(self.create_token_ending_before(kind));
                    return self.lex_normal(tokens, c);
                }
            }
            LexerState::Binary(mut whole) => {
                let binary_digit = if let U8OrEof::U8(c) = c {
                    match c {
                        b'0' | b'1' => Some(c),
                        _ => None,
                    }
                } else {
                    None
                };

                if let Some(binary_digit) = binary_digit {
                    // add binary digit
                    whole.push(binary_digit);
                    LexerState::Binary(whole)
                } else {
                    if whole.is_empty() {
                        // had non-digit, zero digits disallowed
                        return Err(
                            self.current_token_error(LexerErrorKind::BinaryDigitExpected, c)
                        );
                    }
                    // had non-digit, nonzero digits
                    // push new token and lex the character normally
                    let kind = TokenKind::Binary(SmtBinDigits::new_unchecked(whole));
                    tokens.push(self.create_token_ending_before(kind));
                    return self.lex_normal(tokens, c);
                }
            }

            LexerState::HexadecimalOrBinary => match c {
                U8OrEof::U8(b'x') => LexerState::Hexadecimal(String8::new()),
                U8OrEof::U8(b'b') => LexerState::Binary(String8::new()),
                _ => return Err(self.current_token_error(LexerErrorKind::BaseSelectionExpected, c)),
            },
            LexerState::StringLiteral(mut literal) => {
                match c {
                    U8OrEof::Eof => {
                        // forbidden as the literal must be totally enclosed by double quotes
                        return Err(
                            self.current_token_error(LexerErrorKind::UnclosedStringLiteral, c)
                        );
                    }
                    U8OrEof::U8(b'\"') => {
                        // we have a double quote in string literal
                        // it may be followed by another double quote for escaping
                        // otherwise, it will end the string literal
                        // put the lexer in a special state to handle the next character
                        LexerState::StringLiteralDoubleQuote(literal)
                    }
                    U8OrEof::U8(byte) => {
                        if CharClass::from(byte).is_printable_or_whitespace() {
                            // add to literal
                            literal.push(byte);
                            LexerState::StringLiteral(literal)
                        } else {
                            // forbidden as not printable or whitespace
                            return Err(
                                self.current_token_error(LexerErrorKind::ForbiddenCharInString, c)
                            );
                        }
                    }
                }
            }
            LexerState::StringLiteralDoubleQuote(mut literal) => {
                match c {
                    U8OrEof::U8(b'\"') => {
                        // this has been a double-quote escape
                        // push a double-quote and continue lexing the string literal
                        literal.push(b'\"');
                        LexerState::StringLiteral(literal)
                    }
                    _ => {
                        // literal has ended by the previous character
                        // push new token and lex the character normally
                        let kind = TokenKind::String(SmtStringContent::new_unchecked(literal));
                        tokens.push(self.create_token_ending_before(kind));
                        return self.lex_normal(tokens, c);
                    }
                }
            }
            LexerState::SimpleSymbol(mut symbol) => {
                if let Some((class, c)) = char_class_opt(c)
                    && class.is_allowed_in_simple_symbol()
                {
                    // add character
                    symbol.push(c);
                    LexerState::SimpleSymbol(symbol)
                } else {
                    // simple symbol ended with previous character
                    // process reserved words
                    let kind = if let Some(reserved) = Reserved::from_symbol_opt(&symbol) {
                        TokenKind::Reserved(reserved)
                    } else {
                        TokenKind::Symbol(SmtSymbol::new_unchecked(symbol))
                    };

                    // push new token and lex the character normally
                    tokens.push(self.create_token_ending_before(kind));
                    return self.lex_normal(tokens, c);
                }
            }
            LexerState::Keyword(mut keyword) => match char_class_opt(c) {
                Some((
                    CharClass::Letter | CharClass::Digit | CharClass::Special | CharClass::Dot,
                    byte,
                )) => {
                    // add character
                    keyword.push(byte);
                    LexerState::Keyword(keyword)
                }
                _ => {
                    // simple symbol ended with previous character
                    if keyword.is_empty() {
                        return Err(
                            self.current_token_error(LexerErrorKind::KeywordNameExpected, c)
                        );
                    }

                    // reserved words as keywords are prohibited
                    if Reserved::from_symbol_opt(&keyword).is_some() {
                        return Err(self.current_token_error(LexerErrorKind::KeywordReserved, c));
                    }

                    // push new token and lex the character normally
                    let kind = TokenKind::Keyword(SmtKeyword::new_unchecked(keyword));
                    tokens.push(self.create_token_ending_before(kind));
                    return self.lex_normal(tokens, c);
                }
            },
            LexerState::QuotedSymbol(mut symbol) => {
                match c {
                    U8OrEof::U8(b'\\') => {
                        // backslash forbidden in quoted symbols
                        return Err(
                            self.current_token_error(LexerErrorKind::BackslashInQuotedSymbol, c)
                        );
                    }
                    U8OrEof::U8(b'|') => {
                        // end of quoted symbol, push its token, continue normally with next character

                        let kind = TokenKind::Symbol(SmtSymbol::new_unchecked(symbol));
                        tokens.push(self.create_token_ending_now(kind));
                        LexerState::Normal
                    }
                    U8OrEof::U8(byte) => {
                        if CharClass::from(byte).is_printable_or_whitespace() {
                            // add the character to the quoted symbol and continue it
                            symbol.push(byte);
                            LexerState::QuotedSymbol(symbol)
                        } else {
                            // character forbidden as not printable or whitespace

                            return Err(self.current_token_error(
                                LexerErrorKind::ForbiddenCharInQuotedSymbol,
                                c,
                            ));
                        }
                    }

                    U8OrEof::Eof => {
                        // EOF forbidden as the symbol must be totally enclosed by pipes
                        return Err(
                            self.current_token_error(LexerErrorKind::UnclosedQuotedSymbol, c)
                        );
                    }
                }
            }
            LexerState::Comment => {
                match char_class_opt(c) {
                    Some((CharClass::LineBreak, _)) => {
                        // end comment, ready for next token
                        LexerState::Normal
                    }
                    Some(_) => {
                        // continue comment
                        LexerState::Comment
                    }
                    None => {
                        // end without problems on EOF
                        let token = self.create_zero_byte_token(TokenKind::EndOfFile);
                        tokens.push(token);
                        return Ok(tokens);
                    }
                }
            }
        };
        self.state = state;
        Ok(tokens)
    }

    fn start_token_span(&mut self) {
        self.token_start = self.offset;
    }

    fn create_token_ending_now(&self, kind: TokenKind) -> Token {
        // The current offset is at the start of the current character
        // The span includes start, but not the end
        // Therefore, we need to add 1 to the current offset
        Token::new(
            kind,
            TokenSpan::new_unchecked(self.token_start, self.offset + 1),
        )
    }

    fn create_token_ending_before(&self, kind: TokenKind) -> Token {
        // The current offset is at the start of the current character
        // The span includes start, but not the end
        // Therefore, if the token actually ended with the previous character,
        // we do not need to add anything.
        Token::new(
            kind,
            TokenSpan::new_unchecked(self.token_start, self.offset),
        )
    }

    fn create_zero_byte_token(&mut self, kind: TokenKind) -> Token {
        self.start_token_span();
        self.create_token_ending_before(kind)
    }

    fn current_token_error(&self, kind: LexerErrorKind, c: U8OrEof) -> LexerError {
        // the spans starts at the token start and continues to the currently parsed,
        // where the error was detected, including it

        // if what we are parsing is a byte, add one to the end offset
        // since the span is a half-open range containing the start, but not end
        // if what we are parsing is EOF, do not add anything
        let end_offset = match c {
            U8OrEof::U8(_) => self.offset + 1,
            U8OrEof::Eof => self.offset,
        };

        let span = TokenSpan::new_unchecked(self.token_start, end_offset);
        let span = self.resolve_span(span);
        LexerError::new(kind, span)
    }

    /// Lex the whole input including EOF, returning all tokens or the lexer error.
    ///
    /// This is a helper function for tests.
    #[cfg(test)]
    pub(crate) fn lex_all(input: &[u8]) -> Result<Vec<Token>, LexerError> {
        let mut lexer = Lexer::new();
        let mut tokens = Vec::new();
        for &c in input {
            tokens.extend(lexer.lex_next(c)?);
        }
        tokens.extend(lexer.lex_eof()?);
        Ok(tokens)
    }
}

impl Default for Lexer {
    fn default() -> Self {
        Self::new()
    }
}

impl LexerError {
    fn new(kind: LexerErrorKind, span: SmtSpan) -> Self {
        Self { kind, span }
    }

    pub fn kind(&self) -> &LexerErrorKind {
        &self.kind
    }

    pub fn span(&self) -> SmtSpan {
        self.span
    }

    pub fn into_kind(self) -> LexerErrorKind {
        self.kind
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::token::TokenType;

    /// Expected location as `(offset, line, column)`.
    type Loc = (u64, u64, u64);

    fn loc(location: SmtLocation) -> Loc {
        (location.offset(), location.line(), location.column())
    }

    fn lex_all(input: &[u8]) -> Result<Vec<Token>, LexerError> {
        Lexer::lex_all(input)
    }

    /// Lexes the input, requires an error of the given kind, and checks its span.
    #[track_caller]
    fn assert_error(input: &[u8], kind: LexerErrorKind, start: Loc, end: Loc) {
        let err = lex_all(input).expect_err("expected a lexer error, got tokens");
        assert_eq!(*err.kind(), kind);
        let span = err.span();
        assert_eq!(
            (loc(span.start()), loc(span.end())),
            (start, end),
            "span mismatch (start, end) as (offset, line, column)"
        );
    }

    #[test]
    fn valid_input_has_no_error() {
        assert!(lex_all(b"").is_ok());
        assert!(lex_all(b"(set-logic QF_UF)\n(check-sat)\n").is_ok());
        assert!(lex_all(b"; comment only").is_ok());
        assert!(lex_all(b"7 7.0 #x1F #b10 \"s\" :kw |q s| sym").is_ok());
    }

    // --- Errors detected on a byte: span covers the token so far and the offending byte ---

    #[test]
    fn unexpected_character_is_single_byte() {
        // backslash is not allowed outside of string literals
        assert_error(
            b"\\",
            LexerErrorKind::UnexpectedCharacter,
            (0, 1, 1),
            (1, 1, 2),
        );
        // after other tokens, still just the one byte
        assert_error(
            b"(check-sat) \\",
            LexerErrorKind::UnexpectedCharacter,
            (12, 1, 13),
            (13, 1, 14),
        );
    }

    #[test]
    fn fraction_digit_expected_on_byte() {
        // "7." followed by a space: the space is the byte where the error is detected
        assert_error(
            b"7. ",
            LexerErrorKind::FractionDigitExpected,
            (0, 1, 1),
            (3, 1, 4),
        );
    }

    #[test]
    fn base_selection_expected() {
        assert_error(
            b"#q",
            LexerErrorKind::BaseSelectionExpected,
            (0, 1, 1),
            (2, 1, 3),
        );
    }

    #[test]
    fn hexadecimal_digit_expected() {
        assert_error(
            b"#x ",
            LexerErrorKind::HexadecimalDigitExpected,
            (0, 1, 1),
            (3, 1, 4),
        );
    }

    #[test]
    fn binary_digit_expected() {
        assert_error(
            b"#b)",
            LexerErrorKind::BinaryDigitExpected,
            (0, 1, 1),
            (3, 1, 4),
        );
    }

    #[test]
    fn numeral_leading_zero() {
        assert_error(
            b"01",
            LexerErrorKind::NumeralLeadingZero,
            (0, 1, 1),
            (2, 1, 3),
        );
    }

    #[test]
    fn keyword_name_expected() {
        assert_error(
            b": ",
            LexerErrorKind::KeywordNameExpected,
            (0, 1, 1),
            (2, 1, 3),
        );
    }

    #[test]
    fn keyword_reserved() {
        assert_error(
            b":let ",
            LexerErrorKind::KeywordReserved,
            (0, 1, 1),
            (5, 1, 6),
        );
    }

    #[test]
    fn backslash_in_quoted_symbol() {
        assert_error(
            b"|a\\b|",
            LexerErrorKind::BackslashInQuotedSymbol,
            (0, 1, 1),
            (3, 1, 4),
        );
    }

    #[test]
    fn forbidden_char_in_string() {
        assert_error(
            b"\"a\x01b\"",
            LexerErrorKind::ForbiddenCharInString,
            (0, 1, 1),
            (3, 1, 4),
        );
    }

    #[test]
    fn forbidden_char_in_quoted_symbol() {
        assert_error(
            b"|a\x7fb|",
            LexerErrorKind::ForbiddenCharInQuotedSymbol,
            (0, 1, 1),
            (3, 1, 4),
        );
    }

    // --- Errors detected at EOF: span must end exactly at the input length, not past it ---

    #[test]
    fn fraction_digit_expected_at_eof() {
        assert_error(
            b"7.",
            LexerErrorKind::FractionDigitExpected,
            (0, 1, 1),
            (2, 1, 3),
        );
    }

    #[test]
    fn hexadecimal_digit_expected_at_eof() {
        assert_error(
            b"#x",
            LexerErrorKind::HexadecimalDigitExpected,
            (0, 1, 1),
            (2, 1, 3),
        );
    }

    #[test]
    fn base_selection_expected_at_eof() {
        assert_error(
            b"#",
            LexerErrorKind::BaseSelectionExpected,
            (0, 1, 1),
            (1, 1, 2),
        );
    }

    #[test]
    fn keyword_name_expected_at_eof() {
        assert_error(
            b":",
            LexerErrorKind::KeywordNameExpected,
            (0, 1, 1),
            (1, 1, 2),
        );
    }

    #[test]
    fn unclosed_string_literal_at_eof() {
        assert_error(
            b"\"abc",
            LexerErrorKind::UnclosedStringLiteral,
            (0, 1, 1),
            (4, 1, 5),
        );
    }

    #[test]
    fn unclosed_quoted_symbol_at_eof() {
        assert_error(
            b"|abc",
            LexerErrorKind::UnclosedQuotedSymbol,
            (0, 1, 1),
            (4, 1, 5),
        );
    }

    // --- Line and column tracking ---

    #[test]
    fn error_on_later_line() {
        // the string literal starts on line 3, column 3 (offset 15) and is unclosed at EOF
        assert_error(
            b"(check-sat)\n\n  \"abc",
            LexerErrorKind::UnclosedStringLiteral,
            (15, 3, 3),
            (19, 3, 7),
        );
    }

    #[test]
    fn error_spanning_lines() {
        // an unclosed quoted symbol may contain newlines; the end is on a later line
        assert_error(
            b"|ab\ncd",
            LexerErrorKind::UnclosedQuotedSymbol,
            (0, 1, 1),
            (6, 2, 3),
        );
    }

    #[test]
    fn crlf_counts_as_one_line() {
        // CR must not start a new line, so "01" is on line 2, column 1
        assert_error(
            b"(check-sat)\r\n01",
            LexerErrorKind::NumeralLeadingZero,
            (13, 2, 1),
            (15, 2, 3),
        );
    }

    #[test]
    fn error_after_comment_line() {
        assert_error(
            b"; a comment\n\\",
            LexerErrorKind::UnexpectedCharacter,
            (12, 2, 1),
            (13, 2, 2),
        );
    }

    // --- Token spans and current location ---

    #[test]
    fn token_spans_are_byte_ranges() {
        let tokens = lex_all(b"(a 12)\n|q|").expect("valid input");
        let spans: Vec<(u64, u64)> = tokens
            .iter()
            .map(|token| (token.span().start(), token.span().end()))
            .collect();
        // `(`, `a`, `12`, `)`, `|q|`, and the zero-width EOF token
        assert_eq!(
            spans,
            vec![(0, 1), (1, 2), (3, 5), (5, 6), (7, 10), (10, 10)]
        );
    }

    #[test]
    fn current_location_follows_consumed_bytes() {
        let mut lexer = Lexer::new();
        assert_eq!(loc(lexer.current_location()), (0, 1, 1));
        for &c in b"ab\nc" {
            lexer.lex_next(c).expect("valid input");
        }
        assert_eq!(loc(lexer.current_location()), (4, 2, 2));
    }

    // --- Resolved token spans: offset, line and column ---

    /// Expected token as `(type, start, end)`, with the locations as `(offset, line, column)`.
    type TokenLoc = (TokenType, Loc, Loc);

    /// Lexes the whole input and resolves the span of every token to lines and columns.
    ///
    /// The resolution goes through the lexer's line positions, which is what reading does
    /// with parser error spans. Should a token ever carry an already resolved span instead,
    /// only this helper has to change; the expectations of the tests below describe the
    /// locations themselves and stay as they are.
    fn resolved_token_spans(input: &[u8]) -> Vec<TokenLoc> {
        let mut lexer = Lexer::new();
        let mut tokens = Vec::new();
        for &c in input {
            tokens.extend(lexer.lex_next(c).expect("test input must lex"));
        }
        tokens.extend(lexer.lex_eof().expect("test input must lex"));
        tokens
            .iter()
            .map(|token| {
                let span = lexer.resolve_span(token.span());
                (token.kind().ty(), loc(span.start()), loc(span.end()))
            })
            .collect()
    }

    #[test]
    fn spans_on_a_single_line() {
        // columns are one-based and counted in bytes
        assert_eq!(
            resolved_token_spans(b"(a 12)"),
            vec![
                (TokenType::ParenOpen, (0, 1, 1), (1, 1, 2)),
                (TokenType::Symbol, (1, 1, 2), (2, 1, 3)),
                (TokenType::Numeral, (3, 1, 4), (5, 1, 6)),
                (TokenType::ParenClose, (5, 1, 6), (6, 1, 7)),
                (TokenType::EndOfFile, (6, 1, 7), (6, 1, 7)),
            ]
        );
    }

    #[test]
    fn spans_restart_the_column_on_every_line() {
        assert_eq!(
            resolved_token_spans(b"(a)\n(b)"),
            vec![
                (TokenType::ParenOpen, (0, 1, 1), (1, 1, 2)),
                (TokenType::Symbol, (1, 1, 2), (2, 1, 3)),
                (TokenType::ParenClose, (2, 1, 3), (3, 1, 4)),
                (TokenType::ParenOpen, (4, 2, 1), (5, 2, 2)),
                (TokenType::Symbol, (5, 2, 2), (6, 2, 3)),
                (TokenType::ParenClose, (6, 2, 3), (7, 2, 4)),
                (TokenType::EndOfFile, (7, 2, 4), (7, 2, 4)),
            ]
        );
    }

    #[test]
    fn span_end_is_one_past_the_last_byte_of_the_token() {
        // `ab` is terminated by the line break, but its end stays on the first line,
        // one column past the `b`, rather than moving to the start of the second line
        assert_eq!(
            resolved_token_spans(b"ab\ncd"),
            vec![
                (TokenType::Symbol, (0, 1, 1), (2, 1, 3)),
                (TokenType::Symbol, (3, 2, 1), (5, 2, 3)),
                (TokenType::EndOfFile, (5, 2, 3), (5, 2, 3)),
            ]
        );
    }

    #[test]
    fn quoted_symbol_may_span_a_line_break() {
        // the token starts on the first line and ends on the second one,
        // and the line break inside it still counts for the tokens that follow
        assert_eq!(
            resolved_token_spans(b"|a\nb| c"),
            vec![
                (TokenType::Symbol, (0, 1, 1), (5, 2, 3)),
                (TokenType::Symbol, (6, 2, 4), (7, 2, 5)),
                (TokenType::EndOfFile, (7, 2, 5), (7, 2, 5)),
            ]
        );
    }

    #[test]
    fn string_literal_may_span_a_line_break() {
        assert_eq!(
            resolved_token_spans(b"\"a\nb\""),
            vec![
                (TokenType::String, (0, 1, 1), (5, 2, 3)),
                (TokenType::EndOfFile, (5, 2, 3), (5, 2, 3)),
            ]
        );
    }

    #[test]
    fn end_of_file_token_after_a_trailing_line_break() {
        // without a trailing line break, the end-of-file token is just past the last token
        assert_eq!(
            resolved_token_spans(b"(a)"),
            vec![
                (TokenType::ParenOpen, (0, 1, 1), (1, 1, 2)),
                (TokenType::Symbol, (1, 1, 2), (2, 1, 3)),
                (TokenType::ParenClose, (2, 1, 3), (3, 1, 4)),
                (TokenType::EndOfFile, (3, 1, 4), (3, 1, 4)),
            ]
        );
        // with one, its offset is exactly the start of the next line,
        // so it is reported at the first column of that line rather than past the end
        // of the previous one
        assert_eq!(
            resolved_token_spans(b"(a)\n"),
            vec![
                (TokenType::ParenOpen, (0, 1, 1), (1, 1, 2)),
                (TokenType::Symbol, (1, 1, 2), (2, 1, 3)),
                (TokenType::ParenClose, (2, 1, 3), (3, 1, 4)),
                (TokenType::EndOfFile, (4, 2, 1), (4, 2, 1)),
            ]
        );
    }

    #[test]
    fn crlf_is_a_single_line_break_in_token_spans() {
        // CR terminates the symbol but must not start a line of its own
        assert_eq!(
            resolved_token_spans(b"a\r\nb"),
            vec![
                (TokenType::Symbol, (0, 1, 1), (1, 1, 2)),
                (TokenType::Symbol, (3, 2, 1), (4, 2, 2)),
                (TokenType::EndOfFile, (4, 2, 2), (4, 2, 2)),
            ]
        );
    }

    #[test]
    fn comments_produce_no_tokens_but_still_count_lines() {
        assert_eq!(
            resolved_token_spans(b"; c\nx"),
            vec![
                (TokenType::Symbol, (4, 2, 1), (5, 2, 2)),
                (TokenType::EndOfFile, (5, 2, 2), (5, 2, 2)),
            ]
        );
    }

    #[test]
    fn spans_of_every_token_type() {
        // the hash of a hexadecimal or binary literal belongs to its token,
        // and a reserved word spans the same bytes an ordinary symbol would
        assert_eq!(
            resolved_token_spans(b":kw #xAB #b01 1.5 \"s\" let"),
            vec![
                (TokenType::Keyword, (0, 1, 1), (3, 1, 4)),
                (TokenType::Hexadecimal, (4, 1, 5), (8, 1, 9)),
                (TokenType::Binary, (9, 1, 10), (13, 1, 14)),
                (TokenType::Decimal, (14, 1, 15), (17, 1, 18)),
                (TokenType::String, (18, 1, 19), (21, 1, 22)),
                (TokenType::Reserved(Reserved::Let), (22, 1, 23), (25, 1, 26)),
                (TokenType::EndOfFile, (25, 1, 26), (25, 1, 26)),
            ]
        );
    }

    /// Resolving a token span never needs input that comes after the token.
    ///
    /// This is the property that a lexer resolving spans eagerly has to keep, and the one
    /// that makes keeping a history of line positions unnecessary: if a span resolves the
    /// same way at the moment its token is produced as it does once the whole input has
    /// been read, then nothing that follows a token can change where it is reported.
    #[test]
    fn token_spans_resolve_the_same_immediately_and_at_the_end() {
        for input in [
            b"(a 12)" as &[u8],
            b"(a)\n(b)",
            b"ab\ncd",
            b"|a\nb| c",
            b"\"a\nb\"",
            b"; c\nx",
            b"a\r\nb",
            b"(a)\n",
            b"(assert\n  (f\n    x))\n",
        ] {
            let mut lexer = Lexer::new();
            let mut tokens = Vec::new();
            let mut resolved_immediately = Vec::new();

            let mut collect = |lexer: &Lexer, produced: Vec<Token>| {
                for token in produced {
                    resolved_immediately.push(lexer.resolve_span(token.span()));
                    tokens.push(token);
                }
            };

            for &c in input {
                let produced = lexer.lex_next(c).expect("test input must lex");
                collect(&lexer, produced);
            }
            let produced = lexer.lex_eof().expect("test input must lex");
            collect(&lexer, produced);

            let resolved_at_end: Vec<SmtSpan> = tokens
                .iter()
                .map(|token| lexer.resolve_span(token.span()))
                .collect();

            assert_eq!(
                resolved_immediately,
                resolved_at_end,
                "span resolution depends on later input in {:?}",
                String8::from_vec(input.to_vec())
            );
        }
    }
}

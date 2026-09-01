mod char_class;

use char_class::{U8OrEof, char_class_opt};

pub(crate) use char_class::CharClass;

use crate::{
    SmtBinDigits, SmtDecimal, SmtHexDigits, SmtKeyword, SmtLocation, SmtNumeral, SmtSpan,
    SmtStringContent, SmtSymbol, String8,
    token::{Reserved, Token, TokenKind},
};

#[derive(Clone, Copy)]
enum LexerState {
    Normal,
    Fraction,
    NumeralOrDecimal,
    Hexadecimal,
    Binary,
    HexadecimalOrBinary,
    StringLiteral,
    StringLiteralDoubleQuote,
    SimpleSymbol,
    Keyword,
    QuotedSymbol,
    Comment,
    Failed,
}

pub struct Lexer {
    /// Current lexer state.
    state: LexerState,

    /// Location of the start of the currently-processed token.
    token_start: SmtLocation,

    /// The currently-built string content of the currently-processed token.
    token_content: String8,

    /// Location of the start of the byte being processed during lexing.
    ///
    /// It advances once that byte is consumed.
    byte_start: SmtLocation,
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
    ForbiddenKeywordName,
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

pub enum LexError<E> {
    Lexer(LexerError),
    Sink(E),
}

impl Lexer {
    /// Constructs the lexer.
    pub fn new() -> Self {
        Lexer {
            state: LexerState::Normal,
            token_start: SmtLocation::initial(),
            token_content: String8::new(),
            byte_start: SmtLocation::initial(),
        }
    }

    pub fn current_location(&self) -> SmtLocation {
        self.byte_start
    }

    /// Lexes one byte, sending the lexed tokens to the sink.
    ///
    /// Panics if a previous call returned an error.
    pub fn lex_next<E>(
        &mut self,
        c: u8,
        sink: impl FnMut(Token) -> Result<(), E>,
    ) -> Result<(), LexError<E>> {
        self.lex_char(U8OrEof::U8(c), sink)?;
        self.byte_start = self.byte_start.after_byte(c);
        Ok(())
    }

    /// Lexes one byte, sending the lexed tokens to the sink.
    ///
    /// Panics if a previous call returned an error.
    pub fn lex_eof<E>(
        &mut self,
        sink: impl FnMut(Token) -> Result<(), E>,
    ) -> Result<(), LexError<E>> {
        self.lex_char(U8OrEof::Eof, sink)
    }

    fn lex_char<E>(
        &mut self,
        c: U8OrEof,
        sink: impl FnMut(Token) -> Result<(), E>,
    ) -> Result<(), LexError<E>> {
        // when a lexer error is raised, set lexer state to failed
        self.lex_char_inner(c, sink).inspect_err(|_err| {
            self.state = LexerState::Failed;
        })
    }

    fn lex_char_inner<E>(
        &mut self,
        c: U8OrEof,
        mut sink: impl FnMut(Token) -> Result<(), E>,
    ) -> Result<(), LexError<E>> {
        let state = match self.state {
            LexerState::Normal => return self.lex_normal(c, sink),
            LexerState::Fraction => {
                match char_class_opt(c) {
                    Some((CharClass::Digit, c)) => {
                        // add one digit, this will be to the fractional part (after the dot)
                        self.token_content.push(c);
                        LexerState::Fraction
                    }
                    _ => {
                        let last_is_none_or_dot = self
                            .token_content
                            .as_slice()
                            .last()
                            .is_none_or(|c| *c == b'.');
                        if last_is_none_or_dot {
                            // decimals of the form 7. without any digit in fractional part are disallowed
                            return Err(
                                self.current_token_error(LexerErrorKind::FractionDigitExpected, c)
                            );
                        }
                        // sink new token and lex the character normally
                        let kind = TokenKind::Decimal(SmtDecimal::new_unchecked(
                            self.token_content.clone(),
                        ));
                        let token = self.create_token_ending_before(kind);
                        sink(token).map_err(LexError::Sink)?;
                        return self.lex_normal(c, sink);
                    }
                }
            }
            LexerState::NumeralOrDecimal => {
                match char_class_opt(c) {
                    Some((CharClass::Digit, byte)) => {
                        // check that we are not in a leading zero condition
                        // this could not have been done when starting the numeral/decimal
                        // since just a single '0' is allowed
                        if self.token_content.as_slice() == b"0" {
                            return Err(
                                self.current_token_error(LexerErrorKind::NumeralLeadingZero, c)
                            );
                        }

                        // add one digit
                        self.token_content.push(byte);
                        LexerState::NumeralOrDecimal
                    }

                    Some((CharClass::Dot, _)) => {
                        // decimal, the next character will start fraction
                        // add the dot to the value
                        self.token_content.push(b'.');
                        LexerState::Fraction
                    }

                    _ => {
                        // this was a numeral
                        // sink new token and lex the character normally
                        let kind = TokenKind::Numeral(SmtNumeral::new_unchecked(
                            self.token_content.clone(),
                        ));
                        let token = self.create_token_ending_before(kind);
                        sink(token).map_err(LexError::Sink)?;
                        return self.lex_normal(c, sink);
                    }
                }
            }
            LexerState::Hexadecimal => {
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
                    self.token_content.push(hex_digit);
                    LexerState::Hexadecimal
                } else {
                    if self.token_content.is_empty() {
                        // had non-digit, zero digits disallowed
                        return Err(
                            self.current_token_error(LexerErrorKind::HexadecimalDigitExpected, c)
                        );
                    }
                    // had non-digit, nonzero digits
                    // sink new token and lex the character normally
                    let kind = TokenKind::Hexadecimal(SmtHexDigits::new_unchecked(
                        self.token_content.clone(),
                    ));
                    return self.sink_and_lex_next(c, sink, kind);
                }
            }
            LexerState::Binary => {
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
                    self.token_content.push(binary_digit);
                    LexerState::Binary
                } else {
                    if self.token_content.is_empty() {
                        // had non-digit, zero digits disallowed
                        return Err(
                            self.current_token_error(LexerErrorKind::BinaryDigitExpected, c)
                        );
                    }
                    // had non-digit, nonzero digits
                    // sink new token and lex the character normally
                    let kind =
                        TokenKind::Binary(SmtBinDigits::new_unchecked(self.token_content.clone()));
                    return self.sink_and_lex_next(c, sink, kind);
                }
            }

            LexerState::HexadecimalOrBinary => match c {
                U8OrEof::U8(b'x') => LexerState::Hexadecimal,
                U8OrEof::U8(b'b') => LexerState::Binary,
                _ => return Err(self.current_token_error(LexerErrorKind::BaseSelectionExpected, c)),
            },
            LexerState::StringLiteral => {
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
                        LexerState::StringLiteralDoubleQuote
                    }
                    U8OrEof::U8(byte) => {
                        if CharClass::from(byte).is_printable_or_whitespace() {
                            // add to literal
                            self.token_content.push(byte);
                            LexerState::StringLiteral
                        } else {
                            // forbidden as not printable or whitespace
                            return Err(
                                self.current_token_error(LexerErrorKind::ForbiddenCharInString, c)
                            );
                        }
                    }
                }
            }
            LexerState::StringLiteralDoubleQuote => {
                match c {
                    U8OrEof::U8(b'\"') => {
                        // this has been a double-quote escape
                        // push a double-quote and continue lexing the string literal
                        self.token_content.push(b'\"');
                        LexerState::StringLiteral
                    }
                    _ => {
                        // literal has ended by the previous character
                        // sink new token and lex the character normally
                        let kind = TokenKind::String(SmtStringContent::new_unchecked(
                            self.token_content.clone(),
                        ));
                        let token = self.create_token_ending_before(kind);
                        sink(token).map_err(LexError::Sink)?;
                        return self.lex_normal(c, sink);
                    }
                }
            }
            LexerState::SimpleSymbol => {
                if let Some((class, c)) = char_class_opt(c)
                    && class.is_allowed_in_simple_symbol()
                {
                    // add character
                    self.token_content.push(c);
                    LexerState::SimpleSymbol
                } else {
                    // simple symbol ended with previous character
                    // process reserved words
                    let kind =
                        if let Some(reserved) = Reserved::from_symbol_opt(&self.token_content) {
                            TokenKind::Reserved(reserved)
                        } else {
                            TokenKind::Symbol(SmtSymbol::new_unchecked(self.token_content.clone()))
                        };

                    // sink new token and lex the character normally
                    return self.sink_and_lex_next(c, sink, kind);
                }
            }
            LexerState::Keyword => match char_class_opt(c) {
                Some((
                    CharClass::Letter | CharClass::Digit | CharClass::Special | CharClass::Dot,
                    byte,
                )) => {
                    // make sure the keyword doesn't start with a digit
                    if self.token_content.is_empty()
                        && matches!(char_class_opt(c), Some((CharClass::Digit, _)))
                    {
                        return Err(
                            self.current_token_error(LexerErrorKind::ForbiddenKeywordName, c)
                        );
                    }
                    // add character
                    self.token_content.push(byte);
                    LexerState::Keyword
                }
                _ => {
                    // simple symbol ended with previous character
                    if self.token_content.is_empty() {
                        return Err(
                            self.current_token_error(LexerErrorKind::ForbiddenKeywordName, c)
                        );
                    }

                    // reserved words as keywords are prohibited
                    if Reserved::from_symbol_opt(&self.token_content).is_some() {
                        return Err(self.current_token_error(LexerErrorKind::KeywordReserved, c));
                    }

                    // sink new token and lex the character normally
                    let kind =
                        TokenKind::Keyword(SmtKeyword::new_unchecked(self.token_content.clone()));
                    return self.sink_and_lex_next(c, sink, kind);
                }
            },
            LexerState::QuotedSymbol => {
                match c {
                    U8OrEof::U8(b'\\') => {
                        // backslash forbidden in quoted symbols
                        return Err(
                            self.current_token_error(LexerErrorKind::BackslashInQuotedSymbol, c)
                        );
                    }
                    U8OrEof::U8(b'|') => {
                        // end of quoted symbol, push its token, this character is consumed
                        let kind =
                            TokenKind::Symbol(SmtSymbol::new_unchecked(self.token_content.clone()));
                        let token = self.create_token_ending_now(kind);
                        sink(token).map_err(LexError::Sink)?;
                        LexerState::Normal
                    }
                    U8OrEof::U8(byte) => {
                        if CharClass::from(byte).is_printable_or_whitespace() {
                            // add the character to the quoted symbol and continue it
                            self.token_content.push(byte);
                            LexerState::QuotedSymbol
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
                        sink(token).map_err(LexError::Sink)?;
                        return Ok(());
                    }
                }
            }
            LexerState::Failed => panic!("cannot lex after a lexer error"),
        };
        self.state = state;
        Ok(())
    }

    fn lex_normal<E>(
        &mut self,
        c: U8OrEof,
        mut sink: impl FnMut(Token) -> Result<(), E>,
    ) -> Result<(), LexError<E>> {
        let byte = match c {
            U8OrEof::U8(c) => c,
            U8OrEof::Eof => {
                // end without problems on EOF
                let token = self.create_zero_byte_token(TokenKind::EndOfFile);
                return sink(token).map_err(LexError::Sink);
            }
        };

        // start the token as we are in the normal state
        self.start_token();

        let state = match CharClass::from(byte) {
            // whitespace, just continue lexing
            CharClass::Tab | CharClass::Space | CharClass::LineBreak => LexerState::Normal,

            // parentheses are tokens of their own
            CharClass::ParenOpen => {
                let token = self.create_token_ending_now(TokenKind::ParenOpen);
                sink(token).map_err(LexError::Sink)?;
                LexerState::Normal
            }
            CharClass::ParenClose => {
                let token = self.create_token_ending_now(TokenKind::ParenClose);
                sink(token).map_err(LexError::Sink)?;
                LexerState::Normal
            }

            // semicolon starts a comment
            CharClass::Semicolon => LexerState::Comment,

            CharClass::Digit => {
                // digit starts a numeral or a decimal
                // and determines the first digit value
                self.token_content.push(byte);
                LexerState::NumeralOrDecimal
            }

            CharClass::Hash => {
                // hash starts a hexadecimal or a binary
                // the token location includes the hash
                LexerState::HexadecimalOrBinary
            }

            CharClass::DoubleQuote => {
                // double quote starts a string literal
                // the content remains empty here (the quote is outside)
                LexerState::StringLiteral
            }

            CharClass::Colon => {
                // colon starts a keyword, which continues with a simple symbol string
                // the content remains empty here (the colon only marks the keyword)
                LexerState::Keyword
            }

            CharClass::Letter | CharClass::Special | CharClass::Dot => {
                // starts a simple symbol or a reserved word
                // the reserved words will be handled after the name is fully known
                self.token_content.push(byte);
                LexerState::SimpleSymbol
            }

            CharClass::Pipe => {
                // pipe starts a quoted symbol
                // the content remains empty here (the pipe is outside)
                LexerState::QuotedSymbol
            }

            _ => {
                // class disallowed here
                return Err(self.current_token_error(LexerErrorKind::UnexpectedCharacter, c));
            }
        };
        self.state = state;
        Ok(())
    }

    fn sink_and_lex_next<E>(
        &mut self,
        c: U8OrEof,
        mut sink: impl FnMut(Token) -> Result<(), E>,
        kind: TokenKind,
    ) -> Result<(), LexError<E>> {
        let token = self.create_token_ending_before(kind);
        sink(token).map_err(LexError::Sink)?;
        self.lex_normal(c, sink)
    }

    fn start_token(&mut self) {
        // update the token start and clear the token string
        self.token_start = self.byte_start;
        self.token_content.clear();
    }

    fn create_token_ending_now(&self, kind: TokenKind) -> Token {
        // The current offset is at the start of the current character
        // The span includes start, but not the end
        // Therefore, we need to add 1 to the current offset
        Token::new(
            kind,
            SmtSpan::new_unchecked(self.token_start, self.byte_start.after_column()),
        )
    }

    fn create_token_ending_before(&self, kind: TokenKind) -> Token {
        // The current offset is at the start of the current character
        // The span includes start, but not the end
        // Therefore, if the token actually ended with the previous character,
        // we do not need to add anything.
        Token::new(
            kind,
            SmtSpan::new_unchecked(self.token_start, self.byte_start),
        )
    }

    fn create_zero_byte_token(&mut self, kind: TokenKind) -> Token {
        self.start_token();
        self.create_token_ending_before(kind)
    }

    fn current_token_error<E>(&self, kind: LexerErrorKind, c: U8OrEof) -> LexError<E> {
        // the spans starts at the token start and continues to the currently parsed,
        // where the error was detected, including it

        // if what we are parsing is a byte, add one to the end offset
        // since the span is a half-open range containing the start, but not end
        // if what we are parsing is EOF, do not add anything
        let end_offset = match c {
            U8OrEof::U8(_) => self.byte_start.after_column(),
            U8OrEof::Eof => self.byte_start,
        };

        let span = SmtSpan::new_unchecked(self.token_start, end_offset);
        LexError::Lexer(LexerError::new(kind, span))
    }

    /// Lex the whole input including EOF, sinking all produced tokens.
    ///
    /// This is a helper function for tests.
    #[cfg(test)]
    pub(crate) fn lex_all<E>(
        input: &[u8],
        mut sink: impl FnMut(Token) -> Result<(), E>,
    ) -> Result<(), LexError<E>> {
        let mut lexer = Lexer::new();
        for &c in input {
            lexer.lex_next(c, &mut sink)?;
        }
        Ok(())
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

/*
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
            LexerErrorKind::ForbiddenKeywordName,
            (0, 1, 1),
            (2, 1, 3),
        );
    }

    #[test]
    fn keyword_leading_digit() {
        assert_error(
            b":0",
            LexerErrorKind::ForbiddenKeywordName,
            (0, 1, 1),
            (2, 1, 3),
        );
        // the leading digit is rejected even when more characters would follow
        assert_error(
            b":0abc",
            LexerErrorKind::ForbiddenKeywordName,
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
            LexerErrorKind::ForbiddenKeywordName,
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
    fn current_location_follows_consumed_bytes() {
        let mut lexer = Lexer::new();
        assert_eq!(loc(lexer.current_location()), (0, 1, 1));
        for &c in b"ab\nc" {
            // the returned tokens must be drained before lexing the next byte
            lexer.lex_next(c).expect("valid input").for_each(drop);
        }
        assert_eq!(loc(lexer.current_location()), (4, 2, 2));
    }

    /// Expected token as `(type, start, end)`, with the locations as `(offset, line, column)`.
    type TokenLoc = (TokenType, Loc, Loc);

    /// Lexes the whole input and describes every token by its type and its span.
    fn token_spans(input: &[u8]) -> Vec<TokenLoc> {
        lex_all(input)
            .expect("test input must lex")
            .iter()
            .map(|token| {
                let span = token.span();
                (token.kind().ty(), loc(span.start()), loc(span.end()))
            })
            .collect()
    }

    #[test]
    fn spans_on_a_single_line() {
        // columns are one-based and counted in bytes
        assert_eq!(
            token_spans(b"(a 12)"),
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
            token_spans(b"(a)\n(b)"),
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
            token_spans(b"ab\ncd"),
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
            token_spans(b"|a\nb| c"),
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
            token_spans(b"\"a\nb\""),
            vec![
                (TokenType::String, (0, 1, 1), (5, 2, 3)),
                (TokenType::EndOfFile, (5, 2, 3), (5, 2, 3)),
            ]
        );
    }

    #[test]
    fn end_of_file_token_location() {
        // an empty input consists of the end-of-file token alone, at the stream start
        assert_eq!(
            token_spans(b""),
            vec![(TokenType::EndOfFile, (0, 1, 1), (0, 1, 1))]
        );
        // without a trailing line break, the end-of-file token is just past the last token
        assert_eq!(
            token_spans(b"(a)"),
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
            token_spans(b"(a)\n"),
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
            token_spans(b"a\r\nb"),
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
            token_spans(b"; c\nx"),
            vec![
                (TokenType::Symbol, (4, 2, 1), (5, 2, 2)),
                (TokenType::EndOfFile, (5, 2, 2), (5, 2, 2)),
            ]
        );
    }

    #[test]
    fn keyword_may_contain_digits_after_the_first_character() {
        // only the leading digit is forbidden; later ones are ordinary keyword characters
        assert_eq!(
            token_spans(b":a0 :x1y2"),
            vec![
                (TokenType::Keyword, (0, 1, 1), (3, 1, 4)),
                (TokenType::Keyword, (4, 1, 5), (9, 1, 10)),
                (TokenType::EndOfFile, (9, 1, 10), (9, 1, 10)),
            ]
        );
    }

    #[test]
    fn spans_of_every_token_type() {
        // the hash of a hexadecimal or binary literal belongs to its token,
        // and a reserved word spans the same bytes an ordinary symbol would
        assert_eq!(
            token_spans(b":kw #xAB #b01 1.5 \"s\" let"),
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

    #[test]
    fn decimal_token_payload_is_the_verbatim_source() {
        // the payload keeps the source bytes including the dot,
        // fractional leading zeros, and trailing zeros
        let tokens = lex_all(b"7.5 1.05 3.500 0.0").expect("valid input");
        let decimals: Vec<&[u8]> = tokens
            .iter()
            .filter_map(|token| match token.kind() {
                TokenKind::Decimal(decimal) => Some(decimal.as_slice()),
                _ => None,
            })
            .collect();
        assert_eq!(
            decimals,
            vec![
                b"7.5".as_slice(),
                b"1.05".as_slice(),
                b"3.500".as_slice(),
                b"0.0".as_slice(),
            ]
        );
    }

    /// Lexes the whole input and describes every token by its type and payload,
    /// with an empty payload for the token types that have none.
    fn token_payloads(input: &[u8]) -> Vec<(TokenType, Vec<u8>)> {
        lex_all(input)
            .expect("test input must lex")
            .iter()
            .map(|token| {
                let payload = match token.kind() {
                    TokenKind::Symbol(s) => s.as_slice(),
                    TokenKind::Keyword(k) => k.as_slice(),
                    TokenKind::Numeral(n) => n.as_slice(),
                    TokenKind::Decimal(d) => d.as_slice(),
                    TokenKind::Hexadecimal(h) => h.as_slice(),
                    TokenKind::Binary(b) => b.as_slice(),
                    TokenKind::String(s) => s.as_slice(),
                    _ => b"".as_slice(),
                };
                (token.kind().ty(), payload.to_vec())
            })
            .collect()
    }

    #[test]
    fn token_payloads_are_not_contaminated_by_previous_tokens() {
        // every payload-carrying kind in a row; each token is shorter than
        // the one before it, so any missed buffer clear shows up as leftover
        // bytes, and the reserved word fills the buffer without emitting it
        assert_eq!(
            token_payloads(b"abcd let e :k1 \"s\" |q| 12 3.4 #xA #b0"),
            vec![
                (TokenType::Symbol, b"abcd".to_vec()),
                (TokenType::Reserved(Reserved::Let), vec![]),
                (TokenType::Symbol, b"e".to_vec()),
                (TokenType::Keyword, b"k1".to_vec()),
                (TokenType::String, b"s".to_vec()),
                (TokenType::Symbol, b"q".to_vec()),
                (TokenType::Numeral, b"12".to_vec()),
                (TokenType::Decimal, b"3.4".to_vec()),
                (TokenType::Hexadecimal, b"A".to_vec()),
                (TokenType::Binary, b"0".to_vec()),
                (TokenType::EndOfFile, vec![]),
            ]
        );
    }

    #[test]
    fn empty_payloads_follow_nonempty_ones() {
        // the empty quoted symbol and string literal must not inherit
        // the content of the tokens lexed before them
        assert_eq!(
            token_payloads(b"|abc| || \"xy\" \"\" :a"),
            vec![
                (TokenType::Symbol, b"abc".to_vec()),
                (TokenType::Symbol, vec![]),
                (TokenType::String, b"xy".to_vec()),
                (TokenType::String, vec![]),
                (TokenType::Keyword, b"a".to_vec()),
                (TokenType::EndOfFile, vec![]),
            ]
        );
    }

    #[test]
    fn string_double_quote_escape_is_a_single_quote_in_the_payload() {
        assert_eq!(
            token_payloads(b"\"a\"\"b\" \"\"\"\""),
            vec![
                (TokenType::String, b"a\"b".to_vec()),
                (TokenType::String, b"\"".to_vec()),
                (TokenType::EndOfFile, vec![]),
            ]
        );
    }

    // --- Lexer misuse panics ---

    #[test]
    #[should_panic(expected = "cannot lex after a lexer error")]
    fn lexing_after_an_error_panics() {
        let mut lexer = Lexer::new();
        lexer.lex_next(b'7').expect("valid input").for_each(drop);
        // the backslash raises an error just after the numeral token was produced;
        // the discarded numeral must not obscure the after-error panic below
        assert!(lexer.lex_next(b'\\').is_err(), "expected a lexer error");
        let _ = lexer.lex_next(b' ');
    }

    #[test]
    #[should_panic(expected = "tokens returned by lexer must be consumed before further lexing")]
    fn lexing_with_unconsumed_tokens_panics() {
        let mut lexer = Lexer::new();
        // the open parenthesis produces a token, which is deliberately not consumed
        lexer.lex_next(b'(').expect("valid input");
        let _ = lexer.lex_next(b'a');
    }
}
*/

mod char_class;

use char_class::U8OrEof;

pub(crate) use char_class::CharClass;

use crate::{
    SmtBinDigitsView, SmtDecimalView, SmtHexDigitsView, SmtKeywordView, SmtLocation,
    SmtNumeralView, SmtSpan, SmtStringContentView, SmtSymbolView, String8,
    token::{Reserved, Token, TokenKind, TokenType},
};

/// A sequential handler of tokens.
pub trait TokenHandler {
    type Error;

    /// Sequentially handles one token.
    fn handle_token(&mut self, token: Token) -> Result<(), Self::Error>;
}

/// Mutable references over token handlers are token handlers.
impl<T: TokenHandler + ?Sized> TokenHandler for &mut T {
    type Error = T::Error;

    fn handle_token(&mut self, token: Token) -> Result<(), Self::Error> {
        (**self).handle_token(token)
    }
}

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

pub struct Lexer<H: TokenHandler> {
    /// Handler of produced tokens.
    handler: H,

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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexError<E> {
    Lexer(LexerError),
    Handler(E),
}

impl<H: TokenHandler> Lexer<H> {
    /// Constructs the lexer.
    pub fn new(handler: H) -> Self {
        Lexer {
            handler,
            state: LexerState::Normal,
            token_start: SmtLocation::initial(),
            token_content: String8::new(),
            byte_start: SmtLocation::initial(),
        }
    }

    pub fn current_location(&self) -> SmtLocation {
        self.byte_start
    }

    /// Lexes the whole input including EOF at the end.
    ///
    /// Sends the lexed tokens to the handler progressively.
    /// Returns on the first error.
    pub fn lex_all(&mut self, input: &[u8]) -> Result<(), LexError<H::Error>> {
        self.lex_slice(input)?;
        self.lex_eof()
    }

    /// Lexes the given slice, sending the lexed tokens to the handler.
    ///
    /// Panics if a previous call returned an error.
    pub fn lex_slice(&mut self, slice: &[u8]) -> Result<(), LexError<H::Error>> {
        for c in slice.iter().copied() {
            // lex the character
            if let Err(err) = self.lex_char(c) {
                // when a lexer error is raised, set lexer state to failed before propagating
                self.state = LexerState::Failed;
                return Err(err);
            }
            self.byte_start = self.byte_start.after_byte(c);
        }
        Ok(())
    }

    /// Lexes one byte, sending the lexed tokens to the handler.
    ///
    /// This is a slow convenience function, use `lex_slice` for speed
    /// if a slice is available.
    ///
    /// Panics if a previous call returned an error.
    pub fn lex_next(&mut self, c: u8) -> Result<(), LexError<H::Error>> {
        self.lex_slice(&[c])
    }

    /// Lexes end-of-file, sending the lexed tokens to the handler.
    ///
    /// Panics if a previous call returned an error.
    pub fn lex_eof(&mut self) -> Result<(), LexError<H::Error>> {
        let result = match self.state {
            LexerState::Normal | LexerState::Comment => {
                // nothing to do, we accept EOF even in comments
                Ok(())
            }
            LexerState::Fraction => self.finish_decimal(U8OrEof::Eof),
            LexerState::NumeralOrDecimal => self.finish_numeral(U8OrEof::Eof),
            LexerState::Hexadecimal => self.finish_hexadecimal(U8OrEof::Eof),
            LexerState::Binary => self.finish_binary(U8OrEof::Eof),
            LexerState::HexadecimalOrBinary => {
                // hash without selection following it
                Err(self.current_token_error(LexerErrorKind::BaseSelectionExpected, U8OrEof::Eof))
            }
            LexerState::StringLiteral => {
                // we are still within the string literal
                // forbidden as the literal must be totally enclosed by double quotes
                Err(self.current_token_error(LexerErrorKind::UnclosedStringLiteral, U8OrEof::Eof))
            }
            LexerState::StringLiteralDoubleQuote => {
                // string literal has ended by the previous character,
                // a quote directly before the end of the file
                self.finish_string_literal(U8OrEof::Eof)
            }
            LexerState::SimpleSymbol => self.finish_simple_symbol(U8OrEof::Eof),
            LexerState::Keyword => self.finish_keyword(U8OrEof::Eof),
            LexerState::QuotedSymbol => {
                // EOF forbidden as the symbol must be totally enclosed by pipes
                Err(self.current_token_error(LexerErrorKind::UnclosedQuotedSymbol, U8OrEof::Eof))
            }
            LexerState::Failed => {
                panic!("cannot lex after a lexer error")
            }
        };

        // everything processed, finish by sinking the EOF token
        let result = result.and_then(|()| self.sink_empty(TokenType::EndOfFile));

        match result {
            Ok(()) => Ok(()),
            Err(err) => {
                // switch to the failed state and propagate
                self.state = LexerState::Failed;
                Err(err)
            }
        }
    }

    fn lex_char(&mut self, c: u8) -> Result<(), LexError<H::Error>> {
        let state = match self.state {
            LexerState::Normal => return self.lex_normal(c),
            LexerState::Fraction => {
                match CharClass::from(c) {
                    CharClass::Digit => {
                        // add one digit, this will be to the fractional part (after the dot)
                        self.token_content.push(c);
                        LexerState::Fraction
                    }
                    _ => return self.finish_decimal(U8OrEof::U8(c)),
                }
            }
            LexerState::NumeralOrDecimal => {
                match CharClass::from(c) {
                    CharClass::Digit => {
                        // check that we are not in a leading zero condition
                        // this could not have been done when starting the numeral/decimal
                        // since just a single '0' is allowed
                        if self.token_content.as_slice() == b"0" {
                            return Err(self.current_token_error(
                                LexerErrorKind::NumeralLeadingZero,
                                U8OrEof::U8(c),
                            ));
                        }

                        // add one digit
                        self.token_content.push(c);
                        LexerState::NumeralOrDecimal
                    }
                    CharClass::Dot => {
                        // decimal, the next character will start fraction
                        // add the dot to the value
                        self.token_content.push(b'.');
                        LexerState::Fraction
                    }
                    _ => {
                        return self.finish_numeral(U8OrEof::U8(c));
                    }
                }
            }
            LexerState::Hexadecimal => {
                match c {
                    b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F' => {
                        // add hexadecimal digit
                        self.token_content.push(c);
                        LexerState::Hexadecimal
                    }
                    _ => {
                        return self.finish_hexadecimal(U8OrEof::U8(c));
                    }
                }
            }
            LexerState::Binary => {
                match c {
                    b'0' | b'1' => {
                        // add binary digit
                        self.token_content.push(c);
                        LexerState::Binary
                    }
                    _ => {
                        return self.finish_binary(U8OrEof::U8(c));
                    }
                }
            }

            LexerState::HexadecimalOrBinary => match c {
                b'x' => LexerState::Hexadecimal,
                b'b' => LexerState::Binary,
                _ => {
                    return Err(self.current_token_error(
                        LexerErrorKind::BaseSelectionExpected,
                        U8OrEof::U8(c),
                    ));
                }
            },
            LexerState::StringLiteral => {
                if c == b'\"' {
                    // we have a double quote in string literal
                    // it may be followed by another double quote for escaping
                    // otherwise, it will end the string literal
                    // put the lexer in a special state to handle the next character
                    LexerState::StringLiteralDoubleQuote
                } else if CharClass::from(c).is_printable_or_whitespace() {
                    // add to literal
                    self.token_content.push(c);
                    LexerState::StringLiteral
                } else {
                    // forbidden as not printable or whitespace
                    return Err(self.current_token_error(
                        LexerErrorKind::ForbiddenCharInString,
                        U8OrEof::U8(c),
                    ));
                }
            }
            LexerState::StringLiteralDoubleQuote => {
                if c == b'\"' {
                    // this has been a double-quote escape
                    // push a double-quote and continue lexing the string literal
                    self.token_content.push(b'\"');
                    LexerState::StringLiteral
                } else {
                    return self.finish_string_literal(U8OrEof::U8(c));
                }
            }
            LexerState::SimpleSymbol => {
                let class = CharClass::from(c);
                if class.is_allowed_in_simple_symbol() {
                    // add character
                    self.token_content.push(c);
                    LexerState::SimpleSymbol
                } else {
                    // simple symbol ended at the previous character
                    return self.finish_simple_symbol(U8OrEof::U8(c));
                }
            }
            LexerState::Keyword => {
                let class = CharClass::from(c);
                if class.is_allowed_in_simple_symbol() {
                    // make sure the keyword doesn't start with a digit
                    if self.token_content.is_empty() && matches!(class, CharClass::Digit) {
                        return Err(self.current_token_error(
                            LexerErrorKind::ForbiddenKeywordName,
                            U8OrEof::U8(c),
                        ));
                    }
                    // add character
                    self.token_content.push(c);
                    LexerState::Keyword
                } else {
                    // keyword ended at the previous character
                    return self.finish_keyword(U8OrEof::U8(c));
                }
            }
            LexerState::QuotedSymbol => {
                match c {
                    b'\\' => {
                        // backslash forbidden in quoted symbols
                        return Err(self.current_token_error(
                            LexerErrorKind::BackslashInQuotedSymbol,
                            U8OrEof::U8(c),
                        ));
                    }
                    b'|' => {
                        // end of quoted symbol, sink its token, this character is consumed
                        self.sink_current(TokenType::Symbol)?;
                        LexerState::Normal
                    }
                    c => {
                        if CharClass::from(c).is_printable_or_whitespace() {
                            // add the character to the quoted symbol and continue it
                            self.token_content.push(c);
                            LexerState::QuotedSymbol
                        } else {
                            // character forbidden as not printable or whitespace

                            return Err(self.current_token_error(
                                LexerErrorKind::ForbiddenCharInQuotedSymbol,
                                U8OrEof::U8(c),
                            ));
                        }
                    }
                }
            }
            LexerState::Comment => {
                if matches!(CharClass::from(c), CharClass::LineBreak) {
                    // end comment, ready for next token
                    LexerState::Normal
                } else {
                    // continue comment
                    LexerState::Comment
                }
            }
            LexerState::Failed => panic!("cannot lex after a lexer error"),
        };
        self.state = state;
        Ok(())
    }

    fn lex_normal(&mut self, c: u8) -> Result<(), LexError<H::Error>> {
        // start the token as we are in the normal state
        self.start_token();

        let state = match CharClass::from(c) {
            // whitespace, just continue lexing
            CharClass::Tab | CharClass::Space | CharClass::LineBreak => LexerState::Normal,

            // parentheses are tokens of their own
            CharClass::ParenOpen => {
                self.sink_current(TokenType::ParenOpen)?;
                LexerState::Normal
            }
            CharClass::ParenClose => {
                self.sink_current(TokenType::ParenClose)?;
                LexerState::Normal
            }

            // semicolon starts a comment
            CharClass::Semicolon => LexerState::Comment,

            CharClass::Digit => {
                // digit starts a numeral or a decimal
                // and determines the first digit value
                self.token_content.push(c);
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
                self.token_content.push(c);
                LexerState::SimpleSymbol
            }

            CharClass::Pipe => {
                // pipe starts a quoted symbol
                // the content remains empty here (the pipe is outside)
                LexerState::QuotedSymbol
            }

            _ => {
                // class disallowed here
                return Err(
                    self.current_token_error(LexerErrorKind::UnexpectedCharacter, U8OrEof::U8(c))
                );
            }
        };
        self.state = state;
        Ok(())
    }

    fn finish_decimal(&mut self, c: U8OrEof) -> Result<(), LexError<H::Error>> {
        let last_is_none_or_dot = self
            .token_content
            .as_slice()
            .last()
            .is_none_or(|c| *c == b'.');
        if last_is_none_or_dot {
            // decimals of the form 7. without any digit in fractional part are disallowed
            return Err(self.current_token_error(LexerErrorKind::FractionDigitExpected, c));
        }
        // sink new token and lex the character normally
        self.sink_and_lex_normal(TokenType::Decimal, c)
    }

    fn finish_numeral(&mut self, c: U8OrEof) -> Result<(), LexError<H::Error>> {
        // this was a numeral, we have no further checks
        // sink new token and lex the character normally
        self.sink_and_lex_normal(TokenType::Numeral, c)
    }

    fn finish_hexadecimal(&mut self, c: U8OrEof) -> Result<(), LexError<H::Error>> {
        if self.token_content.is_empty() {
            // had non-digit, zero digits disallowed
            return Err(self.current_token_error(LexerErrorKind::HexadecimalDigitExpected, c));
        }
        // had non-digit, nonzero digits
        // sink new token and lex the character normally
        self.sink_and_lex_normal(TokenType::Hexadecimal, c)
    }

    fn finish_binary(&mut self, c: U8OrEof) -> Result<(), LexError<H::Error>> {
        if self.token_content.is_empty() {
            // had non-digit, zero digits disallowed
            return Err(self.current_token_error(LexerErrorKind::BinaryDigitExpected, c));
        }
        // had non-digit, nonzero digits
        // sink new token and lex the character normally
        self.sink_and_lex_normal(TokenType::Binary, c)
    }

    fn finish_simple_symbol(&mut self, c: U8OrEof) -> Result<(), LexError<H::Error>> {
        // process reserved words
        let token_type = if let Some(reserved) = Reserved::from_symbol_opt(&self.token_content) {
            TokenType::Reserved(reserved)
        } else {
            TokenType::Symbol
        };

        // sink new token and lex the character normally
        self.sink_and_lex_normal(token_type, c)
    }

    fn finish_keyword(&mut self, c: U8OrEof) -> Result<(), LexError<H::Error>> {
        // ensure the keyword is not empty
        if self.token_content.is_empty() {
            return Err(self.current_token_error(LexerErrorKind::ForbiddenKeywordName, c));
        }
        // reserved words as keywords are prohibited
        if Reserved::from_symbol_opt(&self.token_content).is_some() {
            return Err(self.current_token_error(LexerErrorKind::KeywordReserved, c));
        }
        // sink new token and lex the character normally
        self.sink_and_lex_normal(TokenType::Keyword, c)
    }

    fn finish_string_literal(&mut self, c: U8OrEof) -> Result<(), LexError<H::Error>> {
        // literal has ended at the previous character
        // sink new token and lex the character normally
        self.sink_and_lex_normal(TokenType::String, c)
    }

    fn sink_current(&mut self, token_type: TokenType) -> Result<(), LexError<H::Error>> {
        self.sink_with_span(token_type, self.span_ending_now())
    }

    fn sink_empty(&mut self, token_type: TokenType) -> Result<(), LexError<H::Error>> {
        self.start_token();
        self.sink_with_span(token_type, self.span_ending_before())
    }

    fn sink_and_lex_normal(
        &mut self,
        token_type: TokenType,
        c: U8OrEof,
    ) -> Result<(), LexError<H::Error>> {
        // the token to be sunk actually ended with the last character
        // we just needed this character to decide that
        // sink the token
        self.sink_with_span(token_type, self.span_ending_before())?;
        // if the character is not EOF, lex it normally
        if let U8OrEof::U8(c) = c {
            self.lex_normal(c)?;
        }
        Ok(())
    }

    fn sink_with_span(
        &mut self,
        token_type: TokenType,
        span: SmtSpan,
    ) -> Result<(), LexError<H::Error>> {
        // pass the content by reference
        let value = self.token_content.as_view();

        // the caller of this function is responsible
        // for ensuring that the constructed token kind is valid
        let kind = match token_type {
            TokenType::ParenOpen => TokenKind::ParenOpen,
            TokenType::ParenClose => TokenKind::ParenClose,
            TokenType::Numeral => TokenKind::Numeral(SmtNumeralView::new_unchecked(value)),
            TokenType::Decimal => TokenKind::Decimal(SmtDecimalView::new_unchecked(value)),
            TokenType::Hexadecimal => {
                TokenKind::Hexadecimal(SmtHexDigitsView::new_unchecked(value))
            }
            TokenType::Binary => TokenKind::Binary(SmtBinDigitsView::new_unchecked(value)),
            TokenType::Symbol => TokenKind::Symbol(SmtSymbolView::new_unchecked(value)),
            TokenType::Reserved(reserved) => TokenKind::Reserved(reserved),
            TokenType::String => TokenKind::String(SmtStringContentView::new_unchecked(value)),
            TokenType::Keyword => TokenKind::Keyword(SmtKeywordView::new_unchecked(value)),
            TokenType::EndOfFile => TokenKind::EndOfFile,
        };

        self.handler
            .handle_token(Token::new(kind, span))
            .map_err(LexError::Handler)
    }

    fn start_token(&mut self) {
        // update the token start and clear the token string
        self.token_start = self.byte_start;
        self.token_content.clear();
    }

    fn span_ending_now(&self) -> SmtSpan {
        // The current offset is at the start of the current character
        // The span includes start, but not the end
        // Therefore, we need to add 1 to the current offset
        SmtSpan::new_unchecked(self.token_start, self.byte_start.after_column())
    }

    fn span_ending_before(&self) -> SmtSpan {
        // The current offset is at the start of the current character
        // The span includes start, but not the end
        // Therefore, if the token actually ended with the previous character,
        // we do not need to add anything.
        SmtSpan::new_unchecked(self.token_start, self.byte_start)
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

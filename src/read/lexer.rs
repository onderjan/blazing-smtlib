mod char_class;

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
            LexerState::Fraction => self.finish_decimal(false),
            LexerState::NumeralOrDecimal => self.finish_numeral(),
            LexerState::Hexadecimal => self.finish_hexadecimal(false),
            LexerState::Binary => self.finish_binary(false),
            LexerState::HexadecimalOrBinary => {
                // hash without selection following it
                Err(self.current_token_error(LexerErrorKind::BaseSelectionExpected, false))
            }
            LexerState::StringLiteral => {
                // we are still within the string literal
                // forbidden as the literal must be totally enclosed by double quotes
                Err(self.current_token_error(LexerErrorKind::UnclosedStringLiteral, false))
            }
            LexerState::StringLiteralDoubleQuote => {
                // string literal has ended by the previous character,
                // a quote directly before the end of the file
                self.finish_string_literal()
            }
            LexerState::SimpleSymbol => self.finish_simple_symbol(),
            LexerState::Keyword => self.finish_keyword(false),
            LexerState::QuotedSymbol => {
                // EOF forbidden as the symbol must be totally enclosed by pipes
                Err(self.current_token_error(LexerErrorKind::UnclosedQuotedSymbol, false))
            }
            LexerState::Failed => {
                panic!("cannot lex after a lexer error")
            }
        };

        // everything processed, start the EOF token and sink it
        self.start_token();
        let result = result.and_then(|()| self.sink(TokenType::EndOfFile, self.end_before_byte()));

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
                    _ => {
                        // finish previously ended token and process current normally
                        self.finish_decimal(true)?;
                        return self.lex_normal(c);
                    }
                }
            }
            LexerState::NumeralOrDecimal => {
                match CharClass::from(c) {
                    CharClass::Digit => {
                        // check that we are not in a leading zero condition
                        // this could not have been done when starting the numeral/decimal
                        // since just a single '0' is allowed
                        if self.token_content.as_slice() == b"0" {
                            return Err(
                                self.current_token_error(LexerErrorKind::NumeralLeadingZero, true)
                            );
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
                        // finish previously ended token and process current normally
                        self.finish_numeral()?;
                        return self.lex_normal(c);
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
                        // finish previously ended token and process current normally
                        self.finish_hexadecimal(true)?;
                        return self.lex_normal(c);
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
                        // finish previously ended token and process current normally
                        self.finish_binary(true)?;
                        return self.lex_normal(c);
                    }
                }
            }

            LexerState::HexadecimalOrBinary => match c {
                b'x' => LexerState::Hexadecimal,
                b'b' => LexerState::Binary,
                _ => {
                    return Err(
                        self.current_token_error(LexerErrorKind::BaseSelectionExpected, true)
                    );
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
                    return Err(
                        self.current_token_error(LexerErrorKind::ForbiddenCharInString, true)
                    );
                }
            }
            LexerState::StringLiteralDoubleQuote => {
                if c == b'\"' {
                    // this has been a double-quote escape
                    // push a double-quote and continue lexing the string literal
                    self.token_content.push(b'\"');
                    LexerState::StringLiteral
                } else {
                    // the previous character was really a quote ending the string literal
                    // finish previously ended token and process current normally
                    self.finish_string_literal()?;
                    return self.lex_normal(c);
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
                    // finish previously ended token and process current normally
                    self.finish_simple_symbol()?;
                    return self.lex_normal(c);
                }
            }
            LexerState::Keyword => {
                let class = CharClass::from(c);
                if class.is_allowed_in_simple_symbol() {
                    // make sure the keyword doesn't start with a digit
                    if self.token_content.is_empty() && matches!(class, CharClass::Digit) {
                        return Err(
                            self.current_token_error(LexerErrorKind::ForbiddenKeywordName, true)
                        );
                    }
                    // add character
                    self.token_content.push(c);
                    LexerState::Keyword
                } else {
                    // keyword ended at the previous character
                    // finish previously ended token and process current normally
                    self.finish_keyword(true)?;
                    return self.lex_normal(c);
                }
            }
            LexerState::QuotedSymbol => {
                match c {
                    b'\\' => {
                        // backslash forbidden in quoted symbols
                        return Err(
                            self.current_token_error(LexerErrorKind::BackslashInQuotedSymbol, true)
                        );
                    }
                    b'|' => {
                        // end of quoted symbol, sink its token, this character is consumed
                        self.sink(TokenType::Symbol, self.end_after_byte())?;
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
                                true,
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
                self.sink(TokenType::ParenOpen, self.end_after_byte())?;
                LexerState::Normal
            }
            CharClass::ParenClose => {
                self.sink(TokenType::ParenClose, self.end_after_byte())?;
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
                return Err(self.current_token_error(LexerErrorKind::UnexpectedCharacter, true));
            }
        };
        self.state = state;
        Ok(())
    }

    fn finish_decimal(&mut self, ended_by_byte: bool) -> Result<(), LexError<H::Error>> {
        let last_is_none_or_dot = self
            .token_content
            .as_slice()
            .last()
            .is_none_or(|c| *c == b'.');
        if last_is_none_or_dot {
            // decimals of the form 7. without any digit in fractional part are disallowed
            return Err(
                self.current_token_error(LexerErrorKind::FractionDigitExpected, ended_by_byte)
            );
        }
        // sink new token
        self.sink(TokenType::Decimal, self.end_before_byte())
    }

    fn finish_numeral(&mut self) -> Result<(), LexError<H::Error>> {
        // this was a numeral, we have no further checks
        // sink new token
        self.sink(TokenType::Numeral, self.end_before_byte())
    }

    fn finish_hexadecimal(&mut self, ended_by_byte: bool) -> Result<(), LexError<H::Error>> {
        if self.token_content.is_empty() {
            // had non-digit, zero digits disallowed
            return Err(
                self.current_token_error(LexerErrorKind::HexadecimalDigitExpected, ended_by_byte)
            );
        }
        // had non-digit, nonzero digits
        // sink new token
        self.sink(TokenType::Hexadecimal, self.end_before_byte())
    }

    fn finish_binary(&mut self, ended_by_byte: bool) -> Result<(), LexError<H::Error>> {
        if self.token_content.is_empty() {
            // had non-digit, zero digits disallowed
            return Err(
                self.current_token_error(LexerErrorKind::BinaryDigitExpected, ended_by_byte)
            );
        }
        // had non-digit, nonzero digits
        // sink new token
        self.sink(TokenType::Binary, self.end_before_byte())
    }

    fn finish_simple_symbol(&mut self) -> Result<(), LexError<H::Error>> {
        // process reserved words
        let token_type = if let Some(reserved) = Reserved::from_symbol_opt(&self.token_content) {
            TokenType::Reserved(reserved)
        } else {
            TokenType::Symbol
        };
        // sink new token
        self.sink(token_type, self.end_before_byte())
    }

    fn finish_keyword(&mut self, ended_by_byte: bool) -> Result<(), LexError<H::Error>> {
        // ensure the keyword is not empty
        if self.token_content.is_empty() {
            return Err(
                self.current_token_error(LexerErrorKind::ForbiddenKeywordName, ended_by_byte)
            );
        }
        // reserved words as keywords are prohibited
        if Reserved::from_symbol_opt(&self.token_content).is_some() {
            return Err(self.current_token_error(LexerErrorKind::KeywordReserved, ended_by_byte));
        }
        // sink new token
        self.sink(TokenType::Keyword, self.end_before_byte())
    }

    fn finish_string_literal(&mut self) -> Result<(), LexError<H::Error>> {
        // literal has ended at the previous character
        // sink new token
        self.sink(TokenType::String, self.end_before_byte())
    }

    fn sink(&mut self, token_type: TokenType, end: SmtLocation) -> Result<(), LexError<H::Error>> {
        // construct the span
        let span = SmtSpan::new_unchecked(self.token_start, end);

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

    fn end_before_byte(&self) -> SmtLocation {
        self.byte_start
    }

    fn end_after_byte(&self) -> SmtLocation {
        self.byte_start.after_column()
    }

    fn error_end(&self, ended_by_byte: bool) -> SmtLocation {
        // the span starts at the token start
        // if we have a pending byte, it includes it at the end
        // if not, it ends before it
        if ended_by_byte {
            self.end_after_byte()
        } else {
            self.end_before_byte()
        }
    }

    fn current_token_error<E>(&self, kind: LexerErrorKind, ended_by_byte: bool) -> LexError<E> {
        let end = self.error_end(ended_by_byte);
        let span = SmtSpan::new_unchecked(self.token_start, end);
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

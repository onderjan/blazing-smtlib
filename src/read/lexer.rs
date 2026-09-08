mod char_class;

pub(crate) use char_class::CharClass;

use crate::{
    SmtBinDigitsView, SmtDecimalView, SmtHexDigitsView, SmtKeywordView, SmtLocation,
    SmtNumeralView, SmtSpan, SmtStringContentView, SmtSymbolView, String8,
    read::lexer::char_class::{FLAGS, QUOTED_PLAIN, SIMPLE_SYMBOL},
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
    NumeralOrDecimal,
    Fraction,
    HexadecimalOrBinary,
    Hexadecimal,
    Binary,
    StringLiteral,
    StringLiteralDoubleQuote,
    SimpleSymbol,
    QuotedSymbol,
    Keyword,
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

    /// Offset of the start of the byte being processed during lexing.
    ///
    /// It only advances after byte consumption.
    offset: u64,

    /// Number of the latest line (zero-based).
    ///
    /// It only advances after consumption of LF.
    line: u64,

    /// Offset of the start of the current line (after line break, zero-based)
    ///
    /// It only advances after consumption of LF.
    line_start: u64,
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
            offset: 0,
            line: 0,
            line_start: 0,
        }
    }

    pub fn current_location(&self) -> SmtLocation {
        // the column is computed by subtracting the line start offset from current offset
        let column = self.offset - self.line_start;
        SmtLocation::new(self.offset, self.line, column)
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
        // lex the slice
        match self.lex_slice_inner(slice) {
            Ok(()) => Ok(()),
            Err(err) => {
                // when a lexer error is raised, set lexer state to failed before propagating
                self.state = LexerState::Failed;
                Err(err)
            }
        }
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
            LexerState::SimpleSymbol => self.finish_simple_symbol(self.end_before_byte()),
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
            Ok(()) => {
                // everything good, move to normal state
                self.state = LexerState::Normal;
                Ok(())
            }
            Err(err) => {
                // switch to the failed state and propagate
                self.state = LexerState::Failed;
                Err(err)
            }
        }
    }

    fn lex_slice_inner(&mut self, mut rest: &[u8]) -> Result<(), LexError<H::Error>> {
        while !rest.is_empty() {
            let consumed = match self.state {
                LexerState::Normal => self.lex_normal(rest)?,
                LexerState::NumeralOrDecimal => self.lex_numeral_or_decimal(rest)?,
                LexerState::Fraction => self.lex_fraction(rest)?,
                LexerState::HexadecimalOrBinary => self.lex_hexadecimal_or_binary(rest)?,
                LexerState::Hexadecimal => self.lex_hexadecimal(rest)?,
                LexerState::Binary => self.lex_binary(rest)?,
                LexerState::StringLiteral => self.lex_string_literal(rest, false)?,
                LexerState::StringLiteralDoubleQuote => self.lex_string_literal(rest, true)?,
                LexerState::SimpleSymbol => self.lex_simple_symbol(rest)?,
                LexerState::QuotedSymbol => {
                    let consumed = self.lex_quoted_symbol(rest)?;
                    // the newlines are already marked, just advance the offset
                    self.offset += consumed as u64;
                    rest = &rest[consumed..];
                    continue;
                }
                LexerState::Keyword => self.lex_keyword(rest)?,
                LexerState::Comment => self.lex_comment(rest)?,
                LexerState::Failed => panic!("cannot lex after a lexer error"),
            };
            // advance the position and continue with the rest
            self.advance(rest, consumed);
            rest = &rest[consumed..];
        }
        Ok(())
    }

    fn lex_normal(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        let c = slice[0];

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
        Ok(1)
    }

    fn lex_numeral_or_decimal(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        let c = slice[0];

        match CharClass::from(c) {
            CharClass::Digit => {
                // check that we are not in a leading zero condition
                // this could not have been done when starting the numeral/decimal
                // since just a single '0' is allowed
                if self.token_content.as_slice() == b"0" {
                    return Err(self.current_token_error(LexerErrorKind::NumeralLeadingZero, true));
                }

                // add one digit
                self.token_content.push(c);
            }
            CharClass::Dot => {
                // decimal, the next character will start fraction
                // add the dot to the value
                self.token_content.push(b'.');
                self.state = LexerState::Fraction;
            }
            _ => {
                // finish previously ended token
                self.finish_numeral()?;
                // force the byte to be processed normally
                self.state = LexerState::Normal;
                return Ok(0);
            }
        }

        Ok(1)
    }

    fn lex_fraction(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        let c = slice[0];

        match CharClass::from(c) {
            CharClass::Digit => {
                // add one digit, this will be to the fractional part (after the dot)
                self.token_content.push(c);
            }
            _ => {
                // finish previously ended token
                self.finish_decimal(true)?;
                // force the byte to be processed normally
                self.state = LexerState::Normal;
                return Ok(0);
            }
        }

        Ok(1)
    }

    fn lex_hexadecimal_or_binary(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        let c = slice[0];

        self.state = match c {
            b'x' => LexerState::Hexadecimal,
            b'b' => LexerState::Binary,
            _ => {
                return Err(self.current_token_error(LexerErrorKind::BaseSelectionExpected, true));
            }
        };

        Ok(1)
    }

    fn lex_hexadecimal(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        let c = slice[0];

        match c {
            b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F' => {
                // add hexadecimal digit
                self.token_content.push(c);
            }
            _ => {
                // finish previously ended token
                self.finish_hexadecimal(true)?;
                // force the byte to be processed normally
                self.state = LexerState::Normal;
                return Ok(0);
            }
        }

        Ok(1)
    }

    fn lex_binary(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        let c = slice[0];

        match c {
            b'0' | b'1' => {
                // add binary digit
                self.token_content.push(c);
            }
            _ => {
                // finish previously ended token
                self.finish_binary(true)?;
                // force the byte to be processed normally
                self.state = LexerState::Normal;
                return Ok(0);
            }
        }

        Ok(1)
    }

    fn lex_string_literal(
        &mut self,
        slice: &[u8],
        being_closed: bool,
    ) -> Result<usize, LexError<H::Error>> {
        let c = slice[0];

        if being_closed {
            if c == b'\"' {
                // this has been a double-quote escape
                // push a double-quote and continue lexing the string literal
                self.token_content.push(b'\"');
                self.state = LexerState::StringLiteral;
            } else {
                // the previous character was really a quote ending the string literal
                // finish previously ended token
                self.finish_string_literal()?;
                // force the byte to be processed normally
                self.state = LexerState::Normal;
                return Ok(0);
            }
        } else {
            if c == b'\"' {
                // we have a double quote in string literal
                // it may be followed by another double quote for escaping
                // otherwise, it will end the string literal
                // put the lexer in a special state to handle the next character
                self.state = LexerState::StringLiteralDoubleQuote;
            } else if CharClass::from(c).is_printable_or_whitespace() {
                // add to literal
                self.token_content.push(c);
            } else {
                // forbidden as not printable or whitespace
                return Err(self.current_token_error(LexerErrorKind::ForbiddenCharInString, true));
            }
        }

        Ok(1)
    }

    fn lex_simple_symbol(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        // find the first byte that is not a simple symbol
        let index = Self::run_end(slice, SIMPLE_SYMBOL);

        // extend the token from slice
        self.token_content.extend_from_slice(&slice[..index]);

        if index < slice.len() {
            // we have successfully consumed the symbol, finish it
            // compute the end location, no line feeds are allowed in simple symbols
            self.finish_simple_symbol(self.current_line_location(index))?;
            self.state = LexerState::Normal;
        }

        Ok(index)
    }

    fn lex_quoted_symbol(&mut self, mut rest: &[u8]) -> Result<usize, LexError<H::Error>> {
        let mut consumed = 0;
        loop {
            // find the first byte that is not a quoted symbol
            let index = Self::run_end(rest, QUOTED_PLAIN);
            let after_slice_position = consumed + index + 1;

            // inspect the problematic byte
            match rest.get(index) {
                Some(b'|') => {
                    // end of quoted symbol, extend and sink its token
                    // the closing pipe is not consumed but delimits the token
                    self.token_content.extend_from_slice(&rest[..index]);
                    self.sink(
                        TokenType::Symbol,
                        self.current_line_location(after_slice_position),
                    )?;
                    // return to normal, consuming bytes including the pipe
                    self.state = LexerState::Normal;
                    return Ok(after_slice_position);
                }
                Some(b'\\') => {
                    // backslash is forbidden in quoted symbols
                    return Err(self.error_ending_at(
                        LexerErrorKind::BackslashInQuotedSymbol,
                        after_slice_position,
                    ));
                }
                Some(b'\n') => {
                    // mark the line feed at the given position
                    self.mark_line_feed_at(consumed + index);
                    // prepare for the next run
                    // move everything including this LF to token content
                    self.token_content.extend_from_slice(&rest[..index + 1]);
                    // take it out of this slice and remember it is consumed
                    rest = &rest[index + 1..];
                    consumed += index + 1;
                }
                Some(_) => {
                    // forbidden character
                    return Err(self.error_ending_at(
                        LexerErrorKind::ForbiddenCharInQuotedSymbol,
                        after_slice_position,
                    ));
                }
                None => {
                    // we ran out of bytes before the token ended
                    // extend content and keep the quoted symbol state
                    self.token_content.extend_from_slice(rest);
                    return Ok(consumed + rest.len());
                }
            }
        }
    }

    fn lex_keyword(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        let c = slice[0];

        let class = CharClass::from(c);
        if class.is_allowed_in_simple_symbol() {
            // make sure the keyword doesn't start with a digit
            if self.token_content.is_empty() && matches!(class, CharClass::Digit) {
                return Err(self.current_token_error(LexerErrorKind::ForbiddenKeywordName, true));
            }
            // add character
            self.token_content.push(c);
        } else {
            // keyword ended at the previous character
            // finish previously ended token
            self.finish_keyword(true)?;
            // force the byte to be processed normally
            self.state = LexerState::Normal;
            return Ok(0);
        }

        Ok(1)
    }

    fn lex_comment(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        let c = slice[0];

        self.state = if matches!(CharClass::from(c), CharClass::LineBreak) {
            // end comment, ready for next token
            LexerState::Normal
        } else {
            // continue comment
            LexerState::Comment
        };

        Ok(1)
    }

    fn advance(&mut self, slice: &[u8], consumed: usize) {
        for c in slice[..consumed].iter().copied() {
            self.offset += 1;
            if c == b'\n' {
                // increment line number
                self.line += 1;
                // the line starts after the newline character
                self.line_start = self.offset;
            }
        }
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

    fn finish_simple_symbol(&mut self, end: SmtLocation) -> Result<(), LexError<H::Error>> {
        // process reserved words
        let token_type = if let Some(reserved) = Reserved::from_symbol_opt(&self.token_content) {
            TokenType::Reserved(reserved)
        } else {
            TokenType::Symbol
        };
        // sink new token
        self.sink(token_type, end)
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
        self.token_start = self.end_before_byte();
        self.token_content.clear();
    }

    fn end_before_byte(&self) -> SmtLocation {
        self.current_location()
    }

    fn end_after_byte(&self) -> SmtLocation {
        self.current_location().after_column()
    }

    fn current_line_location(&self, position: usize) -> SmtLocation {
        // valid if there are no line feeds before the given position
        //
        // scanners that can pass a line feed must update line and line_start
        // before calling this
        let offset = self.offset + position as u64;
        SmtLocation::new(offset, self.line, offset - self.line_start)
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

    fn error_ending_at<E>(&self, kind: LexerErrorKind, position: usize) -> LexError<E> {
        let end = self.current_line_location(position);
        let span = SmtSpan::new_unchecked(self.token_start, end);
        LexError::Lexer(LexerError::new(kind, span))
    }

    fn mark_line_feed_at(&mut self, position: usize) {
        // when parsing a run, this is used to mark a line feed
        // the locations must only refer to positions after it afterwards
        self.line += 1;
        self.line_start = self.offset + position as u64 + 1;
    }

    #[inline]
    fn run_end(slice: &[u8], mask: u8) -> usize {
        // the run is over bytes which have at least one mask flag set
        // return the byte that ends the run or slice length if there is none
        slice
            .iter()
            .position(|c| FLAGS[*c as usize] & mask == 0)
            .unwrap_or(slice.len())
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

mod char_class;

pub(crate) use char_class::CharClass;

use crate::{
    SmtBinDigitsView, SmtDecimalView, SmtHexDigitsView, SmtKeywordView, SmtLocation,
    SmtNumeralView, SmtSpan, SmtStringContentView, SmtSymbolView, String8,
    read::lexer::char_class::{
        BINARY_DIGIT, COMMENT_PLAIN, DIGIT, FLAGS, HEX_DIGIT, NON_LF_WHITESPACE, QUOTED_PLAIN,
        SIMPLE_SYMBOL, STRING_PLAIN,
    },
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
    BaseSelection,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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

#[derive(Clone, Copy)]
struct DigitRun {
    flag: u8,
    token_type: TokenType,
    empty_error: LexerErrorKind,
}
const HEXADECIMAL_RUN: DigitRun = DigitRun {
    flag: HEX_DIGIT,
    token_type: TokenType::Hexadecimal,
    empty_error: LexerErrorKind::HexadecimalDigitExpected,
};
const BINARY_RUN: DigitRun = DigitRun {
    flag: BINARY_DIGIT,
    token_type: TokenType::Binary,
    empty_error: LexerErrorKind::BinaryDigitExpected,
};

/// Helper struct for where a token ended.
#[derive(Clone, Copy)]
struct TokenEnd {
    /// The position after `Lexer.offset` where the token ended.
    position: usize,
    /// Whether the token end was detected at a byte that is not a part of the token.
    at_byte: bool,
}

impl TokenEnd {
    const EOF: TokenEnd = TokenEnd {
        position: 0,
        at_byte: false,
    };
    fn at_byte(position: usize) -> Self {
        TokenEnd {
            position,
            at_byte: true,
        }
    }
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
        self.location_at(0)
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
            LexerState::Fraction => self.finish_decimal(TokenEnd::EOF),
            LexerState::NumeralOrDecimal => self.finish_numeral(TokenEnd::EOF),
            LexerState::Hexadecimal => self.finish_digit_run(HEXADECIMAL_RUN, TokenEnd::EOF),
            LexerState::Binary => self.finish_digit_run(BINARY_RUN, TokenEnd::EOF),
            LexerState::BaseSelection => {
                // hash without selection following it
                Err(self.error(LexerErrorKind::BaseSelectionExpected, TokenEnd::EOF))
            }
            LexerState::StringLiteral => {
                // we are still within the string literal
                // forbidden as the literal must be totally enclosed by double quotes
                Err(self.error(LexerErrorKind::UnclosedStringLiteral, TokenEnd::EOF))
            }
            LexerState::StringLiteralDoubleQuote => {
                // string literal has ended by the previous character,
                // a quote directly before the end of the file
                self.finish_string_literal(TokenEnd::EOF)
            }
            LexerState::SimpleSymbol => self.finish_simple_symbol(TokenEnd::EOF),
            LexerState::Keyword => self.finish_keyword(TokenEnd::EOF),
            LexerState::QuotedSymbol => {
                // EOF forbidden as the symbol must be totally enclosed by pipes
                Err(self.error(LexerErrorKind::UnclosedQuotedSymbol, TokenEnd::EOF))
            }
            LexerState::Failed => {
                panic!("cannot lex after a lexer error")
            }
        };

        // everything processed, start the EOF token and sink it
        self.start_token(0);
        let result = result.and_then(|()| self.sink(TokenType::EndOfFile, TokenEnd::EOF));

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
                LexerState::Fraction => self.lex_fraction_from(rest, 0)?,
                LexerState::BaseSelection => self.lex_base_selection(rest)?,
                LexerState::Hexadecimal => self.lex_digit_run(rest, HEXADECIMAL_RUN)?,
                LexerState::Binary => self.lex_digit_run(rest, BINARY_RUN)?,
                LexerState::StringLiteral | LexerState::StringLiteralDoubleQuote => {
                    self.lex_string_literal(rest)?
                }
                LexerState::SimpleSymbol => self.lex_simple_symbol(rest)?,
                LexerState::QuotedSymbol => self.lex_quoted_symbol(rest)?,
                LexerState::Keyword => self.lex_keyword(rest)?,
                LexerState::Comment => self.lex_comment(rest)?,
                LexerState::Failed => panic!("cannot lex after a lexer error"),
            };
            // advance the offset by the number of consumed bytes
            // the line positions are updated by the arm functions above
            self.offset += consumed as u64;
            // move after consumed bytes
            rest = &rest[consumed..];
        }
        Ok(())
    }

    fn lex_normal(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        let mut index = 0;

        loop {
            // skip whitespace except for line feeds
            // those must be processed for line offsets
            index += Self::run_end(&slice[index..], NON_LF_WHITESPACE);
            let c = match slice.get(index) {
                Some(b'\n') => {
                    // mark the line feed, continue skipping whitespace
                    self.mark_line_feed_at(index);
                    index += 1;
                    continue;
                }
                Some(c) => {
                    // an interesting character, break
                    *c
                }
                None => {
                    // we have consumed every byte
                    return Ok(slice.len());
                }
            };

            // start the token as we are in the normal state
            self.start_token(index);
            let state = match c {
                b'(' => {
                    // parentheses are tokens of their own
                    // sink the token
                    self.sink(TokenType::ParenOpen, TokenEnd::at_byte(index + 1))?;
                    // since we are back in the normal state, just increment the index and continue the loop
                    index += 1;
                    continue;
                }
                b')' => {
                    // parentheses are tokens of their own
                    // sink the token
                    self.sink(TokenType::ParenClose, TokenEnd::at_byte(index + 1))?;
                    // since we are back in the normal state, just increment the index and continue the loop
                    index += 1;
                    continue;
                }
                b';' => LexerState::Comment,
                b'#' => LexerState::BaseSelection,
                b'"' => LexerState::StringLiteral,
                b':' => LexerState::Keyword,
                b'|' => LexerState::QuotedSymbol,
                _ => {
                    // digits start numerals/decimals
                    // the remaining simple-symbol-allowed bytes start simple symbols
                    let flags = FLAGS[c as usize];
                    if flags & DIGIT != 0 {
                        self.token_content.push(c);
                        LexerState::NumeralOrDecimal
                    } else if flags & SIMPLE_SYMBOL != 0 {
                        self.token_content.push(c);
                        LexerState::SimpleSymbol
                    } else {
                        return Err(self.error_at(LexerErrorKind::UnexpectedCharacter, index + 1));
                    }
                }
            };
            // change the state and end normal parsing
            // having consumed bytes up to and including to the current one
            self.state = state;
            return Ok(index + 1);
        }
    }

    fn lex_numeral_or_decimal(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        // find the first byte that is not a digit
        let index = Self::run_end(slice, DIGIT);

        // check that we are not in a leading zero condition
        // this could not have been done when starting the numeral/decimal
        // since just a single '0' is allowed

        // as we emplace the first digit in the normal state,
        // it suffices for the leading zero condition that
        // 1. at least one additional digit has been consumed
        // 2. the content parsed previously is exactly "0"
        if index > 0 && self.token_content.as_slice() == b"0" {
            return Err(self.error_at(LexerErrorKind::NumeralLeadingZero, 1));
        }

        // extend the token from slice
        self.token_content.extend_from_slice(&slice[..index]);

        match slice.get(index) {
            Some(b'.') => {
                // decimal, the next character will start fraction
                // add the dot and immediately start parsing the fraction after it
                self.token_content.push(b'.');
                self.lex_fraction_from(slice, index + 1)
            }
            Some(_) => {
                // we have successfully consumed the numeral, finish it
                // compute the end location, no line feeds are allowed in simple symbols
                self.finish_numeral(TokenEnd::at_byte(index))?;
                // move back to normal lexer state, not consuming the current byte
                self.state = LexerState::Normal;
                Ok(index)
            }
            None => {
                // we have run out of bytes for now
                Ok(index)
            }
        }
    }

    fn lex_fraction_from(
        &mut self,
        slice: &[u8],
        start: usize,
    ) -> Result<usize, LexError<H::Error>> {
        // find the first byte in the remainder that is not a digit
        let end = start + Self::run_end(&slice[start..], DIGIT);
        // extend the token from slice
        self.token_content.extend_from_slice(&slice[start..end]);
        if end < slice.len() {
            // we have successfully consumed the fraction, finish the decimal
            // compute the end location, no line feeds are allowed in simple symbols
            self.finish_decimal(TokenEnd::at_byte(end))?;
            self.state = LexerState::Normal;
        } else {
            // we ran out of bytes for now
            self.state = LexerState::Fraction;
        }
        Ok(end)
    }

    fn lex_base_selection(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        let c = slice[0];
        self.state = match c {
            b'x' => LexerState::Hexadecimal,
            b'b' => LexerState::Binary,
            _ => {
                return Err(self.error_at(LexerErrorKind::BaseSelectionExpected, 1));
            }
        };
        Ok(1)
    }

    /// Lexes a digit run, either hexadecimal or binary.
    fn lex_digit_run(&mut self, slice: &[u8], run: DigitRun) -> Result<usize, LexError<H::Error>> {
        // find the first byte that is not allowed in the run
        let index = Self::run_end(slice, run.flag);
        // extend the token from slice
        self.token_content.extend_from_slice(&slice[..index]);
        if index < slice.len() {
            // we have successfully consumed the digit run, finish it
            // compute the end location, no line feeds are allowed in simple symbols
            self.finish_digit_run(run, TokenEnd::at_byte(index))?;
            self.state = LexerState::Normal;
        }
        Ok(index)
    }

    fn lex_string_literal(&mut self, mut rest: &[u8]) -> Result<usize, LexError<H::Error>> {
        let mut consumed = 0;
        while !rest.is_empty() {
            if matches!(self.state, LexerState::StringLiteralDoubleQuote) {
                // we need to react to the literal being closed by a previous double-quote
                // look at the first byte
                if rest[0] != b'\"' {
                    // the previous character was really a quote ending the string literal
                    // finish the previously ended token
                    self.finish_string_literal(TokenEnd::at_byte(consumed))?;
                    // set lexer to normal state and return, not consuming the current byte
                    self.state = LexerState::Normal;
                    return Ok(consumed);
                } else {
                    // this has been a double-quote escape
                    // consume the first byte
                    rest = &rest[1..];
                    consumed += 1;
                    // push a double-quote byte (just one, we encountered two)
                    self.token_content.push(b'\"');
                    // return to string-literal state and continue parsing
                    self.state = LexerState::StringLiteral;
                }
            }

            // find the first byte that is not a plain string byte
            let index = Self::run_end(rest, STRING_PLAIN);

            match rest.get(index) {
                Some(b'\n') => {
                    // mark the line feed
                    self.mark_line_feed_at(consumed + index);
                    // extend with & consume the run including the line feed
                    self.token_content.extend_from_slice(&rest[..=index]);
                    rest = &rest[index + 1..];
                    consumed += index + 1;
                    // continue parsing
                }
                Some(b'\"') => {
                    // we have a double quote in string literal
                    // only extend the content with bytes before it
                    self.token_content.extend_from_slice(&rest[..index]);
                    // consume the quote and everything before it
                    rest = &rest[index + 1..];
                    consumed += index + 1;
                    // the quote may be followed by another double quote for escaping
                    // otherwise, it will end the string literal
                    // put the lexer in a special state to handle the next character
                    self.state = LexerState::StringLiteralDoubleQuote;
                    // continue parsing
                }
                Some(_) => {
                    // forbidden, not printable or whitespace
                    return Err(
                        self.error_at(LexerErrorKind::ForbiddenCharInString, consumed + index + 1)
                    );
                }
                None => {
                    // extend the content with the rest
                    self.token_content.extend_from_slice(rest);
                    // we have nothing more to consume, return
                    return Ok(consumed + rest.len());
                }
            }
        }
        Ok(consumed)
    }

    fn lex_simple_symbol(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        // find the first byte that is not a simple symbol
        let index = Self::run_end(slice, SIMPLE_SYMBOL);

        // extend the token from slice
        self.token_content.extend_from_slice(&slice[..index]);

        if index < slice.len() {
            // we have successfully consumed the symbol, finish it
            // compute the end location, no line feeds are allowed in simple symbols
            self.finish_simple_symbol(TokenEnd::at_byte(index))?;
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
                    self.sink(TokenType::Symbol, TokenEnd::at_byte(after_slice_position))?;
                    // return to normal, consuming bytes including the pipe
                    self.state = LexerState::Normal;
                    return Ok(after_slice_position);
                }
                Some(b'\\') => {
                    // backslash is forbidden in quoted symbols
                    return Err(self.error_at(
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
                    return Err(self.error_at(
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
        // test that the keyword does not start with a digit
        if self.token_content.is_empty() && slice[0].is_ascii_digit() {
            return Err(self.error_at(LexerErrorKind::ForbiddenKeywordName, 1));
        }

        // find the first byte that is not simple-symbol-like
        let index = Self::run_end(slice, SIMPLE_SYMBOL);

        // extend the token from slice
        self.token_content.extend_from_slice(&slice[..index]);

        if index < slice.len() {
            // we have successfully consumed the keyword, finish it
            // compute the end locations, no line feeds are allowed in keywords
            self.finish_keyword(TokenEnd::at_byte(index))?;
            self.state = LexerState::Normal;
        }

        Ok(index)
    }

    fn lex_comment(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        // run until comment end
        let index = Self::run_end(slice, COMMENT_PLAIN);
        let Some(c) = slice.get(index) else {
            // the comment continues, just consume the whole slice
            // and remain in comment state
            return Ok(slice.len());
        };

        // the comment has ended, either by CR or LF
        // if it ended by LF, we must mark it
        if *c == b'\n' {
            self.mark_line_feed_at(index);
        }

        // move back to the normal state
        self.state = LexerState::Normal;

        // return, consuming up to comment end including it
        Ok(index + 1)
    }

    fn finish_decimal(&mut self, end: TokenEnd) -> Result<(), LexError<H::Error>> {
        // decimals of the form 7. without any digit in fractional part are disallowed
        let last_is_none_or_dot = self
            .token_content
            .as_slice()
            .last()
            .is_none_or(|c| *c == b'.');
        if last_is_none_or_dot {
            return Err(self.error(LexerErrorKind::FractionDigitExpected, end));
        }
        // sink new token
        self.sink(TokenType::Decimal, end)
    }

    fn finish_numeral(&mut self, end: TokenEnd) -> Result<(), LexError<H::Error>> {
        // this was a numeral, we have no further checks
        // sink new token
        self.sink(TokenType::Numeral, end)
    }

    fn finish_digit_run(&mut self, run: DigitRun, end: TokenEnd) -> Result<(), LexError<H::Error>> {
        // digit runs must not be empty
        if self.token_content.is_empty() {
            return Err(self.error(run.empty_error, end));
        }
        // sink new token
        self.sink(run.token_type, end)
    }

    fn finish_simple_symbol(&mut self, end: TokenEnd) -> Result<(), LexError<H::Error>> {
        // process reserved words
        let token_type = if let Some(reserved) = Reserved::from_symbol_opt(&self.token_content) {
            TokenType::Reserved(reserved)
        } else {
            TokenType::Symbol
        };
        // sink new token
        self.sink(token_type, end)
    }

    fn finish_keyword(&mut self, end: TokenEnd) -> Result<(), LexError<H::Error>> {
        // ensure the keyword is not empty
        if self.token_content.is_empty() {
            return Err(self.error(LexerErrorKind::ForbiddenKeywordName, end));
        }
        // reserved words as keywords are prohibited
        if Reserved::from_symbol_opt(&self.token_content).is_some() {
            return Err(self.error(LexerErrorKind::KeywordReserved, end));
        }
        // sink new token
        self.sink(TokenType::Keyword, end)
    }

    fn finish_string_literal(&mut self, end: TokenEnd) -> Result<(), LexError<H::Error>> {
        // literal has ended at the previous character
        // sink new token
        self.sink(TokenType::String, end)
    }

    /// Sinks the current token, ending at `position`.
    fn sink(&mut self, token_type: TokenType, end: TokenEnd) -> Result<(), LexError<H::Error>> {
        // construct the span
        let end = self.location_at(end.position);
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

    fn start_token(&mut self, position: usize) {
        // update the token start to the computed location
        self.token_start = self.location_at(position);
        // clear the token string
        self.token_content.clear();
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

    /// Location of `position` in the current slice.
    ///
    /// Every line feed before `position` must be marked before calling this.
    fn location_at(&self, position: usize) -> SmtLocation {
        let offset = self.offset + position as u64;
        SmtLocation::new(offset, self.line, offset - self.line_start)
    }

    /// Error spanning the token so far and, if it ended at a byte, that byte.
    fn error<E>(&self, kind: LexerErrorKind, end: TokenEnd) -> LexError<E> {
        self.error_at(kind, end.position + end.at_byte as usize)
    }

    /// Error spanning the token up to `position`.
    ///
    /// Used for errors detected mid-run, e.g. forbidden byte in a string
    /// or a backslash in a quoted symbol.
    fn error_at<E>(&self, kind: LexerErrorKind, position: usize) -> LexError<E> {
        let end = self.location_at(position);
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

mod char_class;
mod error;
mod helpers;

pub use error::{LexError, LexerError, LexerErrorKind};

pub(crate) use char_class::CharClass;

use crate::{
    SmtLocation, SmtSpan, String8,
    read::lexer::{
        char_class::{COMMENT_PLAIN, DIGIT, QUOTED_PLAIN, SIMPLE_SYMBOL, STRING_PLAIN, run_end},
        helpers::{BINARY_RUN, Content, DigitRun, HEXADECIMAL_RUN, START, Start, TokenEnd},
    },
    token::{InnerType, Token, TokenHandler, TokenStop},
};

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
        // call inner lexing and fail on error
        self.fail_on_error(|lexer| lexer.lex_slice_inner(slice))
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
        // call inner EOF lexing and fail on error
        self.fail_on_error(|lexer| lexer.lex_eof_inner())
    }

    fn lex_eof_inner(&mut self) -> Result<(), LexError<H::Error>> {
        match self.state {
            LexerState::Normal | LexerState::Comment => {
                // nothing to do, we accept EOF even in comments
                Ok(())
            }
            LexerState::Fraction => self.finish_decimal(TokenEnd::EOF, Content::Stored),
            LexerState::NumeralOrDecimal => self.finish_numeral(TokenEnd::EOF, Content::Stored),
            LexerState::Hexadecimal => {
                self.finish_digit_run(HEXADECIMAL_RUN, TokenEnd::EOF, Content::Stored)
            }
            LexerState::Binary => self.finish_digit_run(BINARY_RUN, TokenEnd::EOF, Content::Stored),
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
                self.finish_string_literal(TokenEnd::EOF, Content::Stored)
            }
            LexerState::SimpleSymbol => self.finish_simple_symbol(TokenEnd::EOF, Content::Stored),
            LexerState::Keyword => self.finish_keyword(TokenEnd::EOF, Content::Stored),
            LexerState::QuotedSymbol => {
                // EOF forbidden as the symbol must be totally enclosed by pipes
                Err(self.error(LexerErrorKind::UnclosedQuotedSymbol, TokenEnd::EOF))
            }
            LexerState::Failed => {
                panic!("cannot lex after a lexer error")
            }
        }?;

        // everything processed, start the EOF token and sink it
        self.start_token(0);
        self.sink_eof()?;
        // reset the lexer to normal
        self.state = LexerState::Normal;
        Ok(())
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

        while let Some(&c) = slice.get(index) {
            // PERFORMANCE: One table lookup decides the arm. Arms eagerly
            // try to complete the token with the whole content borrowed from the slice,
            // which resets the lexer back to the normal state, so the loop can continue.
            //
            // Lexing only returns early if eager dispatch is not possible,
            // typically due to running out of bytes in the slice.
            //
            // This loop is VERY HOT and even small changes can drastically affect
            // performance. This especially applies to unintentional panic paths
            // introduced by maybe-panicking bounds checks.
            let after = index + 1;
            match START[c as usize] {
                Start::Whitespace => {
                    index = after;
                }
                Start::LineFeed => {
                    // line feeds must be marked for line offsets
                    // mark it and update the index
                    self.mark_line_feed_at(index);
                    index = after;
                }
                Start::ParenOpen => {
                    // parentheses are tokens by themselves
                    // dispatch the token, it has no content
                    self.start_token(index);
                    self.sink_slice(
                        InnerType::ParenOpen,
                        TokenEnd::at_byte(after),
                        Content::Borrowed(&[]),
                    )?;
                    // update the index and continue the loop
                    index = after;
                }
                Start::ParenClose => {
                    // parentheses are tokens by themselves
                    // dispatch the token, it has no content
                    self.start_token(index);
                    self.sink_slice(
                        InnerType::ParenClose,
                        TokenEnd::at_byte(after),
                        Content::Borrowed(&[]),
                    )?;
                    // update the index and continue the loop
                    index = after;
                }
                Start::Comment => {
                    // a comment has been started
                    // process the run eagerly
                    self.start_token(index);
                    let end = after + run_end(&slice[after..], COMMENT_PLAIN);
                    match slice.get(end) {
                        Some(b'\n') => {
                            // line feed, we need to mark it
                            self.mark_line_feed_at(end);
                            // ends the comment
                        }
                        Some(_) => {
                            // non-line-feed comment end
                            // must be a carriage return (CR)
                            // also ends the comment
                        }
                        None => {
                            // we ran out of bytes
                            // update the state and return
                            self.state = LexerState::Comment;
                            return Ok(end);
                        }
                    }
                    // we have reached the end of the comment
                    // update the index and continue the loop
                    index = end + 1;
                }
                Start::Hash => {
                    // base selection
                    self.start_token(index);
                    let run = match slice.get(after) {
                        Some(b'x') => HEXADECIMAL_RUN,
                        Some(b'b') => BINARY_RUN,
                        _ => {
                            // we either encountered a wrong base selection
                            // or ran out of bytes
                            // update the state and return
                            // if the base selection is wrong,
                            // the error will be produced in its function
                            self.state = LexerState::BaseSelection;
                            return Ok(after);
                        }
                    };
                    // the base has been selected, get a run of its digits
                    let start = after + 1;
                    let after_end = start + run_end(&slice[start..], run.flag);
                    if after_end == slice.len() {
                        // we ran out of bytes
                        // update the content and the state and return
                        self.token_content
                            .extend_from_slice(&slice[start..after_end]);
                        self.state = run.state;
                        return Ok(after_end);
                    }
                    // dispatch a token with borrowed content
                    self.finish_digit_run(
                        run,
                        TokenEnd::at_byte(after_end),
                        Content::Borrowed(&slice[start..after_end]),
                    )?;
                    // update the index and continue the loop
                    index = after_end;
                }
                Start::Quote => {
                    // starts a string literal
                    self.start_token(index);
                    // determine the run of content bytes
                    let after_content_end = after + run_end(&slice[after..], STRING_PLAIN);
                    // we can only eagerly borrow if the content is ended by a closing quote
                    // that is definitely not followed by another closing quote
                    // (we cannot borrow a string containing an escape)

                    // PERFORMANCE: a fixed two-byte window through `get`; both `&slice[x..]`
                    // (a panic path) and an open range (unknown tail length) can
                    // deeply change the codegen of the whole function.
                    match slice.get(after_content_end..after_content_end + 2) {
                        Some([b'"', next]) if *next != b'"' => {
                            // definitely closed by a quote not followed by another quote
                            // borrow the string literal content and produce a token
                            self.finish_string_literal(
                                TokenEnd::at_byte(after_content_end + 1),
                                Content::Borrowed(&slice[after..after_content_end]),
                            )?;
                            // the closing quote is not part of the content,
                            // but was also processed
                            index = after_content_end + 1;
                        }
                        _ => {
                            // we cannot borrow the content
                            // update the content and state and return
                            self.token_content
                                .extend_from_slice(&slice[after..after_content_end]);
                            self.state = LexerState::StringLiteral;
                            return Ok(after_content_end);
                        }
                    }
                }
                Start::Colon => {
                    // starts a keyword
                    self.start_token(index);
                    // we require that the keyword does not start with a digit
                    // (also non-empty, but that is checked after finishing)
                    if slice.get(after).is_some_and(u8::is_ascii_digit) {
                        return Err(self.error_at(LexerErrorKind::ForbiddenKeywordName, after + 1));
                    }
                    // get a run of simple-symbol bytes
                    let after_end = after + run_end(&slice[after..], SIMPLE_SYMBOL);
                    if after_end == slice.len() {
                        // we ran out of bytes
                        // update the content and state and return
                        self.token_content
                            .extend_from_slice(&slice[after..after_end]);
                        self.state = LexerState::Keyword;
                        return Ok(after_end);
                    }
                    // dispatch a token with borrowed content
                    self.finish_keyword(
                        TokenEnd::at_byte(after_end),
                        Content::Borrowed(&slice[after..after_end]),
                    )?;
                    // update the index and continue the loop
                    index = after_end;
                }
                Start::Pipe => {
                    self.start_token(index);
                    // determine the run of content bytes
                    let after_content_end = after + run_end(&slice[after..], QUOTED_PLAIN);
                    if slice.get(after_content_end) == Some(&b'|') {
                        // closed by another pipe
                        // dispatch the token with borrowed content
                        self.sink_slice(
                            InnerType::QuotedSymbol,
                            TokenEnd::at_byte(after_content_end + 1),
                            Content::Borrowed(&slice[after..after_content_end]),
                        )?;
                        // update the index and continue the loop
                        // the closing pipe is not a part of the content but was processed
                        index = after_content_end + 1;
                    } else {
                        // we encountered a line feed, an error, or ran out of bytes
                        // update the content and state and return
                        self.token_content
                            .extend_from_slice(&slice[after..after_content_end]);
                        self.state = LexerState::QuotedSymbol;
                        return Ok(after_content_end);
                    }
                }
                Start::Digit => {
                    self.start_token(index);
                    // determine the run of digits
                    let after_end = after + run_end(&slice[after..], DIGIT);
                    // check that we are not in a leading zero condition,
                    // which is only possible if the first character was zero
                    // and there is a subsequent digit;
                    // it is possible we will not be able to decide it here
                    // if the slice ends with a single zero, so we need to handle that
                    // when parsing digit in the state `NumeralOrDecimal`
                    if c == b'0' && after_end > after {
                        return Err(self.error_at(LexerErrorKind::NumeralLeadingZero, after + 1));
                    }
                    match slice.get(after_end) {
                        Some(b'.') => {
                            // a dot starts a fraction, try to do a subsequent run of fraction digits
                            let after_fraction_end =
                                after_end + 1 + run_end(&slice[after_end + 1..], DIGIT);
                            if after_fraction_end == slice.len() {
                                // we ran out of bytes
                                // update the content and state and return
                                self.token_content
                                    .extend_from_slice(&slice[index..after_fraction_end]);
                                self.state = LexerState::Fraction;
                                return Ok(after_fraction_end);
                            }
                            // dispatch a decimal token with borrowed content
                            self.finish_decimal(
                                TokenEnd::at_byte(after_fraction_end),
                                Content::Borrowed(&slice[index..after_fraction_end]),
                            )?;
                            // update the index and continue the loop
                            index = after_fraction_end;
                        }
                        Some(_) => {
                            // the numeral is not actually a decimal and ends
                            // dispatch a numeral token with borrowed content
                            self.finish_numeral(
                                TokenEnd::at_byte(after_end),
                                Content::Borrowed(&slice[index..after_end]),
                            )?;
                            // update the index and continue the loop
                            index = after_end;
                        }
                        None => {
                            // we ran out of bytes
                            // update the content and state and return
                            self.token_content
                                .extend_from_slice(&slice[index..after_end]);
                            self.state = LexerState::NumeralOrDecimal;
                            return Ok(after_end);
                        }
                    }
                }
                Start::Symbol => {
                    self.start_token(index);
                    // get a run of simple-symbol bytes
                    let after_end = after + run_end(&slice[after..], SIMPLE_SYMBOL);
                    if after_end == slice.len() {
                        // we ran out of bytes
                        // update the content and state and return
                        self.token_content
                            .extend_from_slice(&slice[index..after_end]);
                        self.state = LexerState::SimpleSymbol;
                        return Ok(after_end);
                    }
                    // dispatch a token with borrowed content
                    self.finish_simple_symbol(
                        TokenEnd::at_byte(after_end),
                        Content::Borrowed(&slice[index..after_end]),
                    )?;
                    // update the index and continue the loop
                    index = after_end;
                }
                Start::Other => {
                    self.start_token(index);
                    // unexpected character
                    return Err(self.error_at(LexerErrorKind::UnexpectedCharacter, after));
                }
            }
        }
        // we have consumed every byte
        Ok(slice.len())
    }

    fn lex_numeral_or_decimal(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        // find the first byte that is not a digit
        let index = run_end(slice, DIGIT);

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
                self.finish_numeral(TokenEnd::at_byte(index), Content::Stored)?;
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
        let end = start + run_end(&slice[start..], DIGIT);
        // extend the token from slice
        self.token_content.extend_from_slice(&slice[start..end]);
        if end < slice.len() {
            // we have successfully consumed the fraction, finish the decimal
            // compute the end location, no line feeds are allowed in simple symbols
            self.finish_decimal(TokenEnd::at_byte(end), Content::Stored)?;
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
        let index = run_end(slice, run.flag);
        // extend the token from slice
        self.token_content.extend_from_slice(&slice[..index]);
        if index < slice.len() {
            // we have successfully consumed the digit run, finish it
            // compute the end location, no line feeds are allowed in simple symbols
            self.finish_digit_run(run, TokenEnd::at_byte(index), Content::Stored)?;
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
                    self.finish_string_literal(TokenEnd::at_byte(consumed), Content::Stored)?;
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
            let index = run_end(rest, STRING_PLAIN);

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
        let index = run_end(slice, SIMPLE_SYMBOL);

        // extend the token from slice
        self.token_content.extend_from_slice(&slice[..index]);

        if index < slice.len() {
            // we have successfully consumed the symbol, finish it
            // compute the end location, no line feeds are allowed in simple symbols
            self.finish_simple_symbol(TokenEnd::at_byte(index), Content::Stored)?;
            self.state = LexerState::Normal;
        }

        Ok(index)
    }

    fn lex_quoted_symbol(&mut self, mut rest: &[u8]) -> Result<usize, LexError<H::Error>> {
        let mut consumed = 0;
        loop {
            // find the first byte that is not a quoted symbol
            let index = run_end(rest, QUOTED_PLAIN);
            let after_slice_position = consumed + index + 1;

            // inspect the problematic byte
            match rest.get(index) {
                Some(b'|') => {
                    // end of quoted symbol, extend and sink its token
                    // the closing pipe is not consumed but delimits the token
                    self.token_content.extend_from_slice(&rest[..index]);
                    self.sink_slice(
                        InnerType::QuotedSymbol,
                        TokenEnd::at_byte(after_slice_position),
                        Content::Stored,
                    )?;
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
        let index = run_end(slice, SIMPLE_SYMBOL);

        // extend the token from slice
        self.token_content.extend_from_slice(&slice[..index]);

        if index < slice.len() {
            // we have successfully consumed the keyword, finish it
            // compute the end locations, no line feeds are allowed in keywords
            self.finish_keyword(TokenEnd::at_byte(index), Content::Stored)?;
            self.state = LexerState::Normal;
        }

        Ok(index)
    }

    fn lex_comment(&mut self, slice: &[u8]) -> Result<usize, LexError<H::Error>> {
        // run until comment end
        let index = run_end(slice, COMMENT_PLAIN);
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

    /// Sinks the current token, ending at `position`.
    fn finish_decimal(
        &mut self,
        end: TokenEnd,
        content: Content,
    ) -> Result<(), LexError<H::Error>> {
        // decimals of the form 7. without any digit in fractional part are disallowed
        let value = content.bytes(&self.token_content);
        if value.last().is_none_or(|c| *c == b'.') {
            return Err(self.error(LexerErrorKind::FractionDigitExpected, end));
        }
        self.sink_slice(InnerType::Decimal, end, content)
    }

    fn finish_numeral(
        &mut self,
        end: TokenEnd,
        content: Content,
    ) -> Result<(), LexError<H::Error>> {
        self.sink_slice(InnerType::Numeral, end, content)
    }

    fn finish_digit_run(
        &mut self,
        run: DigitRun,
        end: TokenEnd,
        content: Content,
    ) -> Result<(), LexError<H::Error>> {
        // digit runs must not be empty
        let value = content.bytes(&self.token_content);
        if value.is_empty() {
            return Err(self.error(run.empty_error, end));
        }
        self.sink_slice(run.token_type, end, content)
    }

    fn finish_simple_symbol(
        &mut self,
        end: TokenEnd,
        content: Content,
    ) -> Result<(), LexError<H::Error>> {
        self.sink_slice(InnerType::UnquotedSymbol, end, content)
    }

    fn finish_keyword(
        &mut self,
        end: TokenEnd,
        content: Content,
    ) -> Result<(), LexError<H::Error>> {
        let value = content.bytes(&self.token_content);
        // ensure the keyword is not empty
        if value.is_empty() {
            return Err(self.error(LexerErrorKind::ForbiddenKeywordName, end));
        }
        self.sink_slice(InnerType::Keyword, end, content)
    }

    fn finish_string_literal(
        &mut self,
        end: TokenEnd,
        content: Content,
    ) -> Result<(), LexError<H::Error>> {
        self.sink_slice(InnerType::String, end, content)
    }

    /// Sinks a token with the given content, ending at `end`.
    #[inline]
    fn sink_slice(
        &mut self,
        ty: InnerType,
        end: TokenEnd,
        content: Content,
    ) -> Result<(), LexError<H::Error>> {
        // construct the span
        let end = self.location_at(end.position);
        let span = SmtSpan::new_unchecked(self.token_start, end);
        // pass the content by reference
        let content = content.bytes(&self.token_content);

        // the caller of this function is responsible
        // for ensuring that the constructed token is valid

        let result = self
            .handler
            .handle_token(Token::new(&Some((ty, content)), &span));

        self.sink_finish(result)
    }

    #[inline]
    fn sink_eof(&mut self) -> Result<(), LexError<H::Error>> {
        // construct the span
        let end = self.location_at(0);
        let span = SmtSpan::new_unchecked(self.token_start, end);

        // sink EOF
        let result = self.handler.handle_token(Token::new(&None, &span));
        self.sink_finish(result)
    }

    fn sink_finish(
        &mut self,
        result: Result<(), TokenStop<H::Error>>,
    ) -> Result<(), LexError<H::Error>> {
        let Err(stop) = result else {
            return Ok(());
        };

        match stop {
            TokenStop::Relex => {
                todo!("Relex");
            }
            TokenStop::Error(err) => Err(LexError::Handler(err)),
        }
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

    /// Sets state to failed when an error propagates from the inner function.
    ///
    /// Called from the outer public functions.
    fn fail_on_error(
        &mut self,
        step: impl FnOnce(&mut Self) -> Result<(), LexError<H::Error>>,
    ) -> Result<(), LexError<H::Error>> {
        let result = step(self);
        if result.is_err() {
            self.state = LexerState::Failed;
        }
        result
    }
}

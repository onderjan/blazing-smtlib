mod char_class;
mod error;
mod helpers;

pub use error::{LexError, LexerError, LexerErrorKind};

pub(crate) use char_class::CharClass;

use std::ops::ControlFlow;

use crate::{
    SmtLocated, SmtLocation, SmtSpan, String8,
    read::lexer::{
        char_class::{
            RUN_COMMENT_PLAIN, RUN_DIGIT, RUN_QUOTED_PLAIN, RUN_SIMPLE_SYMBOL, RUN_STRING_PLAIN,
            run_end, run_end_all,
        },
        helpers::{
            BINARY_RUN, Content, DigitRun, FAST, FAST_DELIM, FAST_EMIT, FAST_ON, FAST_PIPE,
            FAST_RUN_MASK, HEXADECIMAL_RUN, START, Start, TokenEnd,
        },
    },
    token::{InnerType, SmtVersion, TokenCursor, TokenHandler},
};

pub struct Lexer<H: TokenHandler> {
    /// Handler of produced tokens.
    handler: H,

    /// The SMT-LIB version the lexer currently operates under.
    version: SmtVersion,

    /// The initial SMT-LIB version the lexer will reset to.
    initial_version: SmtVersion,

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

    /// Spans of respective batch tokens.
    spans: Box<[SmtSpan; BATCH_CAPACITY]>,
}

/// Maximal number of tokens that can be batched.
const BATCH_CAPACITY: usize = 256;

/// Token batch, may be only partially filled.
struct Batch<'a> {
    entries: [Option<(InnerType, &'a [u8])>; BATCH_CAPACITY],
    len: usize,
}

/// Why lexing stopped before the end of the slice.
enum Stop<R> {
    /// The handler requested lexing again from the stop location.
    Relex,
    /// The handler finished with a result at the stop location.
    Finished(R),
}

struct Interrupted<R, E> {
    result: Result<Stop<R>, E>,
    location: SmtLocation,
}

#[derive(Clone, Copy)]
enum LexerState {
    /// Awaiting the start of a token.
    Normal,
    /// Lexing a numeral or the whole part of a decimal.
    ///
    /// Whether the token is a numeral or a decimal will
    /// only become apparent after encountering a dot
    /// or token end.
    NumeralOrDecimal,
    /// Lexing a fraction.
    Fraction,
    /// Hash encountered, 'h' will select hexadecimal, 'b' binary.
    BaseSelection,
    /// Lexing a hexadecimal number.
    Hexadecimal,
    /// Lexing a binary number.
    Binary,
    /// Lexing a string literal.
    StringLiteral,
    /// Lexing a string literal, a double quote was encountered.
    ///
    /// In standard 2.5+ mode, it should be followed by another
    /// double quote acting as an escape, or a token delimiter,
    /// confirming the string literal closed.
    ///
    /// In legacy 2.0 mode, it should be followed by a token delimiter,
    /// as double quote does not escape itself.
    StringLiteralDoubleQuote,
    /// Lexing a string literal, a backslash escape was encountered (SMT-LIB 2.0 only).
    ///
    /// In the standard 2.5+ mode, backslash does not escape,
    /// so this state is never taken.
    ///
    /// In the legacy 2.0 mode, there are two escape sequences, \" and \\.
    /// Otherwise, the backslash and the byte after it are taken as-is.
    StringLiteralBackslashEscape,
    /// Lexing a simple symbol.
    ///
    /// Reserved words are not handled by the lexer, so this may
    /// be a reserved word as well.
    SimpleSymbol,
    /// Lexing a quoted symbol.
    QuotedSymbol,
    /// Lexing a keyword.
    Keyword,
    /// Lexing a comment.
    Comment,
    /// Quoted symbol closing pipe was encountered, waiting for token delimiter.
    ///
    /// The token cannot be emitted before confirming that the next byte is
    /// a token delimiter; otherwise, an error will occur.
    QuotedSymbolClosed,
    /// A lexer or handler error was returned; lexing cannot continue.
    Failed,
}

impl<H: TokenHandler> Lexer<H> {
    /// Constructs the lexer.
    pub fn new(handler: H, version: SmtVersion) -> Self {
        Lexer {
            handler,
            version,
            initial_version: version,
            state: LexerState::Normal,
            token_start: SmtLocation::initial(),
            token_content: String8::new(),
            offset: 0,
            line: 0,
            line_start: 0,
            spans: Box::new([SmtSpan::new_zero(); BATCH_CAPACITY]),
        }
    }

    pub fn current_location(&self) -> SmtLocation {
        self.location_at(0)
    }

    /// Lexes the whole input including EOF at the end.
    ///
    /// If the token handler returns [`ControlFlow::Break`] on some token,
    /// the lexer passes it through, adding the break location,
    /// and resets itself.
    ///
    /// If the token handler returns [`ControlFlow::Continue`] on all tokens
    /// including EOF, the lexer resets itself after EOF
    /// and returns [`ControlFlow::Continue`].
    ///
    /// If an error occurs, the lexer moves into a failure state;
    /// all further lexing calls panic.
    pub fn lex_all(
        &mut self,
        input: &[u8],
    ) -> Result<ControlFlow<SmtLocated<H::Result>>, LexError<H::Error>> {
        match self.lex_slice(input)? {
            ControlFlow::Break(result) => Ok(ControlFlow::Break(result)),
            ControlFlow::Continue(()) => self.lex_eof(),
        }
    }

    /// Lexes the given slice, sending the lexed tokens to the handler.
    ///
    /// If the token handler returns [`ControlFlow::Break`] on some token,
    /// the lexer passes it through, adding the break location,
    /// and resets itself.
    ///
    /// If the token handler returns [`ControlFlow::Continue`] on all tokens,
    /// the lexer is ready for further lexing.
    ///
    /// If an error occurs, the lexer moves into a failure state;
    /// all further lexing calls panic.
    pub fn lex_slice(
        &mut self,
        slice: &[u8],
    ) -> Result<ControlFlow<SmtLocated<H::Result>>, LexError<H::Error>> {
        // call inner lexing and fail on error
        self.execute_step(|lexer| lexer.lex_slice_inner(slice))
    }

    /// Lexes end-of-file, sending the lexed tokens to the handler.
    ///
    /// If the token handler returns [`ControlFlow::Break`] on the EOF token,
    /// the lexer passes it through, adding the break location,
    /// and resets itself.
    ///
    /// If the token handler returns [`ControlFlow::Continue`] on the EOF token,
    /// the lexer resets itself and returns [`ControlFlow::Continue`].
    ///
    /// If an error occurs, the lexer moves into a failure state;
    /// all further lexing calls panic.
    pub fn lex_eof(&mut self) -> Result<ControlFlow<SmtLocated<H::Result>>, LexError<H::Error>> {
        // call inner EOF lexing and fail on error
        self.execute_step(|lexer| lexer.lex_eof_inner())
    }

    fn lex_eof_inner(&mut self) -> Result<ControlFlow<H::Result>, LexError<H::Error>> {
        // TODO: do not construct batch here
        let mut batch: Batch = Batch {
            entries: [None; BATCH_CAPACITY],
            len: 0,
        };

        // EOF is a token delimiter, we need to produce the token
        // that waits for a delimiter if there is any
        let result = match self.state {
            LexerState::Normal | LexerState::Comment => {
                // nothing to do, we accept EOF even in comments
                Ok(())
            }
            LexerState::QuotedSymbolClosed => {
                // the end of the input is a token delimiter,
                // produce the quoted symbol
                self.sink_slice(
                    &mut batch,
                    InnerType::QuotedSymbol,
                    TokenEnd::EOF,
                    Content::Stored,
                )
            }
            LexerState::Fraction => {
                self.finish_decimal(&mut batch, TokenEnd::EOF, Content::Stored, None)
            }
            LexerState::NumeralOrDecimal => {
                self.finish_numeral(&mut batch, TokenEnd::EOF, Content::Stored)
            }
            LexerState::Hexadecimal => self.finish_digit_run(
                &mut batch,
                HEXADECIMAL_RUN,
                TokenEnd::EOF,
                Content::Stored,
                None,
            ),
            LexerState::Binary => {
                self.finish_digit_run(&mut batch, BINARY_RUN, TokenEnd::EOF, Content::Stored, None)
            }
            LexerState::BaseSelection => {
                // hash without selection following it
                Err(self.error(LexerErrorKind::BaseSelectionExpected, TokenEnd::EOF))
            }
            LexerState::StringLiteral | LexerState::StringLiteralBackslashEscape => {
                // we are still within the string literal
                // forbidden as the literal must be totally enclosed by double quotes
                Err(self.error(LexerErrorKind::UnclosedStringLiteral, TokenEnd::EOF))
            }
            LexerState::StringLiteralDoubleQuote => {
                // string literal has ended by the previous character,
                // a quote directly before the end of the file
                // this works both for 2.0 and 2.5+
                self.finish_string_literal(&mut batch, TokenEnd::EOF, Content::Stored)
            }
            LexerState::SimpleSymbol => {
                self.finish_simple_symbol(&mut batch, TokenEnd::EOF, Content::Stored)
            }
            LexerState::Keyword => {
                self.finish_keyword(&mut batch, TokenEnd::EOF, Content::Stored, None)
            }
            LexerState::QuotedSymbol => {
                // EOF forbidden as the symbol must be totally enclosed by pipes
                Err(self.error(LexerErrorKind::UnclosedQuotedSymbol, TokenEnd::EOF))
            }
            LexerState::Failed => {
                panic!("cannot lex after a lexer error")
            }
        }
        .and_then(|()| {
            // everything has been processed, start the EOF token and sink it
            self.start_token(0);
            self.sink_eof()
        });

        match result {
            Ok(()) => {
                // everything processed, but there was no break out
                // we need manually reset the lexer and return Continue
                self.reset();
                Ok(ControlFlow::Continue(()))
            }
            Err(interrupted) => match interrupted.result? {
                Stop::Relex => {
                    panic!("token handler cannot request relex at end of file")
                }
                Stop::Finished(result) => {
                    // the handler is done with the input
                    // the lexer will be reset as a consequence of the Break result
                    Ok(ControlFlow::Break(result))
                }
            },
        }
    }

    fn lex_slice_inner(
        &mut self,
        slice: &[u8],
    ) -> Result<ControlFlow<H::Result>, LexError<H::Error>> {
        let mut batch: Batch = Batch {
            entries: [None; BATCH_CAPACITY],
            len: 0,
        };

        let initial_offset = self.offset;
        let mut rest = slice;
        let mut fn_result = Ok(ControlFlow::Continue(()));

        loop {
            let result = if rest.is_empty() || fn_result.is_err() {
                // hand over the batch
                match self.flush_batch(&mut batch) {
                    Ok(()) => {
                        // we are done
                        return fn_result;
                    }
                    Err(err) => Err(err),
                }
            } else {
                match self.state {
                    LexerState::Normal => self.lex_normal(&mut batch, rest),
                    LexerState::NumeralOrDecimal => self.lex_numeral_or_decimal(&mut batch, rest),
                    LexerState::Fraction => self.lex_fraction_from(&mut batch, rest, 0),
                    LexerState::BaseSelection => self.lex_base_selection(rest),
                    LexerState::Hexadecimal => {
                        self.lex_digit_run(&mut batch, rest, HEXADECIMAL_RUN)
                    }
                    LexerState::Binary => self.lex_digit_run(&mut batch, rest, BINARY_RUN),
                    LexerState::StringLiteral
                    | LexerState::StringLiteralDoubleQuote
                    | LexerState::StringLiteralBackslashEscape => {
                        self.lex_string_literal(&mut batch, rest)
                    }
                    LexerState::SimpleSymbol => self.lex_simple_symbol(&mut batch, rest),
                    LexerState::QuotedSymbol => self.lex_quoted_symbol(&mut batch, rest),
                    LexerState::Keyword => self.lex_keyword(&mut batch, rest),
                    LexerState::Comment => self.lex_comment(rest),
                    LexerState::QuotedSymbolClosed => {
                        self.lex_quoted_symbol_closed(&mut batch, rest)
                    }
                    LexerState::Failed => panic!("cannot lex after a lexer error"),
                }
            };

            match result {
                Ok(consumed) => {
                    // advance the offset by the number of consumed bytes
                    // the line positions are updated by the arm functions above
                    self.offset += consumed as u64;
                    // move after consumed bytes
                    rest = &rest[consumed..];

                    // continue consuming
                    continue;
                }
                Err(interrupted) => {
                    match interrupted.result {
                        Ok(stop) => {
                            let location = interrupted.location;
                            self.resume_at(location);
                            // every handed-over token borrows this slice
                            // so the location must be equal or greater to initial offset
                            // compute this even for Finished to assert the interrupted location
                            let index = location.offset().checked_sub(initial_offset).expect(
                                "the token handler must not stop before the starting token",
                            );
                            match stop {
                                Stop::Relex => {
                                    // everything up to the index was already consumed
                                    // continue from there
                                    rest = &slice[index as usize..];
                                    fn_result = Ok(ControlFlow::Continue(()));
                                }
                                Stop::Finished(result) => {
                                    // the handler is done: the batch was handed over,
                                    // the rest of the slice stays unlexed
                                    // the lexer will be reset as a consequence of the Break result
                                    return Ok(ControlFlow::Break(result));
                                }
                            }
                        }
                        Err(err) => {
                            // make sure the tokens before the error get handed over
                            fn_result = Err(err);
                        }
                    }
                }
            }
        }
    }

    fn lex_normal<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        slice: &'a [u8],
    ) -> Result<usize, Interrupted<H::Result, LexError<H::Error>>> {
        let mut index = 0;

        // PERFORMANCE: use locals for variables commonly used on the fast path.
        let offset = self.offset;
        let mut local = FastState::load(self, batch);

        while let Some(&c) = slice.get(index) {
            // PERFORMANCE: A fast path handles the most common token types.
            // It is determined by one table lookup. If the started token is not on
            // the fast path, a slower path is taken, again looked up. Arms eagerly
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
            // Handle the parentheses first as they are numerous and
            // need no special processing. The closing parenthesis is first
            // as it forms more clusters.
            if c == b')' {
                let entry = (InnerType::ParenClose, &slice[index..after]);
                self.push_fast(batch, &mut local, offset, entry, index..after, 1)?;
                index = after;
                continue;
            }
            if c == b'(' {
                let entry = (InnerType::ParenOpen, &slice[index..after]);
                self.push_fast(batch, &mut local, offset, entry, index..after, 1)?;
                index = after;
                continue;
            }
            // Handle whitespace and symbols in a fast path.
            let fast_entry = FAST[c as usize];
            if fast_entry & FAST_ON != 0 {
                // Fast path, compute where the run ends and where the token ends.
                // For quoted symbols, the token will end after the closing pipe.
                let run_end_at: usize =
                    after + run_end(&slice[after..], fast_entry & FAST_RUN_MASK);
                let is_quoted = fast_entry & FAST_PIPE != 0;

                // We might need to fall back to state-machine lexing if the token
                // we have found is not properly finished.
                // This can only happen if we are processing a quoted symbol
                // and the expected pipe after the end of the run is not there,
                // or if we are processing a simple symbol and we overrun the slice.
                // Parentheses have trivially zero-length runs and whitespace
                // can be split as it is discarded.

                // PERFORMANCE: gate the check for unfinished by a simpler condition.
                if run_end_at == slice.len() || is_quoted {
                    let is_unfinished = if is_quoted {
                        slice.get(run_end_at) != Some(&b'|')
                    } else {
                        fast_entry & RUN_SIMPLE_SYMBOL != 0
                    };

                    if is_unfinished {
                        // write the locals back
                        local.store(self, batch);
                        self.store_unfinished_symbol_run(
                            slice, fast_entry, index, after, run_end_at,
                        );
                        return Ok(run_end_at);
                    }
                }
                let token_end = run_end_at + is_quoted as usize;

                // No need to fall back, construct the token: the pipes delimit a quoted
                // symbol but are not part of its content, any other fast token is its
                // whole text. The token is on a single line as all fast-lex runs exclude
                // newlines. Whitespace is not emitted and overwritten by next tokens.
                let entry = if is_quoted {
                    (InnerType::QuotedSymbol, &slice[after..run_end_at])
                } else {
                    (InnerType::UnquotedSymbol, &slice[index..token_end])
                };
                let emit = (fast_entry & FAST_EMIT != 0) as usize;
                // A token must be delimited by the byte after it,
                // fall back to the state machine if the delimiter is not found.
                if emit != 0 {
                    if let Some(&next) = slice.get(token_end) {
                        // the token ended inside the slice: the byte after it must delimit it
                        if FAST[next as usize] & FAST_DELIM == 0 {
                            local.store(self, batch);
                            self.start_token(index);
                            return Err(
                                self.error_at(LexerErrorKind::MissingDelimiter, token_end + 1)
                            );
                        }
                    } else {
                        // the token ended exactly at the slice end
                        // this must be a quoted symbol as the unquoted symbol
                        // has its token end inside the confirmed run
                        // the quoted symbol must be wait for the delimiter
                        local.store(self, batch);
                        self.start_token(index);
                        self.token_content.extend_from_slice(entry.1);
                        self.state = LexerState::QuotedSymbolClosed;
                        return Ok(token_end);
                    }
                }
                self.push_fast(batch, &mut local, offset, entry, index..token_end, emit)?;
                // Fast path done, continue normally after the token end.
                index = token_end;
                continue;
            }

            // The slow path will not use the locals, write them back.
            local.store(self, batch);

            // Fast path was not taken, use the slow path.
            match START[c as usize] {
                Start::LineFeed => {
                    // line feeds must be marked for line offsets
                    // mark it and update the index
                    self.mark_line_feed_at(index);
                    index = after;
                }
                Start::Comment => {
                    // a comment has been started
                    // process the run eagerly
                    self.start_token(index);
                    let end = after + run_end(&slice[after..], RUN_COMMENT_PLAIN);
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
                        batch,
                        run,
                        TokenEnd::at_byte(after_end),
                        Content::Borrowed(&slice[start..after_end]),
                        Some(slice[after_end]),
                    )?;
                    // update the index and continue the loop
                    index = after_end;
                }
                Start::Quote => {
                    // starts a string literal
                    self.start_token(index);
                    if self.version == SmtVersion::V2_0 {
                        // SMT-LIB 2.0 has a different string-escape format
                        // than the subsequent versions, leave the fast path immediately
                        self.state = LexerState::StringLiteral;
                        return Ok(after);
                    }
                    // determine the run of content bytes
                    let after_content_end = after + run_end(&slice[after..], RUN_STRING_PLAIN);
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
                            self.expect_delimiter(*next, after_content_end + 1)?;
                            self.finish_string_literal(
                                batch,
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
                    let after_end = after + run_end(&slice[after..], RUN_SIMPLE_SYMBOL);
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
                        batch,
                        TokenEnd::at_byte(after_end),
                        Content::Borrowed(&slice[after..after_end]),
                        Some(slice[after_end]),
                    )?;
                    // update the index and continue the loop
                    index = after_end;
                }
                Start::Digit => {
                    self.start_token(index);
                    // determine the run of digits
                    let after_end = after + run_end(&slice[after..], RUN_DIGIT);
                    // check that we are not in a leading zero condition,
                    // which is only possible if the first character was zero
                    // and there is a subsequent digit;
                    // it is possible we will not be able to decide it here
                    // if the slice ends with a single zero, so we need to handle that
                    // when lexing digit in the state `NumeralOrDecimal`
                    if c == b'0' && after_end > after {
                        return Err(self.error_at(LexerErrorKind::NumeralLeadingZero, after + 1));
                    }
                    match slice.get(after_end) {
                        Some(b'.') => {
                            // a dot starts a fraction, try to do a subsequent run of fraction digits
                            let after_fraction_end =
                                after_end + 1 + run_end(&slice[after_end + 1..], RUN_DIGIT);
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
                                batch,
                                TokenEnd::at_byte(after_fraction_end),
                                Content::Borrowed(&slice[index..after_fraction_end]),
                                Some(slice[after_fraction_end]),
                            )?;
                            // update the index and continue the loop
                            index = after_fraction_end;
                        }
                        Some(&next) => {
                            // the numeral is not actually a decimal and ends
                            // dispatch a numeral token with borrowed content
                            self.expect_delimiter(next, after_end)?;
                            self.finish_numeral(
                                batch,
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
                Start::Other
                | Start::Whitespace
                | Start::ParenOpen
                | Start::ParenClose
                | Start::Symbol
                | Start::Pipe => {
                    // can actually only be Other (resulting in unexpected character),
                    // as the other arms have already been handled in the fast path.
                    self.start_token(index);
                    return Err(self.error_at(LexerErrorKind::UnexpectedCharacter, after));
                }
            }
            // Read the locals for use in a future fast path.
            local = FastState::load(self, batch);
        }
        // We have consumed every byte of the slice.
        // Write the locals back before returning.
        local.store(self, batch);
        Ok(slice.len())
    }

    fn lex_numeral_or_decimal<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        slice: &[u8],
    ) -> Result<usize, Interrupted<H::Result, LexError<H::Error>>> {
        // find the first byte that is not a digit
        let index = run_end(slice, RUN_DIGIT);

        // check that we are not in a leading zero condition
        // this could not have been done when starting the numeral/decimal
        // since just a single '0' is allowed

        // as we emplace the first digit in the normal state,
        // it suffices for the leading zero condition that
        // 1. at least one additional digit has been consumed
        // 2. the content lexed previously is exactly "0"
        if index > 0 && self.token_content.as_slice() == b"0" {
            return Err(self.error_at(LexerErrorKind::NumeralLeadingZero, 1));
        }

        // extend the token from slice
        self.token_content.extend_from_slice(&slice[..index]);

        match slice.get(index) {
            Some(b'.') => {
                // decimal, the next character will start fraction
                // add the dot and immediately start lexing the fraction after it
                self.token_content.push(b'.');
                self.lex_fraction_from(batch, slice, index + 1)
            }
            Some(&next) => {
                // we have successfully consumed the numeral, finish it
                // compute the end location, no line feeds are allowed in simple symbols
                self.expect_delimiter(next, index)?;
                self.finish_numeral(batch, TokenEnd::at_byte(index), Content::Stored)?;
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

    fn lex_fraction_from<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        slice: &[u8],
        start: usize,
    ) -> Result<usize, Interrupted<H::Result, LexError<H::Error>>> {
        // find the first byte in the remainder that is not a digit
        let end = start + run_end(&slice[start..], RUN_DIGIT);
        // extend the token from slice
        self.token_content.extend_from_slice(&slice[start..end]);
        if end < slice.len() {
            // we have successfully consumed the fraction, finish the decimal
            // compute the end location, no line feeds are allowed in simple symbols
            self.finish_decimal(
                batch,
                TokenEnd::at_byte(end),
                Content::Stored,
                Some(slice[end]),
            )?;
            self.state = LexerState::Normal;
        } else {
            // we ran out of bytes for now
            self.state = LexerState::Fraction;
        }
        Ok(end)
    }

    fn lex_base_selection(
        &mut self,
        slice: &[u8],
    ) -> Result<usize, Interrupted<H::Result, LexError<H::Error>>> {
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
    fn lex_digit_run<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        slice: &[u8],
        run: DigitRun,
    ) -> Result<usize, Interrupted<H::Result, LexError<H::Error>>> {
        // find the first byte that is not allowed in the run
        let index = run_end(slice, run.flag);
        // extend the token from slice
        self.token_content.extend_from_slice(&slice[..index]);
        if index < slice.len() {
            // we have successfully consumed the digit run, finish it
            // compute the end location, no line feeds are allowed in simple symbols
            self.finish_digit_run(
                batch,
                run,
                TokenEnd::at_byte(index),
                Content::Stored,
                Some(slice[index]),
            )?;
            self.state = LexerState::Normal;
        }
        Ok(index)
    }

    /// Lexes the string literal.
    fn lex_string_literal<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        mut rest: &[u8],
    ) -> Result<usize, Interrupted<H::Result, LexError<H::Error>>> {
        if self.version == SmtVersion::V2_0 {
            // in 2.0 mode, the string literals are lexed differently,
            // hand over to the legacy lexing function
            return self.lex_string_literal_legacy(batch, rest);
        }

        let mut consumed = 0;
        while !rest.is_empty() {
            if matches!(self.state, LexerState::StringLiteralDoubleQuote) {
                // we need to react to the literal being closed by a previous double-quote
                // look at the first byte
                if rest[0] != b'\"' {
                    // the previous character was really a quote ending the string literal
                    // finish the previously ended token
                    self.expect_delimiter(rest[0], consumed)?;
                    self.finish_string_literal(
                        batch,
                        TokenEnd::at_byte(consumed),
                        Content::Stored,
                    )?;
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
                    // return to string-literal state and continue lexing
                    self.state = LexerState::StringLiteral;
                }
            }

            // find the first byte that is not a plain string byte
            let index = run_end(rest, RUN_STRING_PLAIN);

            match rest.get(index) {
                Some(b'\n') => {
                    // mark the line feed
                    self.mark_line_feed_at(consumed + index);
                    // extend with & consume the run including the line feed
                    self.token_content.extend_from_slice(&rest[..=index]);
                    rest = &rest[index + 1..];
                    consumed += index + 1;
                    // continue lexing
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
                    // continue lexing
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

    /// Lex the string literal in the legacy 2.0 mode.
    ///
    /// The legacy 2.0 mode has two backslash escapes, \" and \\.
    /// There are no other escapes.
    fn lex_string_literal_legacy<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        mut rest: &[u8],
    ) -> Result<usize, Interrupted<H::Result, LexError<H::Error>>> {
        let mut consumed = 0;
        while !rest.is_empty() {
            match self.state {
                LexerState::StringLiteralDoubleQuote => {
                    // expect a delimiter and finish the previously ended token
                    self.expect_delimiter(rest[0], consumed)?;
                    self.finish_string_literal(
                        batch,
                        TokenEnd::at_byte(consumed),
                        Content::Stored,
                    )?;
                    // set lexer to normal state and return, not consuming the current byte
                    self.state = LexerState::Normal;
                    return Ok(consumed);
                }
                LexerState::StringLiteralBackslashEscape => {
                    // handle the backslash escape
                    let c = rest[0];
                    if c == b'\"' || c == b'\\' {
                        // a backslash escape: only the escaped byte belongs to the content
                        self.token_content.push(c);
                        rest = &rest[1..];
                        consumed += 1;
                    } else {
                        // not a backslash escape: the backslash belongs to the content,
                        // and the byte after it is lexed like any other
                        self.token_content.push(b'\\');
                    }
                    // continue parsing the string literal
                    self.state = LexerState::StringLiteral;
                }
                _ => {}
            }

            // find the first byte that does not belong to string nor quoted
            // this means backslash and pipe end the run as well, so we can act on them
            let index = run_end_all(rest, RUN_STRING_PLAIN | RUN_QUOTED_PLAIN);

            let c = match rest.get(index) {
                Some(c) => *c,
                None => {
                    // extend the content with the rest
                    self.token_content.extend_from_slice(rest);
                    // we have nothing more to consume, return
                    return Ok(consumed + rest.len());
                }
            };

            let add_run_ending = match c {
                b'\n' => {
                    // mark the line feed
                    self.mark_line_feed_at(consumed + index);
                    // it belongs to the string, add it and continue lexing
                    true
                }
                b'\"' => {
                    // put the lexer in the double-quote state
                    // do not add the quote, it is not part of the content
                    self.state = LexerState::StringLiteralDoubleQuote;
                    false
                }
                b'\\' => {
                    // put the lexer in the backslash-escape state
                    // do not add the backslash yet
                    // it may or may not be part of the content
                    // depending on if it truly is a backslash escape or not
                    self.state = LexerState::StringLiteralBackslashEscape;
                    false
                }
                b'|' => {
                    // pipe belongs to the string, add it and continue lexing
                    true
                }
                _ => {
                    // forbidden character
                    return Err(
                        self.error_at(LexerErrorKind::ForbiddenCharInString, consumed + index + 1)
                    );
                }
            };

            // extend the content with bytes before the run-ending byte
            self.token_content.extend_from_slice(&rest[..index]);
            if add_run_ending {
                // add the byte to the content
                self.token_content.push(c);
            }
            // consume the run-ending byte and everything before it
            rest = &rest[index + 1..];
            consumed += index + 1;
        }
        Ok(consumed)
    }

    fn lex_simple_symbol<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        slice: &[u8],
    ) -> Result<usize, Interrupted<H::Result, LexError<H::Error>>> {
        // find the first byte that is not a simple symbol
        let index = run_end(slice, RUN_SIMPLE_SYMBOL);

        // extend the token from slice
        self.token_content.extend_from_slice(&slice[..index]);

        if index < slice.len() {
            // we have successfully consumed the symbol, finish it
            // compute the end location, no line feeds are allowed in simple symbols
            self.expect_delimiter(slice[index], index)?;
            self.finish_simple_symbol(batch, TokenEnd::at_byte(index), Content::Stored)?;
            self.state = LexerState::Normal;
        }

        Ok(index)
    }

    fn lex_quoted_symbol<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        mut rest: &[u8],
    ) -> Result<usize, Interrupted<H::Result, LexError<H::Error>>> {
        let mut consumed = 0;
        loop {
            // find the first byte that is not a quoted symbol
            let index = run_end(rest, RUN_QUOTED_PLAIN);
            let after_slice_position = consumed + index + 1;

            // inspect the problematic byte
            match rest.get(index) {
                Some(b'|') => {
                    // end of quoted symbol, extend its content
                    self.token_content.extend_from_slice(&rest[..index]);
                    // the byte after the pipe must delimit the token before it is sunk
                    self.state = match rest.get(index + 1) {
                        Some(&next) => {
                            self.expect_delimiter(next, after_slice_position)?;
                            self.sink_slice(
                                batch,
                                InnerType::QuotedSymbol,
                                TokenEnd::at_byte(after_slice_position),
                                Content::Stored,
                            )?;
                            LexerState::Normal
                        }
                        None => {
                            // we do not have the next byte available,
                            // move to the state expecting it to be a delimiter
                            LexerState::QuotedSymbolClosed
                        }
                    };
                    // consume the bytes including the pipe
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

    fn lex_keyword<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        slice: &[u8],
    ) -> Result<usize, Interrupted<H::Result, LexError<H::Error>>> {
        // test that the keyword does not start with a digit
        if self.token_content.is_empty() && slice[0].is_ascii_digit() {
            return Err(self.error_at(LexerErrorKind::ForbiddenKeywordName, 1));
        }

        // find the first byte that is not simple-symbol-like
        let index = run_end(slice, RUN_SIMPLE_SYMBOL);

        // extend the token from slice
        self.token_content.extend_from_slice(&slice[..index]);

        if index < slice.len() {
            // we have successfully consumed the keyword, finish it
            // compute the end locations, no line feeds are allowed in keywords
            self.finish_keyword(
                batch,
                TokenEnd::at_byte(index),
                Content::Stored,
                Some(slice[index]),
            )?;
            self.state = LexerState::Normal;
        }

        Ok(index)
    }

    fn lex_quoted_symbol_closed<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        slice: &[u8],
    ) -> Result<usize, Interrupted<H::Result, LexError<H::Error>>> {
        // we expect a token delimiter to follow the closing pipe
        self.expect_delimiter(slice[0], 0)?;
        // all good, produce the quoted symbol token
        self.sink_slice(
            batch,
            InnerType::QuotedSymbol,
            TokenEnd::at_byte(0),
            Content::Stored,
        )?;
        // the delimiter is not consumed
        self.state = LexerState::Normal;
        Ok(0)
    }

    /// Checks that `next`, the byte at `position` right after a token,
    /// delimits it.
    ///
    /// Called before the token is handed over, so that a token without its
    /// delimiter never reaches the handler; the error spans the token and
    /// the offending byte.
    #[inline]
    fn expect_delimiter<R, E>(
        &self,
        next: u8,
        position: usize,
    ) -> Result<(), Interrupted<R, LexError<E>>> {
        if FAST[next as usize] & FAST_DELIM != 0 {
            Ok(())
        } else {
            Err(self.error_at(LexerErrorKind::MissingDelimiter, position + 1))
        }
    }

    fn lex_comment(
        &mut self,
        slice: &[u8],
    ) -> Result<usize, Interrupted<H::Result, LexError<H::Error>>> {
        // run until comment end
        let index = run_end(slice, RUN_COMMENT_PLAIN);
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

    /// Sinks a decimal token.
    ///
    /// The token's own shape is checked first, then that `next`, the byte
    /// at the end (if there is one), delimits it.
    fn finish_decimal<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        end: TokenEnd,
        content: Content<'a>,
        next: Option<u8>,
    ) -> Result<(), Interrupted<H::Result, LexError<H::Error>>> {
        // decimals of the form 7. without any digit in fractional part are disallowed
        let value = content.bytes(&self.token_content);
        if value.last().is_none_or(|c| *c == b'.') {
            return Err(self.error(LexerErrorKind::FractionDigitExpected, end));
        }
        if let Some(next) = next {
            self.expect_delimiter(next, end.position)?;
        }
        self.sink_slice(batch, InnerType::Decimal, end, content)
    }

    fn finish_numeral<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        end: TokenEnd,
        content: Content<'a>,
    ) -> Result<(), Interrupted<H::Result, LexError<H::Error>>> {
        self.sink_slice(batch, InnerType::Numeral, end, content)
    }

    /// Sinks a hexadecimal/binary token.
    ///
    /// The token's own shape is checked first, then that `next`, the byte
    /// at the end (if there is one), delimits it.
    fn finish_digit_run<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        run: DigitRun,
        end: TokenEnd,
        content: Content<'a>,
        next: Option<u8>,
    ) -> Result<(), Interrupted<H::Result, LexError<H::Error>>> {
        // digit runs must not be empty
        let value = content.bytes(&self.token_content);
        if value.is_empty() {
            return Err(self.error(run.empty_error, end));
        }
        if let Some(next) = next {
            self.expect_delimiter(next, end.position)?;
        }
        self.sink_slice(batch, run.token_type, end, content)
    }

    fn finish_simple_symbol<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        end: TokenEnd,
        content: Content<'a>,
    ) -> Result<(), Interrupted<H::Result, LexError<H::Error>>> {
        self.sink_slice(batch, InnerType::UnquotedSymbol, end, content)
    }

    /// Sinks a keyword.
    ///
    /// The token's own shape is checked first, then that `next`, the byte
    /// at the end (if there is one), delimits it.
    fn finish_keyword<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        end: TokenEnd,
        content: Content<'a>,
        next: Option<u8>,
    ) -> Result<(), Interrupted<H::Result, LexError<H::Error>>> {
        let value = content.bytes(&self.token_content);
        // ensure the keyword is not empty
        if value.is_empty() {
            return Err(self.error(LexerErrorKind::ForbiddenKeywordName, end));
        }
        if let Some(next) = next {
            self.expect_delimiter(next, end.position)?;
        }
        self.sink_slice(batch, InnerType::Keyword, end, content)
    }

    fn finish_string_literal<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        end: TokenEnd,
        content: Content<'a>,
    ) -> Result<(), Interrupted<H::Result, LexError<H::Error>>> {
        self.sink_slice(batch, InnerType::String, end, content)
    }

    /// Sinks a token with the given content, ending at `end`.
    #[inline]
    fn sink_slice<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        ty: InnerType,
        end: TokenEnd,
        content: Content<'a>,
    ) -> Result<(), Interrupted<H::Result, LexError<H::Error>>> {
        // the caller of this function is responsible
        // for ensuring that the constructed token is valid

        // construct the span
        let end = self.location_at(end.position);
        let span = SmtSpan::new_unchecked(self.token_start, end);

        match content {
            Content::Borrowed(bytes) => {
                // this is borrowed content, so put it into the batch
                batch.entries[batch.len] = Some((ty, bytes));
                self.spans[batch.len] = span;
                batch.len += 1;
                if batch.len == BATCH_CAPACITY {
                    self.flush_batch(batch)?;
                }
                Ok(())
            }
            Content::Stored => {
                // this is in our own buffer, so we cannot put it into the batch
                // as we need the buffer usable for the next token
                // flush the batch, then hand over this token
                self.flush_batch(batch)?;
                // store the span and create a single-element batch
                self.spans[0] = span;
                let spans = &self.spans[..1];
                let entry = Some((ty, self.token_content.as_slice()));
                Self::flush_cursor(
                    &mut self.handler,
                    TokenCursor::new(self.version, std::slice::from_ref(&entry), spans),
                    &mut self.version,
                )
            }
        }
    }

    /// Moves the lexer back to `location`, which the tokens handed over
    /// so far end at, discarding whatever was lexed beyond it.
    fn resume_at(&mut self, location: SmtLocation) {
        // the region after the location was lexed once already,
        // restore all bookkeeping
        self.offset = location.offset();
        self.line = location.line();
        self.line_start = location.offset() - location.column();
        // a stop inside an arm leaves it mid-token
        self.state = LexerState::Normal;
        self.token_content.clear();
    }

    fn flush_batch(
        &mut self,
        batch: &mut Batch,
    ) -> Result<(), Interrupted<H::Result, LexError<H::Error>>> {
        // the batch is spent once handed over, no matter what the handler decides
        let len = std::mem::replace(&mut batch.len, 0);
        if len == 0 {
            return Ok(());
        }
        Self::flush_cursor(
            &mut self.handler,
            TokenCursor::new(self.version, &batch.entries[..len], &self.spans[..len]),
            &mut self.version,
        )
    }

    fn flush_cursor(
        handler: &mut H,
        mut cursor: TokenCursor,
        version: &mut SmtVersion,
    ) -> Result<(), Interrupted<H::Result, LexError<H::Error>>> {
        // where lexing continues if the handler stops before the first token
        // relex request empties the cursor, so we need to remember it here
        let first_start = cursor
            .get(0)
            .expect("flushed batch must have at least one token")
            .span()
            .start();

        // flush the cursor
        let result = handler.handle_tokens(&mut cursor);

        // set our version to the cursor-requested version
        *version = cursor.version();

        // process the result
        let result = match result {
            Ok(ControlFlow::Continue(())) if cursor.relex_requested() => Ok(Stop::Relex),
            Ok(ControlFlow::Continue(())) => {
                // ensure the cursor has been fully consumed
                assert!(
                    cursor.is_empty(),
                    "the token handler must consume all tokens before continuing"
                );
                return Ok(());
            }
            Ok(ControlFlow::Break(result)) => {
                assert!(
                    !cursor.relex_requested(),
                    "the token handler cannot both finish and request relex"
                );
                Ok(Stop::Finished(result))
            }
            Err(err) => Err(LexError::Handler(err)),
        };
        // the stop takes effect after the consumed tokens
        let stop_location = match cursor.last_consumed() {
            // nothing was taken, lex again from the first token
            None => first_start,
            // at least one token was taken, lex again after it
            Some(token) => token.span().end(),
        };
        Err(Interrupted {
            result,
            location: stop_location,
        })
    }

    #[inline]
    fn sink_eof(&mut self) -> Result<(), Interrupted<H::Result, LexError<H::Error>>> {
        // construct the span at the first position in the batch
        let end = self.location_at(0);
        self.spans[0] = SmtSpan::new_unchecked(self.token_start, end);

        // the end of file has entry None
        let entry = None;
        let spans = &self.spans[..1];

        Self::flush_cursor(
            &mut self.handler,
            TokenCursor::new(self.version, std::slice::from_ref(&entry), spans),
            &mut self.version,
        )
    }

    /// Moves a fast-path symbol run that cannot be finished
    /// in this slice to the stored path.
    ///
    /// The token itself starts at `index`, its content either at `index`
    /// (simple symbol) or `after` (quoted symbol, excludes pipe), and
    /// the token continues at least to `run_end_at`, where it has been
    /// left unfinished.
    fn store_unfinished_symbol_run(
        &mut self,
        slice: &[u8],
        entry: u8,
        index: usize,
        after: usize,
        run_end_at: usize,
    ) {
        self.start_token(index);
        if entry & FAST_PIPE != 0 {
            // quoted symbol, skip the start pipe
            self.token_content
                .extend_from_slice(&slice[after..run_end_at]);
            self.state = LexerState::QuotedSymbol;
        } else {
            // simple symbol, do not skip anything
            self.token_content
                .extend_from_slice(&slice[index..run_end_at]);
            self.state = LexerState::SimpleSymbol;
        }
    }

    /// Writes a fast-path token into the next batch slot and counts it if `emit`
    /// is one, flushing the batch when it is full.
    ///
    /// The span is on the current line, over `range` in the slice.
    #[inline(always)]
    fn push_fast<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        local: &mut FastState,
        offset: u64,
        entry: (InnerType, &'a [u8]),
        range: std::ops::Range<usize>,
        emit: usize,
    ) -> Result<(), Interrupted<H::Result, LexError<H::Error>>> {
        batch.entries[local.len] = Some(entry);
        self.spans[local.len] = SmtSpan::on_line(
            local.line,
            local.line_start,
            offset + range.start as u64,
            offset + range.end as u64,
        );
        local.len += emit;
        if local.len == BATCH_CAPACITY {
            // Batch capacity reached, we need to flush the batch.
            local.store(self, batch);
            self.flush_batch(batch)?;
            local.len = 0;
        }
        Ok(())
    }

    fn start_token(&mut self, position: usize) {
        // update the token start to the computed location
        self.token_start = self.location_at(position);
        // clear the token string
        self.token_content.clear();
    }

    fn mark_line_feed_at(&mut self, position: usize) {
        // when lexing a run, this is used to mark a line feed
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
    fn error<R, E>(&self, kind: LexerErrorKind, end: TokenEnd) -> Interrupted<R, LexError<E>> {
        self.error_at(kind, end.position + end.at_byte as usize)
    }

    /// Error spanning the token up to `position`.
    ///
    /// Used for errors detected mid-run, e.g. forbidden byte in a string
    /// or a backslash in a quoted symbol.
    fn error_at<R, E>(&self, kind: LexerErrorKind, position: usize) -> Interrupted<R, LexError<E>> {
        let end = self.location_at(position);
        let span = SmtSpan::new_unchecked(self.token_start, end);
        // no tokens have been consumed, as this is an error
        // that occurred during lexing
        Interrupted {
            result: Err(LexError::Lexer(LexerError::new(kind, span))),
            location: end,
        }
    }

    /// Executes an inner lexer step and updates the lexer according to the result.
    ///
    /// Called from the outer public functions.
    fn execute_step(
        &mut self,
        step: impl FnOnce(&mut Self) -> Result<ControlFlow<H::Result>, LexError<H::Error>>,
    ) -> Result<ControlFlow<SmtLocated<H::Result>>, LexError<H::Error>> {
        match step(self) {
            Ok(ControlFlow::Continue(())) => Ok(ControlFlow::Continue(())),
            Ok(ControlFlow::Break(result)) => {
                // get the break location, then reset the lexer
                let location = self.current_location();
                self.reset();
                Ok(ControlFlow::Break(SmtLocated::new(result, location)))
            }
            Err(err) => {
                // set the lexer to failed state
                self.state = LexerState::Failed;
                Err(err)
            }
        }
    }

    /// Resets the lexer to the initial state, including the location and version.
    ///
    /// Called after each [`ControlFlow::Break`] from the handler.
    fn reset(&mut self) {
        self.version = self.initial_version;
        self.state = LexerState::Normal;
        self.token_start = SmtLocation::initial();
        self.token_content.clear();
        self.offset = 0;
        self.line = 0;
        self.line_start = 0;
        // the spans do not need to be reset, they can be kept dirty
    }
}

/// Local state of `lex_normal`.
///
/// Locals improve performance of fast lexing over always going
/// through the lexer and batch references. The struct allows
/// loading/storing them together for better maintainability.
#[derive(Clone, Copy)]
struct FastState {
    /// Current batch length.
    len: usize,
    /// Current line.
    line: u64,
    /// Byte offset of the start of the current line.
    line_start: u64,
}

impl FastState {
    #[inline(always)]
    fn load<H: TokenHandler>(lexer: &Lexer<H>, batch: &Batch) -> Self {
        Self {
            len: batch.len,
            line: lexer.line,
            line_start: lexer.line_start,
        }
    }

    #[inline(always)]
    fn store<H: TokenHandler>(self, lexer: &mut Lexer<H>, batch: &mut Batch) {
        batch.len = self.len;
        lexer.line = self.line;
        lexer.line_start = self.line_start;
    }
}

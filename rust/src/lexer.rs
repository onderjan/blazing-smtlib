//! Lexer that produces tokens from input bytes, handing them over to a token
//! consumer.
//!
//! [`SmtLexer`] hands over [tokens](crate::token) to a consumer that implements
//! [`SmtConsume`] and [`SmtConsumeFrom`]`<`[`SmtLexerCursor`]`>`. This can be
//! an [`SmtWriter`](crate::SmtWriter) or a parser adapted to a consumer via
//! [`SmtParseAdapter`](crate::parser::SmtParseAdapter). The lexer and an
//! adapted parser together form [`SmtReader`](crate::SmtReader).
//!
//! A custom consumer can be used to process the tokens as desired. If
//! [`SmtConsumeFrom`] is implemented for [`SmtLexerCursor`] specifically rather
//! than generically over every [`SmtCursor`], the consumer can use the token
//! spans exposed by the lexer, as in the following example.
//!
//! ```rust
//! # use std::ops::ControlFlow;
//! # use blazing_smtlib::{SmtVersion, span::{SmtSpan, SmtLocated},
//! # token::{SmtToken, SmtConsume, SmtConsumeFrom}, lexer::{SmtLexer, SmtLexerCursor}};
//! // a consumer that finds the span of the first `x` symbol (quoted or unquoted)
//! struct XFinder(Option<SmtSpan>);
//! impl SmtConsume for XFinder {
//!     type Result = Option<SmtSpan>;
//!     type Error = ();
//!     const IS_CONCRETE: bool = false; // whitespace and comments are not handed over
//! }
//! impl SmtConsumeFrom<SmtLexerCursor<'_>> for XFinder {
//!     fn consume(&mut self, cursor: &mut SmtLexerCursor)
//!         -> Result<ControlFlow<Option<SmtSpan>>, ()> {
//!         // process every token in cursor
//!         // next() requires the SmtCursor trait in scope
//!         use blazing_smtlib::token::SmtCursor;
//!         while let Some(next) = cursor.next() {
//!             match cursor.syntax(&next) {
//!                 SmtToken::Symbol(symbol) => {
//!                     if self.0.is_none() && symbol.bytes().as_slice() == b"x" {
//!                         // remember the span
//!                         self.0 = Some(next.span())
//!                     }
//!                 }
//!                 SmtToken::EndOfFile => {
//!                     // EOF, break with a given value
//!                     return Ok(ControlFlow::Break(self.0));
//!                 }
//!                 _ => {}
//!             }
//!         }
//!         // not enough tokens provided from the cursor yet to end the file
//!         Ok(ControlFlow::Continue(()))
//!     }
//! }
//! // lex sample input, handing over tokens progressively to the consumer
//! let input = b"(bvadd x y)";
//! let mut lexer = SmtLexer::new(XFinder(None), SmtVersion::V2_7);
//! let result = lexer.lex_all(input).expect("no error").into_value();
//! let span = result.expect("x should be found");
//! assert!(span.start().offset() == 7 && span.end().offset() == 8);
//! ```
//!
//! It is unspecified how the lexer batches the tokens, only that it provides at
//! least one token per call and the consumer must consume at least one. The
//! consumer is required to return a break value on EOF, and a non-EOF token
//! that would be handed over after the break value results in an error with
//! [`SmtLexicalErrorKind::UnexpectedTrailingToken`]. See [`SmtLexer`] and
//! [`SmtConsumeFrom::consume`] for the details of the handover contract.
//!
//! The inputs can be passed to the lexer in two ways:
//!
//! - In full (the lexer hands the consumer an EOF token at the end): from a
//!   file ([`SmtLexer::lex_file`]), a buffered reader ([`SmtLexer::lex_from`]),
//!   or a full slice ([`SmtLexer::lex_all`]).
//! - In parts using calls of [`SmtLexer::lex_slice`] followed by
//!   [`SmtLexer::lex_eof`].
//!
//! On successful consumer break, the lexer returns the result value augmented
//! with the location where lexing ended and resets itself so it is prepared for
//! lexing another input. On an error, the lexer returns [`SmtLexerError`] or
//! [`SmtLexerReadError`] and goes into a failure state where subsequent lexing
//! will panic.
//!
mod char_class;
mod cursor;
mod error;
mod helpers;
mod recovery;

pub use cursor::{SmtLexerCursor, SmtLexerToken, SmtLexerWindow};
pub use error::{
    SmtLexerError, SmtLexerErrorKind, SmtLexerReadError, SmtLexerReadErrorKind,
    SmtLexicalErrorKind, SmtLexicalExpected,
};
pub use recovery::{SmtFailFast, SmtLexerRecovery, SmtRecover, SmtRecovering};

pub(crate) use cursor::{InnerCategory, LexerCursorAction};

pub(crate) use char_class::CharClass;

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::marker::PhantomData;
use std::path::Path;
use std::{fmt, ops::ControlFlow};

use crate::{
    SmtVersion,
    lexer::{
        char_class::{
            RUN_COMMENT_PLAIN, RUN_DIGIT, RUN_NON_LF_WHITESPACE, RUN_QUOTED_PLAIN,
            RUN_SIMPLE_SYMBOL, RUN_STRING_PLAIN, run_end, run_end_all,
        },
        helpers::{
            BINARY_RUN, Content, DigitRun, FAST, FAST_DELIM, FAST_EMIT, FAST_ON, FAST_PIPE,
            FAST_RUN_MASK, HEXADECIMAL_RUN, START, Start, TokenEnd,
        },
    },
    span::{SmtLocated, SmtLocation, SmtSpan},
    token::{SmtConsume, SmtConsumeFrom, SmtCursor},
};

/// Lexes SMT-LIB input, handing the tokens to a consumer.
///
/// The lexer lexes a byte stream into tokens that it sends
/// to an implementation of [`SmtConsume`], which is expected
/// to break with a value once it has finished processing
/// and expects no more tokens belonging to the value.
/// If any more tokens appear in the stream before
/// its end, the lexer returns an error of the kind
/// [`SmtLexicalErrorKind::UnexpectedTrailingToken`].
///
/// The EOF token is only produced if no value has been
/// produced before the end of file, and the [`SmtConsume`]
/// implementation is required by the contract to break
/// with a value on it.
///
/// When [`SmtLexer::lex_eof`] or [`SmtLexer::lex_all`] returns
/// successfully, the lexer is guaranteed to be reset
/// and ready to lex another byte stream.
///
/// If an error occurs during lexing, the lexer moves
/// into a failure state where all further lexing calls panic.
pub struct SmtLexer<C: SmtConsume, R: SmtLexerRecovery<C> = SmtFailFast> {
    /// Consumer of produced tokens.
    consumer: C,

    /// The SMT-LIB version the lexer currently operates under.
    version: SmtVersion,

    /// The initial SMT-LIB version the lexer will reset to.
    initial_version: SmtVersion,

    /// Current lexer state.
    state: LexerState,

    /// Held-back consumer break result, to be returned when EOF is reached.
    held: Option<SmtLocated<C::Result>>,

    /// Whether the lexer discards bytes until EOF is reached.
    discard: bool,

    /// The number of parentheses left open by the tokens the consumer has consumed.
    ///
    /// Only tracked by a recovering lexer to aid recovery.
    consumed_depth: u64,

    /// The number of parentheses lexed.
    ///
    /// Only tracked by a recovering lexer to aid recovery.
    /// Used to speed up depth tracking in the common case
    /// of consumer consuming the whole batch.
    lexed_depth: u64,

    /// The current state of lexer recovery (if any).
    recovery_state: Option<RecoveryState>,

    /// Location of the start of the currently-processed token.
    token_start: SmtLocation,

    /// The currently-built string content of the currently-processed token.
    token_content: Vec<u8>,

    /// Offset of the start of the byte being processed during lexing.
    ///
    /// It only advances after byte consumption.
    offset: u64,

    /// Number of the latest line (zero-based).
    ///
    /// It only advances after consumption of LF.
    line: u64,

    /// Offset of the start of the current line (after line break, zero-based).
    ///
    /// It only advances after consumption of LF.
    line_start: u64,

    /// Spans of respective batch tokens.
    spans: Box<[SmtSpan; BATCH_CAPACITY]>,

    /// Phantom data for the recovery behaviour.
    ///
    /// The actual recovery behaviour is given by the generic type argument,
    /// this field is a zero-sized type that makes sure the argument is used.
    recovery: PhantomData<R>,
}

impl<C: SmtConsume, R: SmtLexerRecovery<C>> fmt::Debug for SmtLexer<C, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SmtLexer")
            .field("version", &self.version())
            .field("current_location", &self.current_location())
            .finish_non_exhaustive()
    }
}

/// Maximal number of tokens that can be batched.
const BATCH_CAPACITY: usize = 256;

/// Token batch, may be only partially filled.
struct Batch<'a> {
    entries: [Option<(InnerCategory, &'a [u8])>; BATCH_CAPACITY],
    len: usize,
}

/// Why lexing stopped before the end of the slice.
enum Stop {
    /// The consumer requested lexing again from the stop location.
    Relex,
    /// The consumer requested to discard everything from the location.
    Discard,
}

struct Interrupted<E> {
    result: Result<Stop, E>,
    location: SmtLocation,
}

/// A lexing error with the effective failure location.
///
/// For a lexical error, the effective failure location is before the byte that
/// raised it, or the end of the input if the end raised it. For a consumer error,
/// it is after the last token the consumer has consumed.
struct Failure<E> {
    error: SmtLexerError<E>,
    location: SmtLocation,
}

/// The state of recovery in a lexer.
#[derive(Clone, Copy)]
enum RecoveryState {
    /// Nothing more: the end of the input raised the error, so only
    /// the end of the input can be lexed again.
    End,
    /// Nothing yet: recovery starts at a token boundary.
    ///
    /// If no parenthesis is open there, nothing is skipped at all.
    Boundary,
    /// Plain text outside of the strings, quoted symbols, and comments.
    Plain,
    /// Inside string literal.
    String,
    /// At the byte after a backslash in a string literal (SMT-LIB 2.0 only).
    StringEscape,
    /// Inside a quoted symbol.
    QuotedSymbol,
    /// Inside a comment.
    Comment,
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
    /// Quoted symbol closing pipe was encountered, waiting for token delimiter.
    ///
    /// The token cannot be emitted before confirming that the next byte is
    /// a token delimiter; otherwise, an error will occur.
    QuotedSymbolClosed,
    /// Lexing a keyword.
    Keyword,
    /// Lexing a comment.
    Comment,
    /// Lexing whitespace.
    ///
    /// The lexer can only be set to this state if
    /// [`SmtConsume::IS_CONCRETE`] is true,
    /// otherwise the whitespace is eagerly discarded without combining it.
    Whitespace,
    /// A lexer or consumer error was returned; lexing cannot continue.
    Failed,
}

impl<C: for<'a> SmtConsumeFrom<SmtLexerCursor<'a>>> SmtLexer<C> {
    /// Constructs a lexer that stops at its first error.
    pub fn new(consumer: C, version: SmtVersion) -> Self {
        // construct the lexer normally
        // fail-fast is selected by the implementation generics
        Self::construct(consumer, version)
    }

    /// Lexes the whole input including EOF at the end.
    ///
    /// If successful, the lexer is reset before returning
    /// the token consumer result.
    ///
    /// If an error occurs, the lexer moves into a failure state
    /// where all further lexing calls panic.
    ///
    /// The contract of the token consumer forbids it from
    /// returning [`ControlFlow::Continue`] on the EOF token,
    /// and the lexer panics if it does.
    pub fn lex_all(
        &mut self,
        input: &[u8],
    ) -> Result<SmtLocated<C::Result>, SmtLexerError<C::Error>> {
        self.lex_slice(input)?;
        self.lex_eof()
    }

    /// Lexes the content of the buffered reader as the whole input, including
    /// EOF at the end.
    ///
    /// The input is considered to end when the buffered reader returns
    /// a zero-length buffer. A failure while reading is reported as
    /// an I/O error with an empty span at the position reached.
    ///
    /// The buffer content is consumed up to where the consumer requests
    /// discarding the rest or fully if no such request was made.
    ///
    /// Otherwise, behaves as [`lex_all`](Self::lex_all).
    pub fn lex_from<B: BufRead>(
        &mut self,
        mut buf_reader: B,
    ) -> Result<SmtLocated<C::Result>, SmtLexerReadError<C::Error>> {
        loop {
            if self.discarded_from().is_some() {
                // the consumer does not care about any subsequent bytes
                break;
            }
            let buffer = match buf_reader.fill_buf() {
                Ok(buffer) => buffer,
                Err(err) => {
                    let span = SmtSpan::new_empty(self.current_location());
                    return Err(SmtLexerReadError::new(SmtLexerReadErrorKind::Io(err), span));
                }
            };
            if buffer.is_empty() {
                break;
            }
            // consume the bytes lexed, which are fewer than the buffer
            // holds when discarding begins inside it
            let start_offset = self.current_location().offset();
            self.lex_slice(buffer)?;
            let len = self
                .current_location()
                .offset()
                .saturating_sub(start_offset) as usize;
            buf_reader.consume(len);
        }
        Ok(self.lex_eof()?)
    }

    /// Opens the file at `path` and lexes it as the whole input, as
    /// [`lex_from`](Self::lex_from) does.
    ///
    /// A failure to open the file is reported as an I/O error with an empty
    /// span at the start of the input.
    pub fn lex_file(
        &mut self,
        path: impl AsRef<Path>,
    ) -> Result<SmtLocated<C::Result>, SmtLexerReadError<C::Error>> {
        let file = File::open(path).map_err(|err| {
            SmtLexerReadError::new(SmtLexerReadErrorKind::Io(err), SmtSpan::new_zero())
        })?;
        // a large buffer gives the lexer large batches
        const BUF_READER_CAPACITY: usize = 1024 * 1024;
        self.lex_from(BufReader::with_capacity(BUF_READER_CAPACITY, file))
    }

    /// Returns a reference to the token consumer.
    pub fn consumer(&self) -> &C {
        &self.consumer
    }

    /// Returns a mutable reference to the token consumer.
    pub fn consumer_mut(&mut self) -> &mut C {
        &mut self.consumer
    }
}

impl<C: SmtRecover> SmtLexer<C, SmtRecovering> {
    /// Constructs a lexer that recovers from errors (EXPERIMENTAL).
    ///
    /// Lexer recovery is implemented but experimental
    /// since the exact semantics have not yet been set in stone.
    /// It can change or be removed in any version and should not be used.
    #[doc(hidden)]
    pub fn new_recovering(consumer: C, version: SmtVersion) -> Self {
        // construct the lexer normally
        // recovering is selected by the implementation generics
        Self::construct(consumer, version)
    }
}

type ArmLexResult<C> = Result<usize, Interrupted<SmtLexerError<<C as SmtConsume>::Error>>>;
type FinishLexResult<C> = Result<(), Interrupted<SmtLexerError<<C as SmtConsume>::Error>>>;

impl<C: SmtConsume, R: SmtLexerRecovery<C>> SmtLexer<C, R> {
    fn construct(consumer: C, version: SmtVersion) -> Self {
        SmtLexer {
            consumer,
            version,
            initial_version: version,
            state: LexerState::Normal,
            held: None,
            discard: false,
            consumed_depth: 0,
            lexed_depth: 0,
            recovery_state: None,
            token_start: SmtLocation::initial(),
            token_content: Vec::new(),
            offset: 0,
            line: 0,
            line_start: 0,
            spans: Box::new([SmtSpan::new_zero(); BATCH_CAPACITY]),
            recovery: PhantomData,
        }
    }

    /// Returns the version currently in force.
    ///
    /// The version can change if the token consumer asks for it from the
    /// cursor. The end of the input resets the version to the initial one.
    pub fn version(&self) -> SmtVersion {
        self.version
    }

    /// Returns the current lexer location.
    ///
    /// While discarding, the lexer location does not change
    /// and stays where discarding began.
    pub fn current_location(&self) -> SmtLocation {
        self.location_at(0)
    }

    /// Returns the location after which bytes have been discarded (if any).
    ///
    /// Discarding is used to implement the behaviour after `(exit)`.
    pub fn discarded_from(&self) -> Option<SmtLocation> {
        if self.discard {
            Some(self.current_location())
        } else {
            None
        }
    }

    /// Location of `position` in the current slice.
    ///
    /// Every line feed before `position` must be marked before calling this.
    fn location_at(&self, position: usize) -> SmtLocation {
        let offset = self.offset + position as u64;
        SmtLocation::new_unchecked(offset, self.line, offset - self.line_start)
    }
}

impl<C: for<'a> SmtConsumeFrom<SmtLexerCursor<'a>>, R: SmtLexerRecovery<C>> SmtLexer<C, R> {
    /// Lexes the given slice, sending the lexed tokens to the consumer.
    ///
    /// If the consumer produces a result, the result is held back until EOF.
    ///
    /// If an error occurs, the fail-fast lexer moves into
    /// a failure state and all further lexing calls panic.
    pub fn lex_slice(&mut self, slice: &[u8]) -> Result<(), SmtLexerError<C::Error>> {
        if self.discard {
            // pretend that we lexed everything we were given
            return Ok(());
        }

        // a recovering lexer must skip until out of the root-level expression
        // in which the error occurred
        let mut slice = slice;
        if let Some(skip) = self.recovery_state {
            if let RecoveryState::End = skip {
                // the input has ended, there is nothing to skip to
                assert!(
                    slice.is_empty(),
                    "cannot lex a slice after the end of the input"
                );
                return Ok(());
            }
            let Some(skipped) = self.skip_slice(slice, skip) else {
                // the whole slice was skipped
                return Ok(());
            };
            // the lexing goes on from here, tell the consumer before any token
            self.recovery_state = None;
            self.lexed_depth = self.consumed_depth;
            let location = self.current_location();
            R::recover(&mut self.consumer, location);
            slice = &slice[skipped..];
        }

        // execute the inner lexing step
        match self.lex_slice_inner(slice) {
            Ok(()) => Ok(()),
            Err(failure) => {
                // fail on error
                Err(self.fail(failure, false))
            }
        }
    }

    /// Lexes the end of file, sending the lexed tokens to the consumer.
    ///
    /// If there is any pending token, it is processed.
    /// Then, if a result value has been obtained from the consumer,
    /// it is returned. Otherwise, the EOF token is processed,
    /// and its result is returned.
    ///
    /// If an error occurs, the fail-fast lexer moves into
    /// a failure state and all further lexing calls panic.
    ///
    /// The contract of the token consumer forbids it from
    /// returning [`ControlFlow::Continue`] on the EOF token,
    /// and the lexer panics if it does.
    pub fn lex_eof(&mut self) -> Result<SmtLocated<C::Result>, SmtLexerError<C::Error>> {
        // the end of the input forces recovery
        let recovered = self.recovery_state.take().is_some();
        if recovered {
            let location = self.current_location();
            R::recover(&mut self.consumer, location);
        }

        // call inner EOF lexing
        match self.lex_eof_inner() {
            Ok(result) => {
                // the input has ended, reset the lexer
                self.reset();
                Ok(result)
            }
            Err(failure) => {
                if recovered {
                    // the consumer has refused the EOF token with nothing left to abandon:
                    // the error is final and the input has ended, reset the lexer
                    self.reset();
                    Err(failure.error)
                } else {
                    Err(self.fail(failure, true))
                }
            }
        }
    }

    fn lex_eof_inner(&mut self) -> Result<SmtLocated<C::Result>, Failure<C::Error>> {
        // construct a batch for the tokens
        let mut batch: Batch = Batch {
            entries: [None; BATCH_CAPACITY],
            len: 0,
        };

        // EOF is a token delimiter, we need to produce the token
        // that waits for a delimiter if there is any
        let pending = match self.state {
            LexerState::Normal => {
                // nothing to do
                Ok(())
            }
            LexerState::QuotedSymbolClosed => {
                // the end of the input is a token delimiter,
                // produce the quoted symbol
                self.sink_slice(
                    &mut batch,
                    InnerCategory::QuotedSymbol,
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
                Err(self.error(
                    SmtLexicalErrorKind::Expected(SmtLexicalExpected::Base),
                    TokenEnd::EOF,
                ))
            }
            LexerState::StringLiteral | LexerState::StringLiteralBackslashEscape => {
                // we are still within the string literal
                // forbidden as the literal must be totally enclosed by double quotes
                Err(self.error(SmtLexicalErrorKind::UnclosedString, TokenEnd::EOF))
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
                Err(self.error(SmtLexicalErrorKind::UnclosedQuotedSymbol, TokenEnd::EOF))
            }
            LexerState::Whitespace => {
                // we can only be in this state if the consumer wants the
                // whitespace to be emitted, so sink it
                self.sink_slice(
                    &mut batch,
                    InnerCategory::Whitespace,
                    TokenEnd::EOF,
                    Content::Stored,
                )
            }
            LexerState::Comment => {
                // only produce the comment if the consumer wants it
                if C::IS_CONCRETE {
                    self.sink_slice(
                        &mut batch,
                        InnerCategory::Comment,
                        TokenEnd::EOF,
                        Content::Stored,
                    )
                } else {
                    Ok(())
                }
            }
            LexerState::Failed => {
                panic!("cannot lex after a lexer error")
            }
        };

        // return an error, ignore relex / version switch request
        // as we will only send EOF next
        if let Err(Interrupted {
            result: Err(error),
            location,
        }) = pending
        {
            return Err(Failure { error, location });
        }

        if let Some(result) = self.held.take() {
            // we have a held result already, no need to sink EOF, return it now
            return Ok(result);
        }
        // everything has been processed, start the EOF token and sink it
        self.start_token(0);
        let result = self.sink_eof();

        // return an error, ignore relex / version switch request
        if let Err(Interrupted {
            result: Err(error),
            location,
        }) = result
        {
            return Err(Failure { error, location });
        }

        // the consumer EOF is required by the contract to produce a result
        // so we should hold it now
        match self.held.take() {
            Some(result) => Ok(result),
            None => panic!("consumer must not continue on EOF"),
        }
    }

    fn lex_slice_inner(&mut self, slice: &[u8]) -> Result<(), Failure<C::Error>> {
        let mut batch: Batch = Batch {
            entries: [None; BATCH_CAPACITY],
            len: 0,
        };

        let initial_offset = self.offset;
        let mut rest = slice;
        let mut fn_result = Ok(());

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
                    LexerState::QuotedSymbolClosed => {
                        self.lex_quoted_symbol_closed(&mut batch, rest)
                    }
                    LexerState::Keyword => self.lex_keyword(&mut batch, rest),
                    LexerState::Whitespace => self.lex_whitespace(&mut batch, rest),
                    LexerState::Comment => self.lex_comment(&mut batch, rest),
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
                            // we will resume consuming at a given location
                            self.resume_at(location);
                            // every handed-over token borrows this slice
                            // so the location must be equal or greater to initial offset
                            let index = location.offset().checked_sub(initial_offset).expect(
                                "the token consumer must not stop before the starting token",
                            );
                            match stop {
                                Stop::Relex => {
                                    // everything up to the index was already consumed
                                    // continue from there
                                    rest = &slice[index as usize..];
                                    // clear any existing lexer errors we did not get to yet
                                    fn_result = Ok(());
                                    // continue consuming
                                    continue;
                                }
                                Stop::Discard => {
                                    // make sure the rest is discarded and return
                                    self.discard = true;
                                    return Ok(());
                                }
                            }
                        }
                        Err(error) => {
                            // make sure the tokens before the error get handed over
                            fn_result = Err(Failure {
                                error,
                                location: interrupted.location,
                            });
                        }
                    }
                }
            }
        }
    }

    fn lex_normal<'a>(&mut self, batch: &mut Batch<'a>, slice: &'a [u8]) -> ArmLexResult<C> {
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
                if R::RECOVERS {
                    // saturate to avoid going below zero depth
                    // which would happen with too many closing parentheses
                    self.lexed_depth = self.lexed_depth.saturating_sub(1);
                }
                let entry = (InnerCategory::ParenClose, &slice[index..after]);
                self.push_fast(batch, &mut local, offset, entry, index..after, 1)?;
                index = after;
                continue;
            }
            if c == b'(' {
                if R::RECOVERS {
                    self.lexed_depth += 1;
                }
                let entry = (InnerCategory::ParenOpen, &slice[index..after]);
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

                // Check if we need to fall back to state-machine lexing
                // if we have been asked to emit whitespace and are handling it.
                // We need to fall back if we have overrun the slice or encountered
                // a line-feed which needs to update the location line/column.
                let is_whitespace = fast_entry & RUN_NON_LF_WHITESPACE != 0;
                if C::IS_CONCRETE
                    && is_whitespace
                    && matches!(slice.get(run_end_at), None | Some(b'\n'))
                {
                    // the whitespace token does not end on this line inside the slice
                    local.store(self, batch);
                    index = self.start_whitespace(batch, slice, index)?;
                    if index == slice.len() {
                        // we ran out of bytes inside the whitespace
                        return Ok(index);
                    }
                    local = FastState::load(self, batch);
                    continue;
                }

                // We might need to fall back to state-machine lexing if the token
                // we have found is not properly finished.
                // This can only happen if we are processing a quoted symbol
                // and the expected pipe after the end of the run is not there,
                // or if we are processing a simple symbol and we overrun the slice.
                // Parentheses have trivially zero-length runs.
                // If the consumer does not want whitespace to be emitted,
                // it can be discarded split.

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
                // newlines. Whitespace is only emitted if the consumer wants it.
                let entry = if is_quoted {
                    (InnerCategory::QuotedSymbol, &slice[after..run_end_at])
                } else if C::IS_CONCRETE && is_whitespace {
                    // only emitted if the consumer takes whitespace
                    (InnerCategory::Whitespace, &slice[index..token_end])
                } else {
                    (InnerCategory::UnquotedSymbol, &slice[index..token_end])
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
                                self.error_at(SmtLexicalErrorKind::MissingDelimiter, token_end + 1)
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
                // whitespace needs no delimiter, it is emitted only if the consumer takes it
                let emit = if C::IS_CONCRETE {
                    emit | is_whitespace as usize
                } else {
                    emit
                };
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
                    if C::IS_CONCRETE {
                        // the line feed starts a whitespace token
                        index = self.start_whitespace(batch, slice, index)?;
                        if index == slice.len() {
                            return Ok(index);
                        }
                    } else {
                        // line feeds must be marked for line offsets
                        // mark it and update the index
                        self.mark_line_feed_at(index);
                        index = after;
                    }
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
                            // we ran out of bytes while inside the comment
                            // extend the content if if should be emitted
                            if C::IS_CONCRETE {
                                self.token_content.extend_from_slice(&slice[after..]);
                            }
                            // update the state and return
                            self.state = LexerState::Comment;
                            return Ok(end);
                        }
                    }
                    // we have reached the end of the comment, which includes
                    // the byte that ended it but not its semicolon
                    // sink the content if it should be emitted
                    if C::IS_CONCRETE {
                        self.sink_slice(
                            batch,
                            InnerCategory::Comment,
                            TokenEnd::at_byte(end + 1),
                            Content::Borrowed(&slice[after..end + 1]),
                        )?;
                    }
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
                        return Err(
                            self.error_at(SmtLexicalErrorKind::NumeralLeadingZero, after + 1)
                        );
                    }
                    match slice.get(after_end) {
                        Some(b'.') => {
                            // a dot starts a fraction,
                            // try to do a subsequent run of fraction digits
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
                    return Err(self.error_at(SmtLexicalErrorKind::UnexpectedByte, after));
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
    ) -> ArmLexResult<C> {
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
            return Err(self.error_at(SmtLexicalErrorKind::NumeralLeadingZero, 1));
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
    ) -> ArmLexResult<C> {
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

    fn lex_base_selection(&mut self, slice: &[u8]) -> ArmLexResult<C> {
        let c = slice[0];
        self.state = match c {
            b'x' => LexerState::Hexadecimal,
            b'b' => LexerState::Binary,
            _ => {
                return Err(
                    self.error_at(SmtLexicalErrorKind::Expected(SmtLexicalExpected::Base), 1)
                );
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
    ) -> ArmLexResult<C> {
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
    ) -> ArmLexResult<C> {
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
                    return Err(self.error_at(
                        SmtLexicalErrorKind::ForbiddenByteInString,
                        consumed + index + 1,
                    ));
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
    ) -> ArmLexResult<C> {
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
                    return Err(self.error_at(
                        SmtLexicalErrorKind::ForbiddenByteInString,
                        consumed + index + 1,
                    ));
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

    fn lex_simple_symbol<'a>(&mut self, batch: &mut Batch<'a>, slice: &[u8]) -> ArmLexResult<C> {
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

    fn lex_quoted_symbol<'a>(&mut self, batch: &mut Batch<'a>, mut rest: &[u8]) -> ArmLexResult<C> {
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
                                InnerCategory::QuotedSymbol,
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
                        SmtLexicalErrorKind::BackslashInQuotedSymbol,
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
                        SmtLexicalErrorKind::ForbiddenByteInQuotedSymbol,
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

    fn lex_keyword<'a>(&mut self, batch: &mut Batch<'a>, slice: &[u8]) -> ArmLexResult<C> {
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
    ) -> ArmLexResult<C> {
        // we expect a token delimiter to follow the closing pipe
        self.expect_delimiter(slice[0], 0)?;
        // all good, produce the quoted symbol token
        self.sink_slice(
            batch,
            InnerCategory::QuotedSymbol,
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
    /// delimiter never reaches the consumer; the error spans the token and
    /// the offending byte.
    #[inline]
    fn expect_delimiter<E>(
        &self,
        next: u8,
        position: usize,
    ) -> Result<(), Interrupted<SmtLexerError<E>>> {
        if FAST[next as usize] & FAST_DELIM != 0 {
            Ok(())
        } else {
            Err(self.error_at(SmtLexicalErrorKind::MissingDelimiter, position + 1))
        }
    }

    /// Lexes the whitespace run that starts at `index` of the slice,
    /// to be handed over as a token.
    ///
    /// Returns the position after the run. If the run ends inside the slice,
    /// its token is sunk with borrowed content. Otherwise, the run is stored,
    /// the state becomes `Whitespace`, and the length of the slice is returned.
    fn start_whitespace<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        slice: &'a [u8],
        index: usize,
    ) -> ArmLexResult<C> {
        self.start_token(index);
        let mut end = index;
        loop {
            // find the first byte that is not whitespace other than a line feed
            end += run_end(&slice[end..], RUN_NON_LF_WHITESPACE);
            match slice.get(end) {
                Some(b'\n') => {
                    // the line feed is a part of the run, mark it and continue
                    self.mark_line_feed_at(end);
                    end += 1;
                }
                Some(_) => {
                    // the run has ended inside the slice
                    self.finish_whitespace(
                        batch,
                        TokenEnd::at_byte(end),
                        Content::Borrowed(&slice[index..end]),
                    )?;
                    return Ok(end);
                }
                None => {
                    // we ran out of bytes, update the content and state
                    self.token_content.extend_from_slice(&slice[index..]);
                    self.state = LexerState::Whitespace;
                    return Ok(slice.len());
                }
            }
        }
    }

    fn lex_whitespace<'a>(&mut self, batch: &mut Batch<'a>, mut rest: &[u8]) -> ArmLexResult<C> {
        // we know that the consumer is interested in the whitespace
        // as it would otherwise be immediately discarded instead
        // of the state change
        let mut consumed = 0;
        loop {
            // find the first byte that is not non-LF whitespace
            let index = run_end(rest, RUN_NON_LF_WHITESPACE);
            // inspect the problematic byte
            match rest.get(index) {
                Some(b'\n') => {
                    // mark the line feed at the given position
                    self.mark_line_feed_at(consumed + index);
                    // prepare for the next run
                    // extend the token content with everything including this LF
                    self.token_content.extend_from_slice(&rest[..index + 1]);
                    // take it out of this slice and remember it is consumed
                    rest = &rest[index + 1..];
                    consumed += index + 1;
                }
                Some(_) => {
                    // end of whitespace
                    // extend and finish the token
                    let after_whitespace_end = consumed + index;
                    self.token_content.extend_from_slice(&rest[..index]);
                    self.finish_whitespace(
                        batch,
                        TokenEnd::at_byte(after_whitespace_end),
                        Content::Stored,
                    )?;
                    // go back to normal state, consuming the whitespace
                    self.state = LexerState::Normal;
                    return Ok(after_whitespace_end);
                }
                None => {
                    // we ran out of bytes before the token ended
                    // extend the token content with everything
                    // keep the whitespace state
                    self.token_content.extend_from_slice(rest);
                    return Ok(consumed + rest.len());
                }
            }
        }
    }

    fn lex_comment<'a>(&mut self, batch: &mut Batch<'a>, slice: &[u8]) -> ArmLexResult<C> {
        // run until comment end
        let index = run_end(slice, RUN_COMMENT_PLAIN);
        let Some(c) = slice.get(index) else {
            // the comment continues; if we are producing comments,
            // extend the content from the whole slice
            if C::IS_CONCRETE {
                self.token_content.extend_from_slice(slice);
            }
            // remain in comment state
            return Ok(slice.len());
        };

        // the comment has ended, either by CR or LF
        // if it ended by LF, we must mark it
        if *c == b'\n' {
            self.mark_line_feed_at(index);
        }

        let after_comment_end = index + 1;

        if C::IS_CONCRETE {
            // we need to produce the comment token
            // extend the comment content and finish the token
            self.token_content
                .extend_from_slice(&slice[..after_comment_end]);
            self.sink_slice(
                batch,
                InnerCategory::Comment,
                TokenEnd::at_byte(after_comment_end),
                Content::Stored,
            )?;
        }

        // move back to the normal state and return
        self.state = LexerState::Normal;
        Ok(after_comment_end)
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
    ) -> FinishLexResult<C> {
        // decimals of the form 7. without any digit in fractional part are disallowed
        let value = content.bytes(&self.token_content);
        if value.last().is_none_or(|c| *c == b'.') {
            return Err(self.error(
                SmtLexicalErrorKind::Expected(SmtLexicalExpected::FractionDigit),
                end,
            ));
        }
        if let Some(next) = next {
            self.expect_delimiter(next, end.position)?;
        }
        self.sink_slice(batch, InnerCategory::Decimal, end, content)
    }

    fn finish_numeral<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        end: TokenEnd,
        content: Content<'a>,
    ) -> FinishLexResult<C> {
        self.sink_slice(batch, InnerCategory::Numeral, end, content)
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
    ) -> FinishLexResult<C> {
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
    ) -> FinishLexResult<C> {
        self.sink_slice(batch, InnerCategory::UnquotedSymbol, end, content)
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
    ) -> FinishLexResult<C> {
        let value = content.bytes(&self.token_content);
        // ensure the keyword is not empty
        if value.is_empty() {
            return Err(self.error(SmtLexicalErrorKind::EmptyKeyword, end));
        }
        if let Some(next) = next {
            self.expect_delimiter(next, end.position)?;
        }
        self.sink_slice(batch, InnerCategory::Keyword, end, content)
    }

    fn finish_string_literal<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        end: TokenEnd,
        content: Content<'a>,
    ) -> FinishLexResult<C> {
        self.sink_slice(batch, InnerCategory::String, end, content)
    }

    fn finish_whitespace<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        end: TokenEnd,
        content: Content<'a>,
    ) -> FinishLexResult<C> {
        self.sink_slice(batch, InnerCategory::Whitespace, end, content)
    }

    /// Sinks a token with the given content, ending at `end`.
    #[inline]
    fn sink_slice<'a>(
        &mut self,
        batch: &mut Batch<'a>,
        ty: InnerCategory,
        end: TokenEnd,
        content: Content<'a>,
    ) -> FinishLexResult<C> {
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
                    &mut self.consumer,
                    SmtLexerCursor::new(self.version, std::slice::from_ref(&entry), spans),
                    &mut self.version,
                    &mut self.consumed_depth,
                    &mut self.lexed_depth,
                    &mut self.held,
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

    fn flush_batch(&mut self, batch: &mut Batch) -> FinishLexResult<C> {
        // the batch is spent once handed over, no matter what the consumer decides
        let len = std::mem::replace(&mut batch.len, 0);
        if len == 0 {
            return Ok(());
        }
        Self::flush_cursor(
            &mut self.consumer,
            SmtLexerCursor::new(self.version, &batch.entries[..len], &self.spans[..len]),
            &mut self.version,
            &mut self.consumed_depth,
            &mut self.lexed_depth,
            &mut self.held,
        )
    }

    fn flush_cursor(
        consumer: &mut C,
        mut cursor: SmtLexerCursor,
        version: &mut SmtVersion,
        consumed_depth: &mut u64,
        lexed_depth: &mut u64,
        held: &mut Option<SmtLocated<C::Result>>,
    ) -> FinishLexResult<C> {
        // flush the cursor until nothing remains
        while let Some(peeked) = cursor.peek() {
            if held.is_some() {
                // we have still have tokens to flush,
                // but the result was already given to us
                // no need to flush more
                let span = peeked.span();
                // the cursor was not fully consumed, finish it
                Self::finish_cursor(cursor, consumed_depth, lexed_depth);

                return Err(Interrupted {
                    result: Err(SmtLexerError::new(
                        SmtLexerErrorKind::Lexical(SmtLexicalErrorKind::UnexpectedTrailingToken),
                        span,
                        None,
                    )),
                    location: span.start(),
                });
            }

            let result = consumer.consume(&mut cursor);

            // get the location where the cursor ended up
            // this will panic if no tokens were consumed,
            // which violates the consumer contract
            let consumed_span = cursor
                .consumed_span()
                .expect("token consumer must consume at least one token");

            // set our version to the cursor-requested version
            *version = cursor.version();

            // process the result
            let result = match result {
                Ok(flow) => {
                    if let ControlFlow::Break(result) = flow {
                        // hold the result
                        *held = Some(SmtLocated::new(result, consumed_span.end()));
                    }
                    match cursor.action() {
                        LexerCursorAction::None => {
                            // zero the number of consumed tokens in the cursor
                            cursor.reset_consumed();
                            // continue flushing until nothing remains
                            continue;
                        }
                        LexerCursorAction::Relex => {
                            // we need to stop and relex here
                            Ok(Stop::Relex)
                        }
                        LexerCursorAction::Discard => {
                            // we need to discard from now on
                            Ok(Stop::Discard)
                        }
                    }
                }
                Err(err) => Err(SmtLexerError::new(
                    SmtLexerErrorKind::Consumer(err),
                    consumed_span,
                    None,
                )),
            };
            // the cursor was not necessarily fully consumed, finish it
            Self::finish_cursor(cursor, consumed_depth, lexed_depth);
            // the stop takes effect after the consumed tokens
            return Err(Interrupted {
                result,
                location: consumed_span.end(),
            });
        }
        // everything was consumed without break or error
        // the consumer has taken every token lexed so far
        // as the cursor is empty, so the consumed parentheses
        // are the same that were lexed and we can find out
        // the new depth easily
        if R::RECOVERS {
            *consumed_depth = *lexed_depth;
        }
        Ok(())
    }

    fn finish_cursor(cursor: SmtLexerCursor, consumed_depth: &mut u64, lexed_depth: &mut u64) {
        if !R::RECOVERS {
            // just drop the cursor
            return;
        }

        // the consumer may not have taken the whole batch
        // we must count parentheses for recovery
        // count the actually consumed parentheses only
        // and reset the lexed depth to them
        for entry in cursor.consumed_entries() {
            match entry {
                Some((InnerCategory::ParenOpen, _)) => *consumed_depth += 1,
                Some((InnerCategory::ParenClose, _)) => {
                    *consumed_depth = consumed_depth.saturating_sub(1)
                }
                _ => {}
            }
        }
        *lexed_depth = *consumed_depth;
    }

    #[inline]
    fn sink_eof(&mut self) -> FinishLexResult<C> {
        // construct the span at the first position in the batch
        let end = self.location_at(0);
        self.spans[0] = SmtSpan::new_unchecked(self.token_start, end);

        // the end of file has entry None
        let entry = None;
        let spans = &self.spans[..1];

        Self::flush_cursor(
            &mut self.consumer,
            SmtLexerCursor::new(self.version, std::slice::from_ref(&entry), spans),
            &mut self.version,
            &mut self.consumed_depth,
            &mut self.lexed_depth,
            &mut self.held,
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
        entry: (InnerCategory, &'a [u8]),
        range: std::ops::Range<usize>,
        emit: usize,
    ) -> FinishLexResult<C> {
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

    /// Error spanning the token so far and, if it ended at a byte, that byte.
    fn error<E>(&self, kind: SmtLexicalErrorKind, end: TokenEnd) -> Interrupted<SmtLexerError<E>> {
        // if the token ended at a byte, that byte raised the error,
        // otherwise the end of the input did
        self.error_with(kind, end.position + end.at_byte as usize, end.position)
    }

    /// Error spanning the token up to `position`.
    ///
    /// Used for errors detected mid-run, e.g. forbidden byte in a string
    /// or a backslash in a quoted symbol.
    fn error_at<E>(
        &self,
        kind: SmtLexicalErrorKind,
        position: usize,
    ) -> Interrupted<SmtLexerError<E>> {
        // the byte before the position raised the error
        let raised_by = position
            .checked_sub(1)
            .expect("an error detected at a byte must span that byte");
        self.error_with(kind, position, raised_by)
    }

    /// Error spanning up to `position` with effective failure at `failure`.
    fn error_with<E>(
        &self,
        kind: SmtLexicalErrorKind,
        position: usize,
        failure: usize,
    ) -> Interrupted<SmtLexerError<E>> {
        let end = self.location_at(position);
        let span = SmtSpan::new_unchecked(self.token_start, end);
        // no tokens have been consumed, as this is an error
        // that occurred during lexing
        Interrupted {
            result: Err(SmtLexerError::new(
                SmtLexerErrorKind::Lexical(kind),
                span,
                None,
            )),
            location: self.location_at(failure),
        }
    }

    /// Moves the lexer into failure mode and returns the error.
    ///
    /// A fail-fast lexer has no way out of the failure mode. A recovering lexer
    /// makes the consumer abandon its current work and skips bytes until recovery is made.
    fn fail(&mut self, failure: Failure<C::Error>, at_end: bool) -> SmtLexerError<C::Error> {
        if !R::RECOVERS {
            // set the lexer to failed state
            self.state = LexerState::Failed;
            return failure.error;
        }

        let skip = if at_end {
            // the input has ended, nothing is left to skip
            RecoveryState::End
        } else {
            // start recovering from inside the string or quoted symbol if necessary
            match failure.error.kind() {
                SmtLexerErrorKind::Lexical(kind) => match kind {
                    SmtLexicalErrorKind::ForbiddenByteInString => RecoveryState::String,
                    SmtLexicalErrorKind::BackslashInQuotedSymbol
                    | SmtLexicalErrorKind::ForbiddenByteInQuotedSymbol => {
                        RecoveryState::QuotedSymbol
                    }
                    _ => RecoveryState::Plain,
                },
                // the consumer fails at the boundary after a whole token
                SmtLexerErrorKind::Consumer(_) => RecoveryState::Boundary,
            }
        };

        // drop the held result
        self.held = None;
        // start recovering from the given failure location
        self.resume_at(failure.location);
        R::abandon(&mut self.consumer, failure.location);
        self.recovery_state = Some(skip);
        failure.error.continuing_from(failure.location)
    }

    /// Skips the input while recovering.
    ///
    /// Returns the position in the slice where the recovery was made,
    /// or returns [`Option::None`] if it has not yet been done.
    fn skip_slice(&mut self, slice: &[u8], mut skip: RecoveryState) -> Option<usize> {
        if let RecoveryState::Boundary = skip {
            if self.consumed_depth == 0 {
                // the consumer failed after a whole value, no recovery needed
                return Some(0);
            }
            // we are still at some depth and need to recover
            skip = RecoveryState::Plain;
        }

        let legacy = self.version == SmtVersion::V2_0;
        for (position, &c) in slice.iter().enumerate() {
            skip = match skip {
                RecoveryState::End | RecoveryState::Boundary | RecoveryState::Plain => match c {
                    b'"' => RecoveryState::String,
                    b'|' => RecoveryState::QuotedSymbol,
                    b' ' | b'\t' | b'\r' | b'\n' | b'(' | b')' | b';'
                        if self.consumed_depth == 0 =>
                    {
                        // delimits the error end while nothing is open, we have recoveded
                        self.offset += position as u64;
                        return Some(position);
                    }
                    b';' => RecoveryState::Comment,
                    b'(' => {
                        self.consumed_depth += 1;
                        RecoveryState::Plain
                    }
                    b')' => {
                        // depth must be nonzero here as zero depth would have ended recovery
                        self.consumed_depth -= 1;
                        if self.consumed_depth == 0 {
                            // recover after the closing parenthesis
                            self.offset += position as u64 + 1;
                            return Some(position + 1);
                        }
                        RecoveryState::Plain
                    }
                    _ => RecoveryState::Plain,
                },
                RecoveryState::String => match c {
                    b'"' => RecoveryState::Plain,
                    // in the legacy 2.0 mode, a backslash escapes the byte after it
                    b'\\' if legacy => RecoveryState::StringEscape,
                    _ => RecoveryState::String,
                },
                RecoveryState::StringEscape => RecoveryState::String,
                RecoveryState::QuotedSymbol => match c {
                    b'|' => RecoveryState::Plain,
                    _ => RecoveryState::QuotedSymbol,
                },
                RecoveryState::Comment => match c {
                    b'\n' | b'\r' => RecoveryState::Plain,
                    _ => RecoveryState::Comment,
                },
            };
            if c == b'\n' {
                // the line feed was skipped, it must be marked for line offsets
                self.mark_line_feed_at(position);
            }
        }

        // we ran out of bytes, update the offset and what is being skipped
        self.offset += slice.len() as u64;
        self.recovery_state = Some(skip);
        None
    }

    /// Resets the lexer to the initial state, including the location and version.
    ///
    /// Called at the end of every input.
    fn reset(&mut self) {
        self.version = self.initial_version;
        self.state = LexerState::Normal;
        self.held = None;
        self.discard = false;
        self.consumed_depth = 0;
        self.lexed_depth = 0;
        self.recovery_state = None;
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
    fn load<C: SmtConsume, R: SmtLexerRecovery<C>>(lexer: &SmtLexer<C, R>, batch: &Batch) -> Self {
        Self {
            len: batch.len,
            line: lexer.line,
            line_start: lexer.line_start,
        }
    }

    #[inline(always)]
    fn store<C: SmtConsume, R: SmtLexerRecovery<C>>(
        self,
        lexer: &mut SmtLexer<C, R>,
        batch: &mut Batch,
    ) {
        batch.len = self.len;
        lexer.line = self.line;
        lexer.line_start = self.line_start;
    }
}

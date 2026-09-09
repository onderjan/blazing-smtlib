use crate::{
    String8,
    read::lexer::{
        LexerErrorKind, LexerState,
        char_class::{BINARY_DIGIT, CharClass, DIGIT, HEX_DIGIT, SIMPLE_SYMBOL},
    },
    token::TokenType,
};

/// What a byte does in the normal state.
#[derive(Clone, Copy)]
pub(super) enum Start {
    Whitespace,
    LineFeed,
    ParenOpen,
    ParenClose,
    Comment,
    Hash,
    Quote,
    Colon,
    Pipe,
    Digit,
    Symbol,
    Other,
}

impl Start {
    const fn classify(c: u8) -> Self {
        let flags = CharClass::flags(c);
        match c {
            b' ' | b'\t' | b'\r' => Start::Whitespace,
            b'\n' => Start::LineFeed,
            b'(' => Start::ParenOpen,
            b')' => Start::ParenClose,
            b';' => Start::Comment,
            b'#' => Start::Hash,
            b'"' => Start::Quote,
            b':' => Start::Colon,
            b'|' => Start::Pipe,
            _ if flags & DIGIT != 0 => Start::Digit,
            _ if flags & SIMPLE_SYMBOL != 0 => Start::Symbol,
            _ => Start::Other,
        }
    }
}

/// Normal-state dispatch table.
pub(super) static START: [Start; 256] = {
    let mut table = [Start::Other; 256];
    let mut i = 0;
    while i < 256 {
        table[i] = Start::classify(i as u8);
        i += 1;
    }
    table
};

#[derive(Clone, Copy)]
pub(super) struct DigitRun {
    pub flag: u8,
    pub state: LexerState,
    pub token_type: TokenType,
    pub empty_error: LexerErrorKind,
}
pub(super) const HEXADECIMAL_RUN: DigitRun = DigitRun {
    flag: HEX_DIGIT,
    state: LexerState::Hexadecimal,
    token_type: TokenType::Hexadecimal,
    empty_error: LexerErrorKind::HexadecimalDigitExpected,
};
pub(super) const BINARY_RUN: DigitRun = DigitRun {
    flag: BINARY_DIGIT,
    state: LexerState::Binary,
    token_type: TokenType::Binary,
    empty_error: LexerErrorKind::BinaryDigitExpected,
};

/// Helper struct for where a token ended.
#[derive(Clone, Copy)]
pub(super) struct TokenEnd {
    /// The position after `Lexer.offset` where the token ended.
    pub position: usize,
    /// Whether the token end was detected at a byte that is not a part of the token.
    pub at_byte: bool,
}

impl TokenEnd {
    pub(super) const EOF: TokenEnd = TokenEnd {
        position: 0,
        at_byte: false,
    };
    pub(super) fn at_byte(position: usize) -> Self {
        TokenEnd {
            position,
            at_byte: true,
        }
    }
}

/// Determines whether the bytes of a finished token are.
#[derive(Clone, Copy)]
pub(super) enum Content<'a> {
    /// Accumulated in lexer token content.
    Stored,
    /// Still in the input slice.
    Borrowed(&'a [u8]),
}

impl<'a> Content<'a> {
    pub(super) fn bytes<'s>(self, stored: &'s String8) -> &'s [u8]
    where
        'a: 's,
    {
        match self {
            Content::Stored => stored.as_slice(),
            Content::Borrowed(bytes) => bytes,
        }
    }
}

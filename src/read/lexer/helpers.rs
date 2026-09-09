use crate::{
    read::lexer::{
        LexerErrorKind,
        char_class::{BINARY_DIGIT, HEX_DIGIT},
    },
    token::TokenType,
};

#[derive(Clone, Copy)]
pub(super) struct DigitRun {
    pub flag: u8,
    pub token_type: TokenType,
    pub empty_error: LexerErrorKind,
}
pub(super) const HEXADECIMAL_RUN: DigitRun = DigitRun {
    flag: HEX_DIGIT,
    token_type: TokenType::Hexadecimal,
    empty_error: LexerErrorKind::HexadecimalDigitExpected,
};
pub(super) const BINARY_RUN: DigitRun = DigitRun {
    flag: BINARY_DIGIT,
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

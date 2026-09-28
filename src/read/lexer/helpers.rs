use crate::{
    String8,
    read::lexer::{
        LexerErrorKind, LexerState,
        char_class::{
            CharClass, RUN_BINARY_DIGIT, RUN_COMMENT_PLAIN, RUN_DIGIT, RUN_HEX_DIGIT,
            RUN_NON_LF_WHITESPACE, RUN_QUOTED_PLAIN, RUN_SIMPLE_SYMBOL, RUN_STRING_PLAIN,
        },
    },
    token::InnerType,
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
        let flags = CharClass::run_flags(c);
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
            _ if flags & RUN_DIGIT != 0 => Start::Digit,
            _ if flags & RUN_SIMPLE_SYMBOL != 0 => Start::Symbol,
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

/// Determines the inner type through `FAST_INNER`.
pub(super) const FAST_TYPE_MASK: u8 = 0b0000_0011;

/// Determines whether the fast path should be taken.
pub(super) const FAST_ON: u8 = 0b0000_0100;

/// Determines whether a token should be emitted in the fast path.
///
/// Is unset for whitespace.
pub(super) const FAST_EMIT: u8 = 0b0000_1000;

/// Determines the run mask that should be used.
pub(super) const FAST_RUN_MASK: u8 = 0b0111_0000;

/// Set if this is a quoted symbol ending with a pipe.
///
/// The pipe requires special behaviour: the token extends
/// from the opening pipe to the closing pipe including them,
/// but its content excludes the pipes.
pub(super) const FAST_PIPE: u8 = 0b1000_0000;

/// Masks for the fast flags.
const FAST_MASKS: [u8; 5] = [FAST_TYPE_MASK, FAST_ON, FAST_EMIT, FAST_RUN_MASK, FAST_PIPE];

/// Fast masks partition u8 and are pairwise distinct.
const _: () = {
    let mut union = 0u8;
    let mut i = 0;
    while i < FAST_MASKS.len() {
        assert!(union & FAST_MASKS[i] == 0, "fast masks must not overlap");
        union |= FAST_MASKS[i];
        i += 1;
    }
    assert!(
        union == u8::MAX,
        "fast masks must cover every bit of the byte"
    );
};

/// Fast run flags contain exactly the three run flags we need.
const _: () = assert!(
    (RUN_SIMPLE_SYMBOL | RUN_NON_LF_WHITESPACE | RUN_QUOTED_PLAIN) & FAST_RUN_MASK == FAST_RUN_MASK
        && (RUN_STRING_PLAIN | RUN_DIGIT | RUN_HEX_DIGIT | RUN_BINARY_DIGIT | RUN_COMMENT_PLAIN)
            & FAST_RUN_MASK
            == 0,
    "exactly the fast-path run flags must lie inside FAST_RUN_MASK"
);

/// Index of whitespace in `FAST_INNER`.
pub(super) const FAST_TYPE_WHITESPACE: u8 = 0;
/// Index of symbol in `FAST_INNER`.
pub(super) const FAST_TYPE_SYMBOL: u8 = 1;
/// Index of opening parenthesis in `FAST_INNER`.
pub(super) const FAST_TYPE_PAREN_OPEN: u8 = 2;
/// Index of closing parenthesis in `FAST_INNER`.
pub(super) const FAST_TYPE_PAREN_CLOSE: u8 = 3;

/// The inner type per fast type index.
///
/// Whitespace is never emitted, so its entry is never observed.
pub(super) const FAST_INNER: [InnerType; 4] = [
    InnerType::UnquotedSymbol,
    InnerType::UnquotedSymbol,
    InnerType::ParenOpen,
    InnerType::ParenClose,
];

/// Fast dispatch bitmasks for every input byte.
///
/// The bitmasks carry the masks present in `FAST_MASKS`.
pub(super) static FAST: [u8; 256] = {
    let mut table = [0u8; 256];
    let mut i = 0;
    while i < 256 {
        let c = i as u8;
        let flags = CharClass::run_flags(c);
        table[i] = match c {
            b' ' | b'\t' | b'\r' => FAST_ON | RUN_NON_LF_WHITESPACE | FAST_TYPE_WHITESPACE,
            b'(' => FAST_ON | FAST_EMIT | FAST_TYPE_PAREN_OPEN,
            b')' => FAST_ON | FAST_EMIT | FAST_TYPE_PAREN_CLOSE,
            b'|' => FAST_ON | FAST_EMIT | FAST_PIPE | RUN_QUOTED_PLAIN | FAST_TYPE_SYMBOL,
            // a simple symbol may contain digits but must not start with one
            _ if flags & RUN_SIMPLE_SYMBOL != 0 && flags & RUN_DIGIT == 0 => {
                FAST_ON | FAST_EMIT | RUN_SIMPLE_SYMBOL | FAST_TYPE_SYMBOL
            }
            _ => 0,
        };
        i += 1;
    }
    table
};

/// The fast table and `START` agree on which bytes are fast, so that the
/// `START` arms of those classes can be absent.
const _: () = {
    let mut i = 0;
    while i < 256 {
        let fast = FAST[i] & FAST_ON != 0;
        let covered = matches!(
            START[i],
            Start::Whitespace | Start::ParenOpen | Start::ParenClose | Start::Pipe | Start::Symbol
        );
        assert!(
            fast == covered,
            "a byte is fast exactly when its START class is one the fast path replaces"
        );
        i += 1;
    }
};

#[derive(Clone, Copy)]
pub(super) struct DigitRun {
    pub flag: u8,
    pub state: LexerState,
    pub token_type: InnerType,
    pub empty_error: LexerErrorKind,
}
pub(super) const HEXADECIMAL_RUN: DigitRun = DigitRun {
    flag: RUN_HEX_DIGIT,
    state: LexerState::Hexadecimal,
    token_type: InnerType::Hexadecimal,
    empty_error: LexerErrorKind::HexadecimalDigitExpected,
};
pub(super) const BINARY_RUN: DigitRun = DigitRun {
    flag: RUN_BINARY_DIGIT,
    state: LexerState::Binary,
    token_type: InnerType::Binary,
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

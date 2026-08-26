mod char_class;

use char_class::{U8OrEof, char_class_opt};

pub use char_class::CharClass;

use crate::{
    SmtBinDigits, SmtDecimal, SmtDigits, SmtHexDigits, SmtKeyword, SmtNumeral, SmtSpan,
    SmtStringContent, SmtSymbol, String8,
    token::{Reserved, Token, TokenKind},
};

pub enum LexerState {
    Normal,
    Fraction {
        whole_part: String8,
        fractional_part: String8,
    },
    NumeralOrDecimal(String8),
    Hexadecimal(String8),
    Binary(String8),
    HexadecimalOrBinary,
    StringLiteral(String8),
    StringLiteralDoubleQuote(String8),
    SimpleSymbol(String8),
    Keyword(String8),
    QuotedSymbol(String8),
    Comment,
}

pub struct Lexer {
    state: LexerState,
    // Current byte offset since start of reading.
    //
    // Increments after lexing, i.e. when lexing, points at the
    // "start" of the currently read character.
    offset: u64,
    // Byte offset of the start of the token being currently read.
    token_start: u64,
}

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LexerError {
    UnexpectedCharacter,
    FractionDigitExpected,
    HexadecimalDigitExpected,
    BinaryDigitExpected,
    BaseSelectionExpected,
    UnclosedStringLiteral,
    ForbiddenCharInString,
    KeywordNameExpected,
    KeywordReserved,
    BackslashInQuotedSymbol,
    ForbiddenCharInQuotedSymbol,
    UnclosedQuotedSymbol,
    NumeralLeadingZero,
}

impl Lexer {
    pub fn new() -> Self {
        Lexer {
            state: LexerState::Normal,
            token_start: 0,
            offset: 0,
        }
    }

    pub fn lex_next(&mut self, c: u8) -> Result<Vec<Token>, LexerError> {
        let tokens = self.lex_char(U8OrEof::U8(c))?;
        self.offset += 1;
        Ok(tokens)
    }

    pub fn lex_eof(&mut self) -> Result<Vec<Token>, LexerError> {
        self.lex_char(U8OrEof::Eof)
    }

    fn lex_normal(&mut self, mut tokens: Vec<Token>, c: U8OrEof) -> Result<Vec<Token>, LexerError> {
        let c = match c {
            U8OrEof::U8(c) => c,
            U8OrEof::Eof => {
                // end without problems on EOF
                tokens.push(self.create_zero_byte_token(TokenKind::EndOfFile));
                return Ok(tokens);
            }
        };

        let state = match CharClass::from(c) {
            // whitespace, just continue lexing
            CharClass::Tab | CharClass::Space | CharClass::LineBreak => LexerState::Normal,

            // parentheses are tokens of their own
            CharClass::ParenOpen => {
                let token = self.create_single_byte_token(TokenKind::ParenOpen);
                tokens.push(token);
                LexerState::Normal
            }
            CharClass::ParenClose => {
                let token = self.create_single_byte_token(TokenKind::ParenClose);
                tokens.push(token);
                LexerState::Normal
            }

            // semicolon starts a comment
            CharClass::Semicolon => LexerState::Comment,

            CharClass::Digit => {
                // digit starts a numeral or a decimal
                // and determines the first digit value
                self.start_token();
                LexerState::NumeralOrDecimal(String8::from_byte(c))
            }

            CharClass::Hash => {
                // hash starts a hexadecimal or a binary
                self.start_token();
                LexerState::HexadecimalOrBinary
            }

            CharClass::DoubleQuote => {
                // double quote starts a string literal
                self.start_token();
                LexerState::StringLiteral(String8::new())
            }

            CharClass::Colon => {
                // colon starts a keyword, which continues with a simple symbol string
                self.start_token();
                LexerState::Keyword(String8::new())
            }

            CharClass::Letter | CharClass::Special | CharClass::Dot => {
                // starts a simple symbol or a reserved word
                // the reserved words will be handled after the name is fully known
                self.start_token();
                LexerState::SimpleSymbol(String8::from_byte(c))
            }

            CharClass::Pipe => {
                //  pipe starts a quoted symbol
                self.start_token();
                LexerState::QuotedSymbol(String8::new())
            }

            _ => {
                // class disallowed here
                return Err(LexerError::UnexpectedCharacter);
            }
        };
        self.state = state;
        Ok(tokens)
    }

    fn lex_char(&mut self, c: U8OrEof) -> Result<Vec<Token>, LexerError> {
        let mut state = LexerState::Normal;
        std::mem::swap(&mut self.state, &mut state);
        let mut tokens = Vec::new();
        let state = match state {
            LexerState::Normal => return self.lex_normal(tokens, c),
            LexerState::Fraction {
                whole_part,
                mut fractional_part,
            } => {
                match char_class_opt(c) {
                    Some((CharClass::Digit, c)) => {
                        // add one digit to the fractional part
                        fractional_part.push(c);

                        LexerState::Fraction {
                            whole_part,
                            fractional_part,
                        }
                    }
                    _ => {
                        if fractional_part.is_empty() {
                            // decimals of the form 7. without any digit in fractional part are disallowed
                            return Err(LexerError::FractionDigitExpected);
                        }
                        // push new token and lex the character normally
                        let kind = TokenKind::Decimal(SmtDecimal {
                            whole_part: SmtNumeral::new_unchecked(whole_part),
                            fractional_part: SmtDigits::new_unchecked(fractional_part),
                        });
                        tokens.push(self.create_token_ending_before(kind));
                        return self.lex_normal(tokens, c);
                    }
                }
            }
            LexerState::NumeralOrDecimal(mut value) => {
                match char_class_opt(c) {
                    Some((CharClass::Digit, c)) => {
                        // check that we are not in a leading zero condition
                        // this could not have been done when starting the numeral/decimal
                        // since just a single '0' is allowed
                        if value.as_slice() == b"0" {
                            return Err(LexerError::NumeralLeadingZero);
                        }

                        // add one digit
                        value.push(c);
                        LexerState::NumeralOrDecimal(value)
                    }

                    Some((CharClass::Dot, _)) => {
                        // decimal, the next character will start fraction
                        LexerState::Fraction {
                            whole_part: value,
                            fractional_part: String8::new(),
                        }
                    }

                    _ => {
                        // this was a numeral
                        // push new token and lex the character normally
                        let kind = TokenKind::Numeral(SmtNumeral::new_unchecked(value));
                        tokens.push(self.create_token_ending_before(kind));
                        return self.lex_normal(tokens, c);
                    }
                }
            }
            LexerState::Hexadecimal(mut whole) => {
                let hex_digit = if let U8OrEof::U8(c) = c {
                    match c {
                        b'0'..=b'9' | b'a'..=b'f' | b'A'..=b'F' => Some(c),
                        _ => None,
                    }
                } else {
                    None
                };

                if let Some(hex_digit) = hex_digit {
                    // add hexadecimal digit
                    whole.push(hex_digit);
                    LexerState::Hexadecimal(whole)
                } else {
                    if whole.is_empty() {
                        // had non-digit, zero digits disallowed
                        return Err(LexerError::HexadecimalDigitExpected);
                    }
                    // had non-digit, nonzero digits
                    // push new token and lex the character normally
                    let kind = TokenKind::Hexadecimal(SmtHexDigits::new_unchecked(whole));
                    tokens.push(self.create_token_ending_before(kind));
                    return self.lex_normal(tokens, c);
                }
            }
            LexerState::Binary(mut whole) => {
                let binary_digit = if let U8OrEof::U8(c) = c {
                    match c {
                        b'0' | b'1' => Some(c),
                        _ => None,
                    }
                } else {
                    None
                };

                if let Some(binary_digit) = binary_digit {
                    // add binary digit
                    whole.push(binary_digit);
                    LexerState::Binary(whole)
                } else {
                    if whole.is_empty() {
                        // had non-digit, zero digits disallowed
                        return Err(LexerError::BinaryDigitExpected);
                    }
                    // had non-digit, nonzero digits
                    // push new token and lex the character normally
                    let kind = TokenKind::Binary(SmtBinDigits::new_unchecked(whole));
                    tokens.push(self.create_token_ending_before(kind));
                    return self.lex_normal(tokens, c);
                }
            }

            LexerState::HexadecimalOrBinary => match c {
                U8OrEof::U8(b'x') => LexerState::Hexadecimal(String8::new()),
                U8OrEof::U8(b'b') => LexerState::Binary(String8::new()),
                _ => return Err(LexerError::BaseSelectionExpected),
            },
            LexerState::StringLiteral(mut literal) => {
                match c {
                    U8OrEof::Eof => {
                        // forbidden as the literal must be totally enclosed by double quotes
                        return Err(LexerError::UnclosedStringLiteral);
                    }
                    U8OrEof::U8(b'\"') => {
                        // we have a double quote in string literal
                        // it may be followed by another double quote for escaping
                        // otherwise, it will end the string literal
                        // put the lexer in a special state to handle the next character
                        LexerState::StringLiteralDoubleQuote(literal)
                    }
                    U8OrEof::U8(c) => {
                        if CharClass::from(c).is_printable_or_whitespace() {
                            // add to literal
                            literal.push(c);
                            LexerState::StringLiteral(literal)
                        } else {
                            // forbidden as not printable or whitespace
                            return Err(LexerError::ForbiddenCharInString);
                        }
                    }
                }
            }
            LexerState::StringLiteralDoubleQuote(mut literal) => {
                match c {
                    U8OrEof::U8(b'\"') => {
                        // this has been a double-quote escape
                        // push a double-quote and continue lexing the string literal
                        literal.push(b'\"');
                        LexerState::StringLiteral(literal)
                    }
                    _ => {
                        // literal has ended by the previous character
                        // push new token and lex the character normally
                        let kind = TokenKind::String(SmtStringContent::new_unchecked(literal));
                        tokens.push(self.create_token_ending_before(kind));
                        return self.lex_normal(tokens, c);
                    }
                }
            }
            LexerState::SimpleSymbol(mut symbol) => {
                if let Some((class, c)) = char_class_opt(c)
                    && class.is_allowed_in_simple_symbol()
                {
                    // add character
                    symbol.push(c);
                    LexerState::SimpleSymbol(symbol)
                } else {
                    // simple symbol ended with previous character
                    // process reserved words
                    let kind = if let Some(reserved) = Reserved::from_symbol_opt(&symbol) {
                        TokenKind::Reserved(reserved)
                    } else {
                        TokenKind::Symbol(SmtSymbol::new_unchecked(symbol))
                    };

                    // push new token and lex the character normally
                    tokens.push(self.create_token_ending_before(kind));
                    return self.lex_normal(tokens, c);
                }
            }
            LexerState::Keyword(mut keyword) => match char_class_opt(c) {
                Some((
                    CharClass::Letter | CharClass::Digit | CharClass::Special | CharClass::Dot,
                    c,
                )) => {
                    // add character
                    keyword.push(c);
                    LexerState::Keyword(keyword)
                }
                _ => {
                    // simple symbol ended with previous character
                    if keyword.is_empty() {
                        return Err(LexerError::KeywordNameExpected);
                    }

                    // reserved words as keywords are prohibited
                    if Reserved::from_symbol_opt(&keyword).is_some() {
                        return Err(LexerError::KeywordReserved);
                    }

                    // push new token and lex the character normally
                    let kind = TokenKind::Keyword(SmtKeyword::new_unchecked(keyword));
                    tokens.push(self.create_token_ending_before(kind));
                    return self.lex_normal(tokens, c);
                }
            },
            LexerState::QuotedSymbol(mut symbol) => {
                match c {
                    U8OrEof::U8(b'\\') => {
                        // backslash forbidden in quoted symbols
                        return Err(LexerError::BackslashInQuotedSymbol);
                    }
                    U8OrEof::U8(b'|') => {
                        // end of quoted symbol, push its token, continue normally with next character

                        let kind = TokenKind::Symbol(SmtSymbol::new_unchecked(symbol));
                        tokens.push(self.create_token_ending_now(kind));
                        LexerState::Normal
                    }
                    U8OrEof::U8(c) => {
                        if CharClass::from(c).is_printable_or_whitespace() {
                            // add the character to the quoted symbol and continue it
                            symbol.push(c);
                            LexerState::QuotedSymbol(symbol)
                        } else {
                            // character forbidden as not printable or whitespace

                            return Err(LexerError::ForbiddenCharInQuotedSymbol);
                        }
                    }

                    U8OrEof::Eof => {
                        // EOF forbidden as the symbol must be totally enclosed by pipes
                        return Err(LexerError::UnclosedQuotedSymbol);
                    }
                }
            }
            LexerState::Comment => {
                match char_class_opt(c) {
                    Some((CharClass::LineBreak, _)) => {
                        // end comment, ready for next token
                        LexerState::Normal
                    }
                    Some(_) => {
                        // continue comment
                        LexerState::Comment
                    }
                    None => {
                        // end without problems on EOF
                        let token = self.create_zero_byte_token(TokenKind::EndOfFile);
                        tokens.push(token);
                        return Ok(tokens);
                    }
                }
            }
        };
        self.state = state;
        Ok(tokens)
    }

    fn start_token(&mut self) {
        self.token_start = self.offset;
    }

    fn create_token_ending_now(&self, kind: TokenKind) -> Token {
        // The current offset is at the start of the current character
        // The span includes start, but not the end
        // Therefore, we need to add 1 to the current offset
        Token::new(
            kind,
            SmtSpan::new_unchecked(self.token_start, self.offset + 1),
        )
    }

    fn create_token_ending_before(&self, kind: TokenKind) -> Token {
        // The current offset is at the start of the current character
        // The span includes start, but not the end
        // Therefore, if the token actually ended with the previous character,
        // we do not need to add anything.
        Token::new(kind, SmtSpan::new_unchecked(self.token_start, self.offset))
    }

    fn create_single_byte_token(&mut self, kind: TokenKind) -> Token {
        self.start_token();
        self.create_token_ending_now(kind)
    }
    fn create_zero_byte_token(&mut self, kind: TokenKind) -> Token {
        self.start_token();
        self.create_token_ending_before(kind)
    }
}

impl Default for Lexer {
    fn default() -> Self {
        Self::new()
    }
}

use std::io;

use num::{BigUint, One, Zero};

use crate::{
    parser::char_class::{CharClass, U8OrEof, char_class_opt},
    smt::{Decimal, Reserved, String8, Whole},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    ParenOpen,
    ParenClose,
    Numeral(Whole),
    Decimal(Decimal),
    Hexadecimal(Whole),
    Binary(Whole),
    Symbol(String8),
    Reserved(Reserved),
    String(String8),
    Keyword(String8),
    End,
}

pub enum LexerState {
    Normal,
    Fraction(Decimal),
    NumeralOrDecimal(Whole),
    Hexadecimal(Whole),
    Binary(Whole),
    HexadecimalOrBinary,
    StringLiteral(String8),
    StringLiteralDoubleQuote(String8),
    SimpleSymbol(String8),
    Keyword(String8),
    QuotedSymbol(String8),
    Comment,
}

pub struct Lexer {
    pub state: LexerState,
}

#[allow(dead_code)]
#[derive(Debug)]
pub enum LexerError {
    ReadError(io::Error),
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
}

impl Lexer {
    pub fn new() -> Self {
        Lexer {
            state: LexerState::Normal,
        }
    }

    pub fn lex_next(&mut self, c: u8) -> Result<Vec<Token>, LexerError> {
        self.lex_char(U8OrEof::U8(c))
    }

    pub fn lex_eof(&mut self) -> Result<Vec<Token>, LexerError> {
        self.lex_char(U8OrEof::Eof)
    }

    fn lex_normal(&mut self, mut tokens: Vec<Token>, c: U8OrEof) -> Result<Vec<Token>, LexerError> {
        let c = match c {
            U8OrEof::U8(c) => c,
            U8OrEof::Eof => {
                // end without problems on EOF
                tokens.push(Token::End);
                return Ok(tokens);
            }
        };

        let state = match CharClass::from(c) {
            // whitespace, just continue lexing
            CharClass::Tab | CharClass::Space | CharClass::LineBreak => LexerState::Normal,

            // parentheses are tokens of their own
            CharClass::ParenOpen => {
                tokens.push(Token::ParenOpen);
                LexerState::Normal
            }
            CharClass::ParenClose => {
                tokens.push(Token::ParenClose);
                LexerState::Normal
            }

            // semicolon starts a comment
            CharClass::Semicolon => LexerState::Comment,

            CharClass::Digit => {
                // digit starts a numeral or a decimal
                // and determines the first digit value
                let digit = c - b'0';
                LexerState::NumeralOrDecimal(Whole {
                    value: digit.into(),
                    num_digits: BigUint::one(),
                })
            }

            CharClass::Hash => {
                // hash starts a hexadecimal or a binary
                LexerState::HexadecimalOrBinary
            }

            CharClass::DoubleQuote => {
                // double quote starts a string literal
                LexerState::StringLiteral(String8(Vec::new()))
            }

            CharClass::Colon => {
                // colon starts a keyword, which continues with a simple symbol string
                LexerState::Keyword(String8(Vec::new()))
            }

            CharClass::Letter | CharClass::Special | CharClass::Dot => {
                // starts a simple symbol or a reserved word
                // the reserved words will be handled after the name is fully known
                LexerState::SimpleSymbol(String8(vec![c]))
            }

            CharClass::Pipe => {
                // quoted symbol
                LexerState::QuotedSymbol(String8(Vec::new()))
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
            LexerState::Fraction(mut fraction) => {
                match char_class_opt(c) {
                    Some((CharClass::Digit, c)) => {
                        // compute the new value, add one denominator digit
                        let digit = c - b'0';
                        fraction.value *= 10u32;
                        fraction.value += digit;
                        fraction.num_denominator_digits += BigUint::one();
                        LexerState::Fraction(fraction)
                    }
                    _ => {
                        if fraction.num_denominator_digits.is_zero() {
                            // decimals of the form 7. without any digit in fraction part are disallowed
                            return Err(LexerError::FractionDigitExpected);
                        }
                        // push new token and lex the character normally
                        tokens.push(Token::Decimal(fraction));
                        return self.lex_normal(tokens, c);
                    }
                }
            }
            LexerState::NumeralOrDecimal(mut whole) => {
                match char_class_opt(c) {
                    Some((CharClass::Digit, c)) => {
                        // compute the new value, add one digit
                        let digit = c - b'0';
                        whole.value *= 10u32;
                        whole.value += digit;
                        whole.num_digits += 1u32;
                        LexerState::NumeralOrDecimal(whole)
                    }

                    Some((CharClass::Dot, _)) => {
                        // decimal, the next character will start fraction
                        LexerState::Fraction(Decimal {
                            value: whole.value,
                            num_numerator_digits: whole.num_digits,
                            num_denominator_digits: BigUint::zero(),
                        })
                    }

                    _ => {
                        // this was a numeral
                        // push new token and lex the character normally
                        tokens.push(Token::Numeral(whole));
                        return self.lex_normal(tokens, c);
                    }
                }
            }
            LexerState::Hexadecimal(mut whole) => {
                let digit = if let U8OrEof::U8(c) = c {
                    match c {
                        b'0'..=b'9' => Some(c - b'0'),
                        b'a'..=b'f' => Some((c - b'a') + 10),
                        b'A'..=b'F' => Some((c - b'A') + 10),
                        _ => None,
                    }
                } else {
                    None
                };

                if let Some(digit) = digit {
                    // hexadecimal digit, multiply value by 16 and add it, increment num digits
                    whole.value *= 16u32;
                    whole.value += digit;
                    whole.num_digits += 1u32;
                    LexerState::Hexadecimal(whole)
                } else {
                    if whole.num_digits.is_zero() {
                        // had non-digit, zero digits disallowed
                        return Err(LexerError::HexadecimalDigitExpected);
                    }
                    // had non-digit, nonzero digits
                    // push new token and lex the character normally
                    tokens.push(Token::Hexadecimal(whole));
                    return self.lex_normal(tokens, c);
                }
            }
            LexerState::Binary(mut whole) => {
                if let U8OrEof::U8(c) = c
                    && matches!(c, b'0'..=b'1')
                {
                    // binary digit, multiply value by 2 and add it, increment num digits
                    let digit = c - b'0';
                    whole.value *= 2u32;
                    whole.value += digit;
                    whole.num_digits += 1u32;
                    LexerState::Binary(whole)
                } else {
                    if whole.num_digits.is_zero() {
                        // had non-digit, zero digits disallowed
                        return Err(LexerError::BinaryDigitExpected);
                    }
                    // had non-digit, nonzero digits
                    // push new token and lex the character normally
                    tokens.push(Token::Binary(whole));
                    return self.lex_normal(tokens, c);
                }
            }

            LexerState::HexadecimalOrBinary => {
                let empty_whole = Whole {
                    value: BigUint::zero(),
                    num_digits: BigUint::zero(),
                };
                match c {
                    U8OrEof::U8(b'x') => LexerState::Hexadecimal(empty_whole),
                    U8OrEof::U8(b'b') => LexerState::Binary(empty_whole),
                    _ => return Err(LexerError::BaseSelectionExpected),
                }
            }
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
                            literal.0.push(c);
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
                        literal.0.push(b'\"');
                        LexerState::StringLiteral(literal)
                    }
                    _ => {
                        // literal has ended by the previous character
                        // push new token and lex the character normally
                        tokens.push(Token::String(literal));
                        return self.lex_normal(tokens, c);
                    }
                }
            }
            LexerState::SimpleSymbol(mut symbol) => {
                match char_class_opt(c) {
                    Some((
                        CharClass::Letter | CharClass::Digit | CharClass::Special | CharClass::Dot,
                        c,
                    )) => {
                        // add character
                        symbol.0.push(c);
                        LexerState::SimpleSymbol(symbol)
                    }
                    _ => {
                        // simple symbol ended with previous character
                        // process reserved words
                        let token = if let Some(reserved) = Reserved::from_symbol_opt(&symbol) {
                            Token::Reserved(reserved)
                        } else {
                            Token::Symbol(symbol)
                        };

                        // push new token and lex the character normally
                        tokens.push(token);
                        return self.lex_normal(tokens, c);
                    }
                }
            }
            LexerState::Keyword(mut keyword) => match char_class_opt(c) {
                Some((
                    CharClass::Letter | CharClass::Digit | CharClass::Special | CharClass::Dot,
                    c,
                )) => {
                    // add character
                    keyword.0.push(c);
                    LexerState::Keyword(keyword)
                }
                _ => {
                    // simple symbol ended with previous character
                    if keyword.0.is_empty() {
                        return Err(LexerError::KeywordNameExpected);
                    }

                    // reserved words as keywords are prohibited
                    if Reserved::from_symbol_opt(&keyword).is_some() {
                        return Err(LexerError::KeywordReserved);
                    }

                    // push new token and lex the character normally
                    tokens.push(Token::Keyword(keyword));
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
                        tokens.push(Token::Symbol(symbol));
                        LexerState::Normal
                    }
                    U8OrEof::U8(c) => {
                        if CharClass::from(c).is_printable_or_whitespace() {
                            // add the character to the quoted symbol and continue it
                            symbol.0.push(c);
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
                    _ => {
                        // continue comment, no problem ending file on a comment
                        LexerState::Comment
                    }
                }
            }
        };
        self.state = state;
        Ok(tokens)
    }
}

impl Default for Lexer {
    fn default() -> Self {
        Self::new()
    }
}

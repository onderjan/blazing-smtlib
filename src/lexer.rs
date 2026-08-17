use std::io;

mod char_class;

use char_class::{CharClass, U8OrEof, char_class_opt};

use crate::{
    String8,
    token::{Reserved, Token},
};

pub enum LexerState {
    Normal,
    Fraction {
        numerator: String8,
        denominator: String8,
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
                LexerState::NumeralOrDecimal(String8(vec![c]))
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
            LexerState::Fraction {
                numerator,
                mut denominator,
            } => {
                match char_class_opt(c) {
                    Some((CharClass::Digit, c)) => {
                        // add one denominator digit
                        denominator.0.push(c);

                        LexerState::Fraction {
                            numerator,
                            denominator,
                        }
                    }
                    _ => {
                        if denominator.is_empty() {
                            // decimals of the form 7. without any digit in fraction part are disallowed
                            return Err(LexerError::FractionDigitExpected);
                        }
                        // push new token and lex the character normally
                        tokens.push(Token::Decimal {
                            numerator,
                            denominator,
                        });
                        return self.lex_normal(tokens, c);
                    }
                }
            }
            LexerState::NumeralOrDecimal(mut value) => {
                match char_class_opt(c) {
                    Some((CharClass::Digit, c)) => {
                        // add one digit
                        value.0.push(c);
                        LexerState::NumeralOrDecimal(value)
                    }

                    Some((CharClass::Dot, _)) => {
                        // decimal, the next character will start fraction
                        LexerState::Fraction {
                            numerator: value,
                            denominator: String8::new(),
                        }
                    }

                    _ => {
                        // this was a numeral
                        // push new token and lex the character normally
                        tokens.push(Token::Numeral(value));
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
                    whole.0.push(hex_digit);
                    LexerState::Hexadecimal(whole)
                } else {
                    if whole.is_empty() {
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
                    whole.0.push(binary_digit);
                    LexerState::Binary(whole)
                } else {
                    if whole.is_empty() {
                        // had non-digit, zero digits disallowed
                        return Err(LexerError::BinaryDigitExpected);
                    }
                    // had non-digit, nonzero digits
                    // push new token and lex the character normally
                    tokens.push(Token::Binary(whole));
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

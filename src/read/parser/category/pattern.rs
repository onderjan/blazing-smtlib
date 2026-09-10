use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtPattern, SmtSimplePattern,
    read::parser::{
        ClosedMultipleParser, PairParser, ParserError, SymbolParser,
        category::{CategoryErrorKind, CategoryParser},
    },
    token::{Reserved, Token, TokenKind, TokenType},
};

pub struct SimplePatternParser;

impl SimplePatternParser {
    pub fn new() -> Self {
        Self
    }
}

impl Default for SimplePatternParser {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for SimplePatternParser {
    type Result = SmtSimplePattern;

    fn progress(
        &mut self,
        _handler: &mut H,
        token: &Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        let result = match token.kind() {
            TokenKind::Symbol(symbol) => SmtSimplePattern::Symbol(symbol.into_owned()),
            TokenKind::Reserved(Reserved::Underscore) => SmtSimplePattern::Wildcard,
            _ => {
                return Err(ParserError::category_error(
                    CategoryErrorKind::ExpectedToken(&[
                        TokenType::Symbol,
                        TokenType::Reserved(Reserved::Underscore),
                    ]),
                    token.span(),
                ));
            }
        };
        Ok(ControlFlow::Break(result))
    }
}

/// A parser that reads an SMT-LIB match pattern.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct PatternParser<H: SmtHandler> {
    is_constructor: bool,
    constructor_parser: PairParser<H, SymbolParser, ClosedMultipleParser<H, SimplePatternParser>>,
}

impl<H: SmtHandler> PatternParser<H> {
    pub fn new() -> Self {
        Self {
            is_constructor: false,
            constructor_parser: PairParser::new(),
        }
    }
}

impl<H: SmtHandler> Default for PatternParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for PatternParser<H> {
    type Result = SmtPattern;

    fn restart(&mut self) {
        self.is_constructor = false;
        self.constructor_parser.restart();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: &Token,
    ) -> Result<ControlFlow<SmtPattern, ()>, ParserError<H::Error>> {
        let span = token.span();
        if !self.is_constructor {
            // expecting either a symbol, an underscore, or an opening parenthesis starting a constructor
            let result = match token.kind() {
                TokenKind::Symbol(symbol) => SmtSimplePattern::Symbol(symbol.into_owned()),
                TokenKind::Reserved(Reserved::Underscore) => SmtSimplePattern::Wildcard,
                TokenKind::ParenOpen => {
                    // move to constructor parsing
                    self.is_constructor = true;
                    return Ok(ControlFlow::Continue(()));
                }
                _ => {
                    return Err(ParserError::category_error(
                        CategoryErrorKind::ExpectedToken(&[
                            TokenType::Symbol,
                            TokenType::Reserved(Reserved::Underscore),
                            TokenType::ParenOpen,
                        ]),
                        token.span(),
                    ));
                }
            };
            // this was just a simple pattern
            // no need to reset as we are in the initial state
            return Ok(ControlFlow::Break(SmtPattern::Simple(result)));
        }

        if let ControlFlow::Break((constructor, args)) =
            self.constructor_parser.progress(handler, token)?
        {
            // there must be at least one argument to the constructor
            if args.is_empty() {
                return Err(ParserError::category_error(
                    CategoryErrorKind::EmptyPatternArguments,
                    span,
                ));
            }

            // construct the result
            let result = SmtPattern::Application { constructor, args };
            // reset and return the result
            self.is_constructor = false;
            return Ok(ControlFlow::Break(result));
        }

        // continue parsing
        Ok(ControlFlow::Continue(()))
    }
}

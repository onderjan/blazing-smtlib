use std::ops::ControlFlow;

use crate::{
    SmtApplication, SmtHandler, SmtIdent, SmtQualifiedIdent, SmtSpecialConstant, SmtSymbol,
    SmtTerm,
    parser::{
        ParserError, ParserOrHandlerError,
        category::{CategoryParser, ident::IdentParser},
    },
    token::{Reserved, Token, TokenKind},
};

pub enum TermLevel<H: SmtHandler> {
    Application(SmtQualifiedIdent, Vec<H::Term>),
    LetBinding(Vec<(SmtSymbol, H::Term)>, SmtSymbol),
    LetInner,
}

pub enum TermParserState<H: SmtHandler> {
    Start,
    Open,
    IndexedIdent(IdentParser),
    ApplicationIdent(IdentParser),
    ApplicationTerm(SmtQualifiedIdent, Vec<H::Term>),
    LetBeforeBindingsOpen,
    LetBeforeBindingOpen(Vec<(SmtSymbol, H::Term)>),
    LetBeforeBindingSymbol(Vec<(SmtSymbol, H::Term)>),
    LetBeforeBindingClose(Vec<(SmtSymbol, H::Term)>),
    LetAfterInnerTerm(H::Term),
}

pub struct TermParser<H: SmtHandler> {
    state: TermParserState<H>,
    levels: Vec<TermLevel<H>>,
}

impl<H: SmtHandler> CategoryParser<H> for TermParser<H> {
    type Result = H::Term;

    fn init() -> Self {
        TermParser {
            state: TermParserState::Start,
            levels: Vec::new(),
        }
    }

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Term, Self>, ParserOrHandlerError<H>> {
        let (mut levels, term) = match self.progress_last_level(handler, token)? {
            ControlFlow::Continue(parser) => return Ok(ControlFlow::Continue(parser)),
            ControlFlow::Break((levels, term)) => (levels, term),
        };
        let Some(last_level) = levels.pop() else {
            // this is the root term level, we are done
            return Ok(ControlFlow::Break(term));
        };

        // we need to progress the last level
        let state = match last_level {
            TermLevel::Application(function, mut args) => {
                // add argument and go back to term state
                args.push(term);
                TermParserState::ApplicationTerm(function, args)
            }
            TermLevel::LetBinding(mut bindings, binding_name) => {
                // add binding, should be followed by parenthesis closing the bindings
                bindings.push((binding_name, term));
                TermParserState::LetBeforeBindingClose(bindings)
            }
            TermLevel::LetInner => {
                // end let, should be followed by closing parenthesis
                let term = handler
                    .end_let(term)
                    .map_err(ParserOrHandlerError::HandlerError)?;
                TermParserState::LetAfterInnerTerm(term)
            }
        };

        Ok(ControlFlow::Continue(Self { state, levels }))
    }
}

type TermProgressOk<H, P> = ControlFlow<(Vec<TermLevel<H>>, <H as SmtHandler>::Term), P>;

impl<H: SmtHandler> TermParser<H> {
    fn progress_last_level(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<TermProgressOk<H, Self>, ParserOrHandlerError<H>> {
        let mut levels = self.levels;
        let state = match self.state {
            TermParserState::Start => return Self::parse_term_start(levels, handler, token),
            TermParserState::Open => {
                return Ok(ControlFlow::Continue(Self::parse_term_open(levels, token)?));
            }
            TermParserState::IndexedIdent(parser) => {
                match parser.progress(handler, token)? {
                    ControlFlow::Continue(parser) => TermParserState::IndexedIdent(parser),
                    ControlFlow::Break(ident) => {
                        // TODO: actual qualified ident
                        let term = SmtTerm::QualifiedIdent(SmtQualifiedIdent::Ident(ident));
                        let term = handler
                            .handle_term(term)
                            .map_err(ParserOrHandlerError::HandlerError)?;
                        return Ok(ControlFlow::Break((levels, term)));
                    }
                }
            }
            TermParserState::ApplicationIdent(parser) => {
                match parser.progress(handler, token)? {
                    ControlFlow::Continue(parser) => TermParserState::ApplicationIdent(parser),
                    ControlFlow::Break(ident) => {
                        // TODO: actual qualified ident
                        let ident = SmtQualifiedIdent::Ident(ident);
                        TermParserState::ApplicationTerm(ident, Vec::new())
                    }
                }
            }
            TermParserState::ApplicationTerm(function, args) => {
                if matches!(token.kind(), TokenKind::ParenClose) {
                    // this ends the application term
                    let term = SmtTerm::Application(SmtApplication { function, args });
                    let term = handler
                        .handle_term(term)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    return Ok(ControlFlow::Break((levels, term)));
                } else {
                    // add the application to the level stack and parse the argument
                    levels.push(TermLevel::Application(function, args));
                    return Self::parse_term_start(levels, handler, token);
                }
            }
            TermParserState::LetBeforeBindingsOpen => {
                expect_open_paren(token)?;
                TermParserState::LetBeforeBindingOpen(Vec::new())
            }
            TermParserState::LetBeforeBindingOpen(bindings) => {
                match token.kind() {
                    TokenKind::ParenOpen => {
                        // new binding
                        TermParserState::LetBeforeBindingSymbol(bindings)
                    }
                    TokenKind::ParenClose => {
                        // bindings are closed, inner term will be next
                        // check that there is at least one binding
                        if bindings.is_empty() {
                            return Err(ParserError::EmptyLetBindings.into());
                        }

                        handler
                            .start_let(bindings)
                            .map_err(ParserOrHandlerError::HandlerError)?;

                        levels.push(TermLevel::LetInner);
                        TermParserState::Start
                    }
                    _ => return Err(ParserError::ExpectedOpenOrCloseParen.into()),
                }
            }
            TermParserState::LetBeforeBindingSymbol(bindings) => {
                let symbol = expect_symbol(token)?;
                levels.push(TermLevel::LetBinding(bindings, symbol));
                TermParserState::Start
            }
            TermParserState::LetBeforeBindingClose(bindings) => {
                expect_close_paren(token)?;
                TermParserState::LetBeforeBindingOpen(bindings)
            }
            TermParserState::LetAfterInnerTerm(term) => {
                expect_close_paren(token)?;
                return Ok(ControlFlow::Break((levels, term)));
            }
        };
        Ok(ControlFlow::Continue(Self { state, levels }))
    }

    fn parse_term_start(
        levels: Vec<TermLevel<H>>,
        handler: &mut H,
        token: Token,
    ) -> Result<TermProgressOk<H, Self>, ParserOrHandlerError<H>> {
        let span = token.span();
        match token.into_kind() {
            TokenKind::ParenOpen => {
                // application, binder, or annotation
                // move to operator parsing
                Ok(ControlFlow::Continue(Self {
                    state: TermParserState::Open,
                    levels,
                }))
            }
            TokenKind::Symbol(symbol) => {
                // a qualified identifier that is just a symbol
                let qualified_ident = SmtQualifiedIdent::Ident(SmtIdent {
                    name: symbol,
                    indices: Vec::new(),
                });
                let term = handler
                    .handle_term(SmtTerm::QualifiedIdent(qualified_ident))
                    .map_err(ParserOrHandlerError::HandlerError)?;

                Ok(ControlFlow::Break((levels, term)))
            }

            kind => {
                // handle special constants
                match parse_special_constant(Token::new(kind, span)) {
                    Ok(special_constant) => {
                        let term = handler
                            .handle_term(SmtTerm::SpecialConstant(special_constant))
                            .map_err(ParserOrHandlerError::HandlerError)?;
                        Ok(ControlFlow::Break((levels, term)))
                    }
                    Err(_token) => Err(ParserError::ExpectedTerm.into()),
                }
            }
        }
    }

    fn parse_term_open(
        levels: Vec<TermLevel<H>>,
        token: Token,
    ) -> Result<Self, ParserOrHandlerError<H>> {
        let state = match token.into_kind() {
            TokenKind::Symbol(fn_name) => {
                // this is an application where the function identifier is just a symbol
                let fn_ident = SmtQualifiedIdent::Ident(SmtIdent {
                    name: fn_name,
                    indices: Vec::new(),
                });
                TermParserState::ApplicationTerm(fn_ident, Vec::new())
            }
            TokenKind::Reserved(Reserved::Let) => TermParserState::LetBeforeBindingsOpen,
            TokenKind::Reserved(Reserved::Lambda) => todo!("Lambda"),
            TokenKind::Reserved(Reserved::Forall) => todo!("Forall"),
            TokenKind::Reserved(Reserved::Exists) => todo!("Exists"),
            TokenKind::Reserved(Reserved::Match) => todo!("Match"),
            TokenKind::Reserved(Reserved::ExclamationMark) => todo!("Annotation"),
            TokenKind::Reserved(Reserved::Underscore) => {
                // this is actually a term composed of an indexed identifier
                // start an indexed ident parser after the undescore
                let parser = IdentParser::after_underscore();
                TermParserState::IndexedIdent(parser)
            }
            TokenKind::ParenOpen => {
                // this is an application where the function identifier is qualified or indexed
                // start a qualified ident parser after the parenthesis open
                let parser = IdentParser::after_open_paren();
                TermParserState::ApplicationIdent(parser)
            }
            _ => return Err(ParserError::ExpectedOperator.into()),
        };
        Ok(Self { state, levels })
    }
}

fn parse_special_constant(token: Token) -> Result<SmtSpecialConstant, Token> {
    let span = token.span();
    let constant = match token.into_kind() {
        TokenKind::Numeral(value) => SmtSpecialConstant::Numeral(value),
        TokenKind::Decimal(decimal) => SmtSpecialConstant::Decimal(decimal),
        TokenKind::Hexadecimal(value) => SmtSpecialConstant::Hexadecimal(value),
        TokenKind::Binary(value) => SmtSpecialConstant::Binary(value),
        TokenKind::String(string) => SmtSpecialConstant::String(string),
        kind => return Err(Token::new(kind, span)),
    };
    Ok(constant)
}

fn expect_open_paren<H: SmtHandler>(token: Token) -> Result<(), ParserOrHandlerError<H>> {
    if matches!(token.kind(), TokenKind::ParenOpen) {
        Ok(())
    } else {
        Err(ParserError::ExpectedToken(TokenKind::ParenOpen).into())
    }
}

fn expect_close_paren<H: SmtHandler>(token: Token) -> Result<(), ParserOrHandlerError<H>> {
    if matches!(token.kind(), TokenKind::ParenClose) {
        Ok(())
    } else {
        Err(ParserError::ExpectedToken(TokenKind::ParenClose).into())
    }
}

fn expect_symbol<H: SmtHandler>(token: Token) -> Result<SmtSymbol, ParserOrHandlerError<H>> {
    if let TokenKind::Symbol(symbol) = token.into_kind() {
        Ok(symbol)
    } else {
        Err(ParserError::ExpectedSymbol.into())
    }
}

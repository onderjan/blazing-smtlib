use std::ops::ControlFlow;

use crate::{
    SmtApplication, SmtHandler, SmtIdent, SmtQualifiedIdent, SmtTerm,
    parser::{
        ParserError, ParserOrHandlerError,
        category::{
            CategoryParser, EnclosedPairParser, MultipleParser, SymbolParser, ident::IdentParser,
        },
    },
    token::{Reserved, Token},
};

pub enum TermLevel<H: SmtHandler> {
    ApplicationIdent(IdentParser),
    Application(SmtIdent, MultipleParser<H, TermParser<H>>),
    LetBindings(MultipleParser<H, EnclosedPairParser<H, SymbolParser, TermParser<H>>>),
    LetBound(TermParser<H>),
    IndexedIdent(IdentParser),
}

pub enum TermParser<H: SmtHandler> {
    Start,
    Operator,
    Selected(Box<TermLevel<H>>),
}

impl<H: SmtHandler> CategoryParser<H> for TermParser<H> {
    type Result = H::Term;

    fn init() -> Self {
        TermParser::Start
    }

    fn progress(
        mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Term, Self>, ParserOrHandlerError<H>> {
        match self {
            TermParser::Start => {
                // just parse term start
                Ok(self.parse_term_start(handler, token)?)
            }
            TermParser::Operator => {
                // find out what kind of an application-like S-term we have
                let level = match token {
                    Token::Symbol(fn_name) => {
                        // this is an application where the function identifier is just a symbol
                        let fn_ident = SmtIdent {
                            name: fn_name,
                            indices: Vec::new(),
                        };
                        TermLevel::Application(fn_ident, MultipleParser::after_open_paren())
                    }
                    Token::Reserved(Reserved::Let) => {
                        TermLevel::LetBindings(MultipleParser::init())
                    }
                    Token::Reserved(Reserved::Lambda) => todo!("Lambda"),
                    Token::Reserved(Reserved::Forall) => todo!("Forall"),
                    Token::Reserved(Reserved::Exists) => todo!("Exists"),
                    Token::Reserved(Reserved::Match) => todo!("Match"),
                    Token::Reserved(Reserved::ExclamationMark) => todo!("Annotation"),
                    Token::Reserved(Reserved::Underscore) => {
                        // this is actually a term composed of an indexed identifier
                        TermLevel::IndexedIdent(IdentParser::after_underscore())
                    }
                    Token::ParenOpen => {
                        // this is an application where the function identifier is qualified or indexed
                        TermLevel::ApplicationIdent(IdentParser::after_open_paren())
                    }
                    _ => return Err(ParserError::ExpectedOperator.into()),
                };
                Ok(ControlFlow::Continue(Self::Selected(Box::new(level))))
            }
            TermParser::Selected(level) => Self::progress_selected(*level, handler, token),
        }
    }
}

impl<H: SmtHandler> TermParser<H> {
    fn parse_term_start(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Term, Self>, ParserOrHandlerError<H>> {
        match token {
            Token::ParenOpen => {
                // application, binder, or annotation
                // move to operator parsing
                Ok(ControlFlow::Continue(TermParser::Operator))
            }
            Token::Symbol(symbol) => {
                // TODO: support qualified idents instead of just symbols
                let qualified_ident = SmtQualifiedIdent::Ident(SmtIdent {
                    name: symbol,
                    indices: Vec::new(),
                });
                let term = handler
                    .handle_term(SmtTerm::QualifiedIdent(qualified_ident))
                    .map_err(ParserOrHandlerError::HandlerError)?;

                Ok(ControlFlow::Break(term))
            }
            _ => Err(ParserError::ExpectedTerm.into()),
        }
    }

    fn progress_selected(
        level: TermLevel<H>,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Term, Self>, ParserOrHandlerError<H>> {
        let result = match level {
            TermLevel::ApplicationIdent(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => TermLevel::ApplicationIdent(parser),
                ControlFlow::Break(fn_ident) => {
                    TermLevel::Application(fn_ident, MultipleParser::after_open_paren())
                }
            },
            TermLevel::Application(fn_ident, parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => TermLevel::Application(fn_ident, parser),
                ControlFlow::Break(args) => {
                    let term = SmtTerm::Application(SmtApplication {
                        function: SmtQualifiedIdent::Ident(fn_ident),
                        args,
                    });
                    let term = handler
                        .handle_term(term)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    return Ok(ControlFlow::Break(term));
                }
            },
            TermLevel::LetBindings(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => TermLevel::LetBindings(parser),
                ControlFlow::Break(bindings) => {
                    handler
                        .start_let(bindings)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    TermLevel::LetBound(TermParser::init())
                }
            },
            TermLevel::LetBound(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => TermLevel::LetBound(parser),
                ControlFlow::Break(bound_term) => {
                    let term = handler
                        .end_let(bound_term)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    return Ok(ControlFlow::Break(term));
                }
            },
            TermLevel::IndexedIdent(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => TermLevel::IndexedIdent(parser),
                ControlFlow::Break(ident) => {
                    // TODO: qualified identifiers are accepted here
                    let term = SmtTerm::QualifiedIdent(SmtQualifiedIdent::Ident(ident));
                    let term = handler
                        .handle_term(term)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    return Ok(ControlFlow::Break(term));
                }
            },
        };

        Ok(ControlFlow::Continue(Self::Selected(Box::new(result))))
    }
}

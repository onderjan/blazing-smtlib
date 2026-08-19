use std::ops::ControlFlow;

use crate::{
    SmtApplication, SmtHandler, SmtIdent, SmtQualifiedIdent, SmtTerm, String8,
    parser::{
        ParserError, ParserOrHandlerError, ParserState,
        category::{CategoryParser, CategoryParserState},
        command::CommandCallback,
        progress_state,
    },
    token::{Reserved, Token},
};

pub(crate) fn parse_term<H: SmtHandler>(
    handler: &mut H,
    callback: CommandCallback<H, H::Term>,
    token: Token,
) -> Result<ParserState<H>, ParserOrHandlerError<H>> {
    match parse_term_start(handler, token)? {
        ControlFlow::Continue(level) => Ok(ParserState::Term(CategoryParserState::new(
            callback,
            TermParser { stack: vec![level] },
        ))),
        ControlFlow::Break(term) => Ok(progress_state(
            callback(handler, term).map_err(ParserOrHandlerError::HandlerError)?,
        )),
    }
}

fn parse_term_start<H: SmtHandler>(
    handler: &mut H,
    token: Token,
) -> Result<ControlFlow<H::Term, TermLevel<H>>, ParserOrHandlerError<H>> {
    match token {
        Token::ParenOpen => {
            // application, binder, or annotation
            Ok(ControlFlow::Continue(TermLevel::Operator))
        }
        Token::Symbol(symbol) => {
            // TODO: support qualified idents instead of just symbols
            let qualified_ident = SmtQualifiedIdent::Ident(SmtIdent {
                name: symbol.as_str(),
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

enum TermLevel<H: SmtHandler> {
    Operator,
    Application(String8, Vec<H::Term>),
}

pub struct TermParser<H: SmtHandler> {
    stack: Vec<TermLevel<H>>,
}

impl<H: SmtHandler> TermParser<H> {
    fn close_level(
        &mut self,
        handler: &mut H,
        term: SmtTerm<'_, H>,
    ) -> Result<ControlFlow<H::Term, ()>, ParserOrHandlerError<H>> {
        self.stack.pop();
        let term = handler
            .handle_term(term)
            .map_err(ParserOrHandlerError::HandlerError)?;
        if let Some(lower_level) = self.stack.last_mut() {
            match lower_level {
                TermLevel::Operator => panic!("Cannot add terms from last operator"),
                TermLevel::Application(_fn_name, args) => {
                    args.push(term);
                }
            }
            Ok(ControlFlow::Continue(()))
        } else {
            Ok(ControlFlow::Break(term))
        }
    }
}

impl<H: SmtHandler> CategoryParser<H> for TermParser<H> {
    type Category = H::Term;

    fn progress(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Term, ()>, ParserOrHandlerError<H>> {
        let level = self
            .stack
            .last_mut()
            .expect("Processing stack should be non-empty");
        match level {
            TermLevel::Operator => {
                match token {
                    Token::Symbol(fn_name) => {
                        // TODO: functions should be quaified idents
                        *level = TermLevel::Application(fn_name, Vec::new());
                    }

                    Token::Reserved(Reserved::Let) => todo!("Let"),
                    Token::Reserved(Reserved::Lambda) => todo!("Lambda"),
                    Token::Reserved(Reserved::Forall) => todo!("Forall"),
                    Token::Reserved(Reserved::Exists) => todo!("Exists"),
                    Token::Reserved(Reserved::Match) => todo!("Match"),
                    Token::Reserved(Reserved::ExclamationMark) => todo!("Annotation"),
                    _ => return Err(ParserError::ExpectedOperator.into()),
                }
                /*match token {
                Token::Symbol(symbol) => {
                    let _symbol = handler
                        .handle_symbol(symbol.as_str())
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    todo!("Indexed sort");
                }
                Token::Reserved(Reserved::Underscore) => {
                    *self = SortParserState::IndexedIdent(IndexedIdentParserState::AwaitingSymbol);
                    Ok(ControlFlow::Continue(()))
                }
                _ => Err(ParserError::ExpectedSortInner.into()),
                */
            }
            TermLevel::Application(fn_name, arguments) => {
                // if the token is closing parenthesis, close this term
                // otherwise, parse an argument term
                if matches!(token, Token::ParenClose) {
                    let fn_name = std::mem::take(fn_name);
                    let arguments = std::mem::take(arguments);
                    return self.close_level(
                        handler,
                        SmtTerm::Application(SmtApplication {
                            args: arguments,
                            function: SmtQualifiedIdent::Ident(SmtIdent {
                                name: fn_name.as_str(),
                                indices: vec![],
                            }),
                        }),
                    );
                } else {
                    match parse_term_start(handler, token)? {
                        ControlFlow::Continue(level) => {
                            self.stack.push(level);
                        }
                        ControlFlow::Break(term) => {
                            arguments.push(term);
                        }
                    }
                }
            }
        }

        Ok(ControlFlow::Continue(()))
    }
}

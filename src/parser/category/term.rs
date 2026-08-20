use std::ops::ControlFlow;

use crate::{
    SmtApplication, SmtHandler, SmtIdent, SmtQualifiedIdent, SmtTerm, String8,
    parser::{ParserError, ParserOrHandlerError, category::CategoryParser},
    token::{Reserved, Token},
};

enum TermLevel<H: SmtHandler> {
    Application(String8, Vec<H::Term>),
}

enum TermParserState {
    Start,
    Operator,
    Term,
}

pub struct TermParser<H: SmtHandler> {
    state: TermParserState,
    stack: Vec<TermLevel<H>>,
}

impl<H: SmtHandler> CategoryParser<H> for TermParser<H> {
    type Result = H::Term;

    fn init() -> Self {
        Self {
            state: TermParserState::Start,
            stack: Vec::new(),
        }
    }

    fn progress(
        mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Term, Self>, ParserOrHandlerError<H>> {
        match self.state {
            TermParserState::Start => {
                // just parse term start
                Ok(self
                    .parse_term_start(handler, token)?
                    .map_continue(|()| self))
            }
            TermParserState::Operator => {
                // find out what kind of an application-like S-term we have
                match token {
                    Token::Symbol(fn_name) => {
                        // TODO: functions should be quaified idents
                        // push application and move to term state
                        self.stack.push(TermLevel::Application(fn_name, Vec::new()));
                        self.state = TermParserState::Term;
                        Ok(ControlFlow::Continue(self))
                    }

                    Token::Reserved(Reserved::Let) => todo!("Let"),
                    Token::Reserved(Reserved::Lambda) => todo!("Lambda"),
                    Token::Reserved(Reserved::Forall) => todo!("Forall"),
                    Token::Reserved(Reserved::Exists) => todo!("Exists"),
                    Token::Reserved(Reserved::Match) => todo!("Match"),
                    Token::Reserved(Reserved::ExclamationMark) => todo!("Annotation"),
                    _ => Err(ParserError::ExpectedOperator.into()),
                }
            }
            TermParserState::Term => self.progress_last_term(handler, token),
        }
    }
}

impl<H: SmtHandler> TermParser<H> {
    fn progress_last_term(
        mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Term, Self>, ParserOrHandlerError<H>> {
        let level = self
            .stack
            .pop()
            .expect("Processing stack should be non-empty");
        match level {
            TermLevel::Application(fn_name, mut args) => {
                // if the token is closing parenthesis, close this term
                // otherwise, parse an argument term
                if matches!(token, Token::ParenClose) {
                    let term = SmtTerm::Application(SmtApplication {
                        function: SmtQualifiedIdent::Ident(SmtIdent {
                            name: fn_name.as_str(),
                            indices: vec![],
                        }),
                        args,
                    });
                    let term = handler
                        .handle_term(term)
                        .map_err(ParserOrHandlerError::HandlerError)?;
                    if let Some(lower_level) = self.stack.last_mut() {
                        match lower_level {
                            TermLevel::Application(_fn_name, args) => {
                                args.push(term);
                            }
                        }
                        Ok(ControlFlow::Continue(self))
                    } else {
                        Ok(ControlFlow::Break(term))
                    }
                } else {
                    match self.parse_term_start(handler, token)? {
                        ControlFlow::Continue(result) => result,
                        ControlFlow::Break(term) => {
                            args.push(term);
                        }
                    };
                    // put the level back
                    self.stack.push(TermLevel::Application(fn_name, args));
                    Ok(ControlFlow::Continue(self))
                }
            }
        }
    }

    fn parse_term_start(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Term, ()>, ParserOrHandlerError<H>> {
        match token {
            Token::ParenOpen => {
                // application, binder, or annotation
                // move to operator parsing
                self.state = TermParserState::Operator;
                Ok(ControlFlow::Continue(()))
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

    /*fn close_level(
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
    }*/
}

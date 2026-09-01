use std::ops::ControlFlow;

use crate::{
    SmtApplication, SmtHandler, SmtQualifiedIdent, SmtSymbol, SmtTerm,
    read::parser::{
        CloseParenParser, OpenParenParser, ParserError, SymbolParser,
        category::{
            CategoryParser, CategoryParserErrorKind, parse_special_constant,
            qualified_ident::QualifiedIdentParser,
        },
        handle_err,
    },
    token::{Reserved, Token, TokenKind, TokenType},
};

enum TermLevel<H: SmtHandler> {
    Application(SmtQualifiedIdent<H>, Vec<H::Term>),
    LetBinding(Vec<(SmtSymbol, H::Term)>, SmtSymbol),
    LetInner,
}

enum TermState<H: SmtHandler> {
    Start,
    Open,
    QualifiedIdent(QualifiedIdentParser<H>),
    ApplicationQualifiedIdent(QualifiedIdentParser<H>),
    ApplicationTerm(SmtQualifiedIdent<H>, Vec<H::Term>),
    LetBeforeBindingsOpen,
    LetBeforeBindingOpen(Vec<(SmtSymbol, H::Term)>),
    LetBeforeBindingSymbol(Vec<(SmtSymbol, H::Term)>),
    LetBeforeBindingClose(Vec<(SmtSymbol, H::Term)>),
    LetAfterInnerTerm(H::Term),
}

pub struct TermParser<H: SmtHandler> {
    state: TermState<H>,
    levels: Vec<TermLevel<H>>,
}

impl<H: SmtHandler> TermParser<H> {
    pub fn new() -> Self {
        TermParser {
            state: TermState::Start,
            levels: Vec::new(),
        }
    }
}

impl<H: SmtHandler> Default for TermParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for TermParser<H> {
    type Result = H::Term;

    fn progress(
        self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Term, Self>, ParserError<H>> {
        let span = token.span();

        let (mut levels, term) = match self.progress_last_level(handler, token)? {
            ControlFlow::Continue(parser) => return Ok(ControlFlow::Continue(parser)),
            ControlFlow::Break((levels, term)) => (levels, term),
        };
        let Some(last_level) = levels.pop() else {
            // this is the root level, we are done
            return Ok(ControlFlow::Break(term));
        };

        // we need to append the newly created term to the last level
        let state = match last_level {
            TermLevel::Application(function, mut args) => {
                // add argument and go back to term state
                args.push(term);
                TermState::ApplicationTerm(function, args)
            }
            TermLevel::LetBinding(mut bindings, binding_name) => {
                // add binding, should be followed by parenthesis closing the bindings
                bindings.push((binding_name, term));
                TermState::LetBeforeBindingClose(bindings)
            }
            TermLevel::LetInner => {
                // end let, should be followed by closing parenthesis
                let term = handle_err(handler.end_let(term), span)?;
                TermState::LetAfterInnerTerm(term)
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
    ) -> Result<TermProgressOk<H, Self>, ParserError<H>> {
        let span = token.span();
        let mut levels = self.levels;
        let state = match self.state {
            TermState::Start => return Self::parse_term_start(levels, handler, token),
            TermState::Open => {
                return Ok(ControlFlow::Continue(Self::parse_term_open(levels, token)?));
            }
            TermState::QualifiedIdent(parser) => match parser.progress(handler, token)? {
                ControlFlow::Continue(parser) => TermState::QualifiedIdent(parser),
                ControlFlow::Break(qualified_ident) => {
                    let term = SmtTerm::QualifiedIdent(qualified_ident);

                    let term = handle_err(handler.handle_term(term), span)?;
                    return Ok(ControlFlow::Break((levels, term)));
                }
            },
            TermState::ApplicationQualifiedIdent(parser) => {
                match parser.progress(handler, token)? {
                    ControlFlow::Continue(parser) => TermState::ApplicationQualifiedIdent(parser),
                    ControlFlow::Break(ident) => TermState::ApplicationTerm(ident, Vec::new()),
                }
            }
            TermState::ApplicationTerm(function, args) => {
                if matches!(token.kind(), TokenKind::ParenClose) {
                    // this ends the application term
                    // it must have at least one argument
                    if args.is_empty() {
                        return Err(ParserError::category_error(
                            CategoryParserErrorKind::EmptyTermApplication,
                            span,
                        ));
                    }
                    let term = SmtTerm::Application(SmtApplication { function, args });

                    let term = handle_err(handler.handle_term(term), span)?;
                    return Ok(ControlFlow::Break((levels, term)));
                } else {
                    // add the application to the level stack and parse the argument
                    levels.push(TermLevel::Application(function, args));
                    return Self::parse_term_start(levels, handler, token);
                }
            }
            TermState::LetBeforeBindingsOpen => {
                OpenParenParser::expect(token)?;
                TermState::LetBeforeBindingOpen(Vec::new())
            }
            TermState::LetBeforeBindingOpen(bindings) => {
                match token.kind() {
                    TokenKind::ParenOpen => {
                        // new binding
                        TermState::LetBeforeBindingSymbol(bindings)
                    }
                    TokenKind::ParenClose => {
                        // bindings are closed, inner term will be next
                        // check that there is at least one binding
                        if bindings.is_empty() {
                            return Err(ParserError::category_error(
                                CategoryParserErrorKind::EmptyLetBindings,
                                span,
                            ));
                        }

                        handle_err(handler.start_let(bindings), span)?;

                        levels.push(TermLevel::LetInner);
                        TermState::Start
                    }
                    _ => {
                        // expected open or close parenthesis
                        return Err(ParserError::category_error(
                            CategoryParserErrorKind::ExpectedToken(&[
                                TokenType::ParenOpen,
                                TokenType::ParenClose,
                            ]),
                            span,
                        ));
                    }
                }
            }
            TermState::LetBeforeBindingSymbol(bindings) => {
                let symbol = SymbolParser::expect(token)?;
                levels.push(TermLevel::LetBinding(bindings, symbol));
                TermState::Start
            }
            TermState::LetBeforeBindingClose(bindings) => {
                CloseParenParser::expect(token)?;
                TermState::LetBeforeBindingOpen(bindings)
            }
            TermState::LetAfterInnerTerm(term) => {
                CloseParenParser::expect(token)?;
                return Ok(ControlFlow::Break((levels, term)));
            }
        };
        Ok(ControlFlow::Continue(Self { state, levels }))
    }

    fn parse_term_start(
        levels: Vec<TermLevel<H>>,
        handler: &mut H,
        token: Token,
    ) -> Result<TermProgressOk<H, Self>, ParserError<H>> {
        let span = token.span();
        match token.kind() {
            TokenKind::ParenOpen => {
                // application, binder, or annotation
                // move to operator parsing
                Ok(ControlFlow::Continue(Self {
                    state: TermState::Open,
                    levels,
                }))
            }
            TokenKind::Symbol(name) => {
                // a qualified identifier that is just a symbol
                let qualified_ident = SmtQualifiedIdent::new_simple(name.into_owned());
                let term = handle_err(
                    handler.handle_term(SmtTerm::QualifiedIdent(qualified_ident)),
                    span,
                )?;

                Ok(ControlFlow::Break((levels, term)))
            }

            kind => {
                // handle special constants
                match parse_special_constant(kind) {
                    Ok(special_constant) => {
                        let term = handle_err(
                            handler.handle_term(SmtTerm::SpecialConstant(special_constant)),
                            span,
                        )?;
                        Ok(ControlFlow::Break((levels, term)))
                    }
                    Err(_token) => Err(ParserError::category_error(
                        CategoryParserErrorKind::ExpectedTerm,
                        span,
                    )),
                }
            }
        }
    }

    fn parse_term_open(levels: Vec<TermLevel<H>>, token: Token) -> Result<Self, ParserError<H>> {
        let span = token.span();
        let state = match token.kind() {
            TokenKind::Symbol(fn_name) => {
                // this is an application where the function identifier is just a symbol
                let fn_ident = SmtQualifiedIdent::new_simple(fn_name.into_owned());
                TermState::ApplicationTerm(fn_ident, Vec::new())
            }
            TokenKind::Reserved(Reserved::Let) => TermState::LetBeforeBindingsOpen,
            TokenKind::Reserved(Reserved::Lambda) => todo!("Lambda"),
            TokenKind::Reserved(Reserved::Forall) => todo!("Forall"),
            TokenKind::Reserved(Reserved::Exists) => todo!("Exists"),
            TokenKind::Reserved(Reserved::Match) => todo!("Match"),
            TokenKind::Reserved(Reserved::ExclamationMark) => todo!("Annotation"),
            TokenKind::Reserved(Reserved::Underscore) => {
                // this is actually a term composed of an indexed identifier
                // start a qualified ident parser after the underscore
                // (meaning the ident will be unqualified but indexed)
                TermState::QualifiedIdent(QualifiedIdentParser::after_underscore())
            }
            TokenKind::Reserved(Reserved::As) => {
                // this is actually a term composed of a qualified identifier
                // start a qualified ident parser after the 'as' reserved word
                // (meaning the ident will be qualified)
                TermState::QualifiedIdent(QualifiedIdentParser::after_as())
            }
            TokenKind::ParenOpen => {
                // this is an application where the function identifier is qualified or indexed
                // start a qualified ident parser after the parenthesis open
                TermState::ApplicationQualifiedIdent(QualifiedIdentParser::after_open_paren())
            }
            _ => {
                return Err(ParserError::category_error(
                    CategoryParserErrorKind::ExpectedOperator,
                    span,
                ));
            }
        };
        Ok(Self { state, levels })
    }
}

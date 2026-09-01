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

/// A parser that reads an SMT-LIB term.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct TermParser<H: SmtHandler> {
    /// Current parser state.
    state: State,
    /// Levels of terms waiting for inner terms.
    levels: Vec<Level<H>>,
    /// A term that is already processed, but waiting for a closing parenthesis.
    pending_term: Option<H::Term>,

    qualified_ident_parser: QualifiedIdentParser<H>,
}

/// State of the term parser.
///
/// There are no ApplicationTerm or LetBinding states:
/// these are handled by opening a new term level.
enum State {
    /// Waiting for the first token.
    Start,
    /// After opening parenthesis "(".
    Open,
    /// This term is a qualified ident, after "(_" or "(as").
    ///
    /// Parsing delegated to the qualified-ident parser.
    QualifiedIdent,
    /// This term is an application, and we are parsing its ident.
    ///
    /// Parsing delegated to the qualified-ident parser.
    ApplicationIdent,
    /// This term is a let: "(let", we are positioned before the bindings open.
    ///
    /// We expect an opening parenthesis (opening the bindings) next.
    LetAllBindingsOpen,
    /// This term is a let, we are positioned before a binding parenthesis starts.
    ///
    /// We expect either an opening parenthesis (new binding),
    /// or a closing one (ending the bindings).
    LetBindingOpen,
    /// The term is a let, we are positioned before a binding symbol starts.
    ///
    /// We expect a symbol next.
    LetBindingSymbol,
    /// The term is a let, we are positioned after a binding term.
    ///
    /// We expect a closing parenthesis (closing the binding) next.
    LetBindingClose,
}

/// A term waiting for an inner term.
enum Level<H: SmtHandler> {
    /// An application waiting for an inner term.
    ///
    /// It is closed by a closing parenthesis instead of the inner term.
    Application {
        ident: SmtQualifiedIdent<H>,
        args: Vec<H::Term>,
    },
    /// A let waiting for a binding term.
    ///
    /// It is closed by a closing parenthesis instead of the inner term.
    LetBinding {
        bindings: Vec<(SmtSymbol, H::Term)>,
        binding_name: SmtSymbol,
    },
    /// A let waiting for the inner term.
    ///
    /// After consuming the term, we must also consume a closing parenthesis.
    LetInner,
}

impl<H: SmtHandler> TermParser<H> {
    pub fn new() -> Self {
        TermParser {
            state: State::Start,
            levels: Vec::new(),
            pending_term: None,

            qualified_ident_parser: QualifiedIdentParser::new(),
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
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<H::Term>, ParserError<H>> {
        let span = token.span();
        let term = match self.pending_term.take() {
            Some(term) => {
                // we have a pending term and are waiting for a closing parenthesis
                CloseParenParser::expect(token)?;
                term
            }
            None => {
                // no pending term, try to get one
                let ControlFlow::Break(term) = self.progress_inner(handler, token)? else {
                    return Ok(ControlFlow::Continue(()));
                };
                self.state = State::Start;
                handle_err(handler.handle_term(term), span)?
            }
        };

        // we have parsed a term, set state to start
        self.state = State::Start;

        // either update the last level with the term or return it if there is none
        // PERFORMANCE: take the last level as mutable instead of wholly consuming it
        match self.levels.last_mut() {
            Some(Level::Application { args, .. }) => {
                // add term as the next argument
                args.push(term);
                Ok(ControlFlow::Continue(()))
            }
            Some(Level::LetBinding {
                bindings,
                binding_name,
            }) => {
                // we need to swap to a new symbol here
                let mut name = SmtSymbol::new_empty();
                std::mem::swap(binding_name, &mut name);
                bindings.push((name, term));
                self.state = State::LetBindingClose;
                Ok(ControlFlow::Continue(()))
            }
            Some(Level::LetInner) => {
                // end the let and wait for the closing parenthesis
                self.levels.pop();
                let term = handle_err(handler.end_let(term), span)?;
                self.pending_term = Some(term);
                Ok(ControlFlow::Continue(()))
            }
            None => {
                // root level, return the term
                Ok(ControlFlow::Break(term))
            }
        }
    }
}

impl<H: SmtHandler> TermParser<H> {
    fn progress_inner(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<SmtTerm<H>>, ParserError<H>> {
        match self.state {
            State::Start => self.parse_term_start(token),
            State::Open => {
                self.parse_term_open(token)?;
                Ok(ControlFlow::Continue(()))
            }
            State::QualifiedIdent => Ok(self
                .qualified_ident_parser
                .progress(handler, token)?
                .map_break(SmtTerm::QualifiedIdent)),
            State::ApplicationIdent => {
                match self.qualified_ident_parser.progress(handler, token)? {
                    ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
                    ControlFlow::Break(ident) => {
                        // start a new level
                        self.start_level(Level::Application {
                            ident,
                            args: Vec::new(),
                        });
                        Ok(ControlFlow::Continue(()))
                    }
                }
            }
            State::LetAllBindingsOpen => {
                // expect an opening parenthesis and move to the single binding
                OpenParenParser::expect(token)?;
                self.state = State::LetBindingOpen;
                Ok(ControlFlow::Continue(()))
            }
            State::LetBindingOpen => self.parse_let_binding_open(handler, token),
            State::LetBindingSymbol => {
                // except a symbol that will be the binding name
                let mut symbol = SymbolParser::expect(token)?;
                // mutably take the let bindings on the last level and add the name
                // for performance, we do not switch bindings between level and state,
                // so we need to unwrap
                let Some(Level::LetBinding { binding_name, .. }) = self.levels.last_mut() else {
                    panic!("last level should be a let binding when adding a binding symbol")
                };
                // set the binding name
                std::mem::swap(binding_name, &mut symbol);
                // go to the start state to parse the binding term
                self.state = State::Start;
                Ok(ControlFlow::Continue(()))
            }
            State::LetBindingClose => {
                // expect a close parenthesis
                CloseParenParser::expect(token)?;
                // move to before binding open, a next binding can be opened
                self.state = State::LetBindingOpen;
                Ok(ControlFlow::Continue(()))
            }
        }
    }

    fn parse_term_start(
        &mut self,
        token: Token,
    ) -> Result<ControlFlow<SmtTerm<H>>, ParserError<H>> {
        match token.kind() {
            TokenKind::ParenOpen => {
                // application, binder, or annotation
                // move to operator parsing
                self.state = State::Open;
                Ok(ControlFlow::Continue(()))
            }
            TokenKind::ParenClose => {
                // this is only permitted when we are ending an application
                // pop the level and construct it
                if let Some(Level::Application { ident, args }) = self.levels.pop() {
                    // an application must contain at least one argument
                    if args.is_empty() {
                        return Err(ParserError::category_error(
                            CategoryParserErrorKind::EmptyTermApplication,
                            token.span(),
                        ));
                    }
                    // construct the term and break with it
                    let term = SmtTerm::Application(SmtApplication {
                        function: ident,
                        args,
                    });
                    Ok(ControlFlow::Break(term))
                } else {
                    Err(ParserError::category_error(
                        CategoryParserErrorKind::ExpectedTerm,
                        token.span(),
                    ))
                }
            }
            TokenKind::Symbol(name) => {
                // a term that is a qualified identifier that is just a symbol
                let term =
                    SmtTerm::QualifiedIdent(SmtQualifiedIdent::new_simple(name.into_owned()));
                Ok(ControlFlow::Break(term))
            }
            kind => {
                // handle special constants
                let span = token.span();
                match parse_special_constant(kind) {
                    Ok(special_constant) => {
                        // a term that is just a special constant
                        let term = SmtTerm::SpecialConstant(special_constant);
                        Ok(ControlFlow::Break(term))
                    }
                    Err(_) => Err(ParserError::category_error(
                        CategoryParserErrorKind::ExpectedTerm,
                        span,
                    )),
                }
            }
        }
    }

    fn parse_term_open(&mut self, token: Token) -> Result<(), ParserError<H>> {
        let span = token.span();
        let state = match token.kind() {
            TokenKind::Symbol(fn_name) => {
                // this is an application where the function identifier is just a symbol
                // start a new level
                let fn_ident = SmtQualifiedIdent::new_simple(fn_name.into_owned());
                self.start_level(Level::Application {
                    ident: fn_ident,
                    args: Vec::new(),
                });
                return Ok(());
            }
            TokenKind::Reserved(Reserved::Let) => {
                // add a level for let bindings and move before the bindings opening
                self.levels.push(Level::LetBinding {
                    bindings: Vec::new(),
                    binding_name: SmtSymbol::new_empty(),
                });
                State::LetAllBindingsOpen
            }
            TokenKind::Reserved(Reserved::Lambda) => todo!("Lambda"),
            TokenKind::Reserved(Reserved::Forall) => todo!("Forall"),
            TokenKind::Reserved(Reserved::Exists) => todo!("Exists"),
            TokenKind::Reserved(Reserved::Match) => todo!("Match"),
            TokenKind::Reserved(Reserved::ExclamationMark) => todo!("Annotation"),
            TokenKind::Reserved(Reserved::Underscore) => {
                // this is actually a term composed of an indexed identifier
                // start a qualified ident parser after the underscore
                // (meaning the ident will be unqualified but indexed)
                self.qualified_ident_parser = QualifiedIdentParser::after_underscore();
                State::QualifiedIdent
            }
            TokenKind::Reserved(Reserved::As) => {
                // this is actually a term composed of a qualified identifier
                // start a qualified ident parser after the 'as' reserved word
                // (meaning the ident will be qualified)
                self.qualified_ident_parser = QualifiedIdentParser::after_as();
                State::QualifiedIdent
            }
            TokenKind::ParenOpen => {
                // this is an application where the function identifier is qualified or indexed
                // start a qualified ident parser after the parenthesis open
                self.qualified_ident_parser = QualifiedIdentParser::after_open_paren();
                State::ApplicationIdent
            }
            _ => {
                return Err(ParserError::category_error(
                    CategoryParserErrorKind::ExpectedOperator,
                    span,
                ));
            }
        };
        self.state = state;
        Ok(())
    }

    fn parse_let_binding_open(
        &mut self,
        handler: &mut H,
        token: Token,
    ) -> Result<ControlFlow<SmtTerm<H>>, ParserError<H>> {
        let span = token.span();
        match token.kind() {
            TokenKind::ParenOpen => {
                // opening a new binding, we will parse the symbol next
                self.state = State::LetBindingSymbol;
            }
            TokenKind::ParenClose => {
                // bindings are closed, inner term will be next

                // retrieve the bindings
                // for performance, we do not switch bindings between level and state,
                // so we need to unwrap
                let Some(Level::LetBinding {
                    bindings,
                    binding_name,
                }) = self.levels.pop()
                else {
                    panic!("last level should be a let binding when closing bindings")
                };
                assert!(
                    binding_name.is_empty(),
                    "additional binding name should be empty when closing bindings"
                );

                // there must be at least one binding
                if bindings.is_empty() {
                    return Err(ParserError::category_error(
                        CategoryParserErrorKind::EmptyLetBindings,
                        span,
                    ));
                }

                // tell the handler we are starting a let
                handle_err(handler.start_let(bindings), span)?;

                // add a new level for the inner term in the let
                self.start_level(Level::LetInner);
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
        Ok(ControlFlow::Continue(()))
    }

    fn start_level(&mut self, level: Level<H>) {
        // push the level and move to the start state
        self.levels.push(level);
        self.state = State::Start;
    }
}

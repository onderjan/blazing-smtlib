use std::ops::ControlFlow;

use crate::{
    SmtApplication, SmtHandler, SmtQualifiedIdent, SmtQuantifierKind, SmtSymbol, SmtTerm,
    read::parser::{
        CloseParenParser, OpenParenParser, ParserError, ParserResources, SortedVarParser,
        SymbolParser,
        category::{
            CategoryErrorKind, CategoryParser, attribute::ClosedMultipleAttributeParser,
            parse_special_constant, pattern::PatternParser, qualified_ident::QualifiedIdentParser,
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
    /// A pending, already processed, term.
    ///
    /// This takes priority over the state and levels.
    pending: Option<Pending<H>>,

    qualified_ident_parser: QualifiedIdentParser<H>,
    attributes_parser: ClosedMultipleAttributeParser<H>,
    sorted_bindings_parser: SortedBindingsParser<H>,
    pattern_parser: PatternParser<H>,
}

#[derive(Clone, Copy)]
enum SortedBinderKind {
    Exists,
    Forall,
    Lambda,
}

#[derive(Clone, Copy)]
enum BinderEndKind {
    Quantifier,
    Lambda,
    Let,
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

    /// The term is a forall/exists/lambda binder, we are parsing its bound variables.
    SortedBinderVars(SortedBinderKind),

    /// The term is a match, we are positioned before the cases open.
    ///
    /// The scrutinee was already handled.
    /// We expect an opening parenthesis (opening the cases) next.
    MatchCasesOpen,
    /// The term is a match, we are positioned before a case parenthesis starts.
    ///
    /// We expect either an opening parenthesis (new case),
    /// or a closing one (ending the cases).
    MatchCaseOpen,
    /// The term is a match, we are parsing a case pattern.
    ///
    /// Parsing delegated to the pattern parser.
    MatchPattern,
    /// The term is a match, we are positioned after a case term.
    ///
    /// We expect a closing parenthesis (closing the case) next.
    MatchCaseClose,
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
    /// A binder (lambda/let/forall/exists) waiting for the inner term.
    ///
    /// After consuming the term, we close all desugared binders.
    /// Then, we must also consume a closing parenthesis.
    BinderInner {
        end_kind: BinderEndKind,
        num_close: u64,
    },

    /// An annotation waiting for the inner term.
    ///
    /// After consuming the term, we consume attributes (at least one),
    /// then a closing parenthesis.
    Annotation,

    /// A match waiting for the scrutinee term.
    ///
    /// The cases will follow after we consume the term.
    MatchScrutinee,
    /// A match waiting for a case term.
    ///
    /// It is closed by a closing parenthesis instead of the inner term.
    MatchCase { num_cases: u64 },
}

/// A pending term has been processed.
///
/// This has priority over the state and levels.
struct Pending<H: SmtHandler> {
    term: H::Term,
    /// Determines if the term we are creating is an annotation.
    ///
    /// True: we are parsing attributes after the inner term.
    /// False: we are just waiting for a closing parenthesis.
    is_annotation: bool,
}

impl<H: SmtHandler> TermParser<H> {
    pub fn new() -> Self {
        TermParser {
            state: State::Start,
            levels: Vec::new(),
            pending: None,

            qualified_ident_parser: QualifiedIdentParser::new(),
            attributes_parser: ClosedMultipleAttributeParser::new(),
            sorted_bindings_parser: SortedBindingsParser::new(),
            pattern_parser: PatternParser::new(),
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

    #[inline]
    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources,
        token: &Token,
    ) -> Result<ControlFlow<H::Term>, ParserError<H::Error>> {
        let span = token.span();
        let term = match self.pending.take() {
            Some(pending) => {
                if pending.is_annotation {
                    // we are parsing attributes
                    match self.attributes_parser.progress(handler, resources, token)? {
                        ControlFlow::Continue(()) => {
                            // put the pending term back
                            self.pending = Some(pending);
                            return Ok(ControlFlow::Continue(()));
                        }
                        ControlFlow::Break(attributes) => {
                            // check that there is at least one attribute
                            if attributes.is_empty() {
                                return Err(ParserError::category_error(
                                    CategoryErrorKind::EmptyAnnotation,
                                    span,
                                ));
                            }
                            // produce the annotated term
                            handle_err(handler.annotate_term(pending.term, attributes), span)?
                        }
                    }
                } else {
                    // we are waiting for a closing parenthesis
                    CloseParenParser::expect(token)?;
                    // produce the term
                    pending.term
                }
            }
            None => {
                // no pending term, try to get one
                let ControlFlow::Break(term) = self.progress_inner(handler, resources, token)?
                else {
                    return Ok(ControlFlow::Continue(()));
                };
                self.state = State::Start;
                handle_err(handler.handle_term(term), span)?
            }
        };

        // we have parsed a term, set state to start
        self.state = State::Start;

        // return the term if there is no last level
        // PERFORMANCE: take the last level as mutable instead of wholly consuming it
        let Some(last_level) = self.levels.last_mut() else {
            // root level, return the term
            return Ok(ControlFlow::Break(term));
        };

        // update the last level with the term
        match last_level {
            Level::Application { args, .. } => {
                // add term as the next argument
                args.push(term);
            }
            Level::LetBinding {
                bindings,
                binding_name,
            } => {
                // we need to swap to a new symbol here
                let mut name = SmtSymbol::new_empty();
                std::mem::swap(binding_name, &mut name);
                bindings.push((name, term));
                self.state = State::LetBindingClose;
            }
            Level::BinderInner {
                end_kind,
                num_close,
            } => {
                // end the binder
                let (end_kind, num_close) = (*end_kind, *num_close);
                self.levels.pop();

                // call the handler repeatedly to close all desugared binders
                let mut term = term;
                for _ in 0..num_close {
                    let handled = match end_kind {
                        BinderEndKind::Quantifier => handler.end_quantifier(term),
                        BinderEndKind::Lambda => handler.end_lambda(term),
                        BinderEndKind::Let => handler.end_let(term),
                    };
                    term = handle_err(handled, span)?;
                }
                // wait for the closing parenthesis
                self.pending = Some(Pending {
                    term,
                    is_annotation: false,
                });
            }
            Level::Annotation => {
                // put the term into pending and start parsing attributes
                self.levels.pop();
                self.pending = Some(Pending {
                    term,
                    is_annotation: true,
                });
            }
            Level::MatchScrutinee => {
                // the scrutinee has been parsed, start the match in the handler
                self.levels.pop();
                handle_err(handler.start_match(term), span)?;
                // the case terms will be processed on a new level
                self.levels.push(Level::MatchCase { num_cases: 0 });
                self.state = State::MatchCasesOpen;
            }
            Level::MatchCase { num_cases } => {
                // a case term has been parsed, end the case in the handler
                handle_err(handler.end_match_case(term), span)?;
                // increment the number of cases and move to expect
                // the closing match case parenthesis
                *num_cases += 1;
                self.state = State::MatchCaseClose;
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

impl<H: SmtHandler> TermParser<H> {
    #[inline]
    fn progress_inner(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources,
        token: &Token,
    ) -> Result<ControlFlow<SmtTerm<H>>, ParserError<H::Error>> {
        match self.state {
            State::Start => self.parse_term_start(token),
            State::Open => {
                self.parse_term_open(resources, token)?;
                Ok(ControlFlow::Continue(()))
            }
            State::QualifiedIdent => Ok(self
                .qualified_ident_parser
                .progress(handler, resources, token)?
                .map_break(SmtTerm::QualifiedIdent)),
            State::ApplicationIdent => {
                match self
                    .qualified_ident_parser
                    .progress(handler, resources, token)?
                {
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
                // expect a symbol that will be the binding name
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
            State::SortedBinderVars(binder_kind) => {
                let span = token.span();

                let flow = self.sorted_bindings_parser.progress_and_open(
                    handler,
                    resources,
                    token,
                    |handler, name, sort| match binder_kind {
                        SortedBinderKind::Exists => {
                            handler.start_quantifier(SmtQuantifierKind::Exists, name, sort)
                        }
                        SortedBinderKind::Forall => {
                            handler.start_quantifier(SmtQuantifierKind::Forall, name, sort)
                        }
                        SortedBinderKind::Lambda => handler.start_lambda(name, sort),
                    },
                )?;

                match flow {
                    ControlFlow::Continue(()) => {}
                    ControlFlow::Break(num_opened) => {
                        // there must be at least one sorted variable in the binder
                        if num_opened == 0 {
                            let err_kind: CategoryErrorKind = match binder_kind {
                                SortedBinderKind::Exists | SortedBinderKind::Forall => {
                                    CategoryErrorKind::EmptyQuantifierBindings
                                }
                                SortedBinderKind::Lambda => CategoryErrorKind::EmptyLambdaBindings,
                            };
                            return Err(ParserError::category_error(err_kind, span));
                        }

                        let end_kind = match binder_kind {
                            SortedBinderKind::Exists => BinderEndKind::Quantifier,
                            SortedBinderKind::Forall => BinderEndKind::Quantifier,
                            SortedBinderKind::Lambda => BinderEndKind::Lambda,
                        };

                        // push a level to handle the inner term and then properly close all opened binders
                        self.start_level(Level::BinderInner {
                            end_kind,
                            num_close: num_opened,
                        });
                    }
                }
                Ok(ControlFlow::Continue(()))
            }
            State::MatchCasesOpen => {
                // expect an opening parenthesis
                OpenParenParser::expect(token)?;
                // move to awaiting a match case or a closing parenthesis
                self.state = State::MatchCaseOpen;
                Ok(ControlFlow::Continue(()))
            }
            State::MatchCaseOpen => self.parse_match_case_open(handler, token),
            State::MatchPattern => {
                // parse the match pattern
                let span = token.span();
                if let ControlFlow::Break(pattern) =
                    self.pattern_parser.progress(handler, resources, token)?
                {
                    // a match case is starting, call the handler
                    handle_err(handler.start_match_case(pattern), span)?;
                    // move the start state to parse the case term
                    self.state = State::Start;
                }
                Ok(ControlFlow::Continue(()))
            }
            State::MatchCaseClose => {
                // expect a closing parenthesis
                CloseParenParser::expect(token)?;
                // move to await a match case or a closing parenthesis
                self.state = State::MatchCaseOpen;
                Ok(ControlFlow::Continue(()))
            }
        }
    }

    #[inline]
    fn parse_term_start(
        &mut self,
        token: &Token,
    ) -> Result<ControlFlow<SmtTerm<H>>, ParserError<H::Error>> {
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
                            CategoryErrorKind::EmptyTermApplication,
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
                        CategoryErrorKind::ExpectedTerm,
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
                        CategoryErrorKind::ExpectedTerm,
                        span,
                    )),
                }
            }
        }
    }

    #[inline]
    fn parse_term_open(
        &mut self,
        resources: &mut ParserResources,
        token: &Token,
    ) -> Result<(), ParserError<H::Error>> {
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
            TokenKind::Reserved(Reserved::Lambda) => {
                // this is a lambda, move to parsing its variables
                State::SortedBinderVars(SortedBinderKind::Lambda)
            }
            TokenKind::Reserved(Reserved::Forall) => {
                // this is a universal binder, move to parsing its variables
                State::SortedBinderVars(SortedBinderKind::Forall)
            }
            TokenKind::Reserved(Reserved::Exists) => {
                // this is an existential binder, move to parsing its variables
                State::SortedBinderVars(SortedBinderKind::Exists)
            }
            TokenKind::Reserved(Reserved::Match) => {
                // this is a match
                // we are parsing its scrutinee next, add a level for it
                self.start_level(Level::MatchScrutinee);
                return Ok(());
            }
            TokenKind::Reserved(Reserved::ExclamationMark) => {
                // this is an annotation
                // we are parsing its annotated term next, add a level for it
                self.start_level(Level::Annotation);
                return Ok(());
            }
            TokenKind::Reserved(Reserved::Underscore) => {
                // this is actually a term composed of an indexed identifier
                // move the qualified ident parser after the underscore
                // (meaning the ident will be unqualified but indexed)
                self.qualified_ident_parser.move_after_underscore(resources);
                State::QualifiedIdent
            }
            TokenKind::Reserved(Reserved::As) => {
                // this is actually a term composed of a qualified identifier
                // move the qualified ident parser after the 'as' reserved word
                // (meaning the ident will be qualified)
                self.qualified_ident_parser.move_after_as();
                State::QualifiedIdent
            }
            TokenKind::ParenOpen => {
                // this is an application where the function identifier is qualified or indexed
                // move the qualified ident parser after the parenthesis open
                self.qualified_ident_parser.move_after_open_paren();
                State::ApplicationIdent
            }
            _ => {
                return Err(ParserError::category_error(
                    CategoryErrorKind::ExpectedOperator,
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
        token: &Token,
    ) -> Result<ControlFlow<SmtTerm<H>>, ParserError<H::Error>> {
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
                        CategoryErrorKind::EmptyLetBindings,
                        span,
                    ));
                }

                // tell the handler we are starting a let
                handle_err(handler.start_let(bindings), span)?;

                // add a new level for the inner term in the let
                // we open it once, so we also need to close it once
                self.start_level(Level::BinderInner {
                    end_kind: BinderEndKind::Let,
                    num_close: 1,
                });
            }
            _ => {
                // expected open or close parenthesis
                return Err(ParserError::category_error(
                    CategoryErrorKind::ExpectedToken(&[
                        TokenType::ParenOpen,
                        TokenType::ParenClose,
                    ]),
                    span,
                ));
            }
        }
        Ok(ControlFlow::Continue(()))
    }

    fn parse_match_case_open(
        &mut self,
        handler: &mut H,
        token: &Token,
    ) -> Result<ControlFlow<SmtTerm<H>>, ParserError<H::Error>> {
        let span = token.span();
        match token.kind() {
            TokenKind::ParenOpen => {
                // a new case is being opened, we will parse the pattern next
                self.state = State::MatchPattern;
            }
            TokenKind::ParenClose => {
                // the match cases are done
                let Some(Level::MatchCase { num_cases }) = self.levels.pop() else {
                    panic!("last level should be a match case when closing cases")
                };
                // there must be at least one case
                if num_cases == 0 {
                    return Err(ParserError::category_error(
                        CategoryErrorKind::EmptyMatchCases,
                        span,
                    ));
                }

                // call the handler to signal the end of the match
                let term = handle_err(handler.end_match(), span)?;
                // wait for the closing parenthesis of the match, we will break after that
                self.pending = Some(Pending {
                    term,
                    is_annotation: false,
                });
            }
            _ => {
                return Err(ParserError::category_error(
                    CategoryErrorKind::ExpectedToken(&[
                        TokenType::ParenOpen,
                        TokenType::ParenClose,
                    ]),
                    span,
                ));
            }
        }
        Ok(ControlFlow::Continue(()))
    }

    #[inline]
    fn start_level(&mut self, level: Level<H>) {
        // push the level and move to the start state
        self.levels.push(level);
        self.state = State::Start;
    }
}

enum SortedBindingsParserState {
    Start,
    AwaitingBinder,
    ParsingBinder,
}

struct SortedBindingsParser<H: SmtHandler> {
    state: SortedBindingsParserState,
    num_opened: u64,
    sorted_var_parser: SortedVarParser<H>,
}

impl<H: SmtHandler> SortedBindingsParser<H> {
    fn new() -> Self {
        Self {
            state: SortedBindingsParserState::Start,
            num_opened: 0,
            sorted_var_parser: SortedVarParser::default(),
        }
    }
}

impl<H: SmtHandler> SortedBindingsParser<H> {
    fn progress_and_open(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources,
        token: &Token,
        open_fn: impl Fn(&mut H, SmtSymbol, H::Sort) -> Result<(), H::Error>,
    ) -> Result<ControlFlow<u64>, ParserError<H::Error>> {
        let token = match self.state {
            SortedBindingsParserState::Start => {
                // expect an opening parenthesis
                OpenParenParser::expect(token)?;
                self.state = SortedBindingsParserState::AwaitingBinder;
                return Ok(ControlFlow::Continue(()));
            }
            SortedBindingsParserState::AwaitingBinder => {
                // either a new sorted variable
                // or a closing parenthesis ending binders
                if matches!(token.kind(), TokenKind::ParenClose) {
                    let num_opened = self.num_opened;
                    // reset before break
                    self.state = SortedBindingsParserState::Start;
                    self.num_opened = 0;
                    return Ok(ControlFlow::Break(num_opened));
                }
                // parse the binder
                self.state = SortedBindingsParserState::ParsingBinder;
                token
            }
            SortedBindingsParserState::ParsingBinder => token,
        };

        // parse the sorted variable
        let span = token.span();
        match self.sorted_var_parser.progress(handler, resources, token)? {
            ControlFlow::Continue(()) => {}
            ControlFlow::Break((name, sort)) => {
                // start the binder and increment opened
                handle_err(open_fn(handler, name, sort), span)?;
                self.num_opened += 1;
                // go back to awaiting a binder
                self.state = SortedBindingsParserState::AwaitingBinder;
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

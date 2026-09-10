use std::ops::ControlFlow;

use crate::{
    SmtApplication, SmtHandler, SmtQualifiedIdent, SmtQuantifierKind, SmtSymbol, SmtTerm,
    read::parser::{
        CloseParenParser, IdentSlot, OpenParenParser, ParserError, ParserResources, SortSlot,
        SortedVarSlot,
        category::{
            CategoryErrorKind, CategoryParser, attribute::MultipleAttributes,
            parse_special_constant,
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
    _priv: std::marker::PhantomData<H>,
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
enum Level<H: SmtHandler + ?Sized> {
    /// An application waiting for an inner term.
    ///
    /// It is closed by a closing parenthesis instead of the inner term.
    Application {
        ident: SmtQualifiedIdent<H>,
        /// The arguments are terms stored in the arena starting at this position.
        arena_args_start: usize,
    },
    /// A let waiting for a binding term.
    ///
    /// It is closed by a closing parenthesis instead of the inner term.
    ///
    /// The binding names are stored in the arena symbols starting at the names
    /// position, with their text starting at the text position, and the binding
    /// terms are stored in the arena terms starting at the terms position.
    LetBinding {
        arena_text_start: usize,
        arena_names_start: usize,
        arena_terms_start: usize,
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
struct Pending<H: SmtHandler + ?Sized> {
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
            _priv: std::marker::PhantomData,
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

    #[inline(always)]
    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<ControlFlow<H::Term>, ParserError<H::Error>> {
        // progress the slot inside the resources
        TermSlot::progress(handler, resources, token)
    }
}

pub(crate) struct TermSlot<H: SmtHandler + ?Sized> {
    /// Current parser state.
    state: State,
    /// Levels of terms waiting for inner terms.
    levels: Vec<Level<H>>,
    /// A pending, already processed, term.
    ///
    /// This takes priority over the state and levels.
    pending: Option<Pending<H>>,

    sorted_bindings_parser: SortedBindingsParser,
}

impl<H: SmtHandler + ?Sized> TermSlot<H> {
    pub(crate) fn new() -> Self {
        Self {
            state: State::Start,
            levels: Vec::new(),
            pending: None,

            sorted_bindings_parser: SortedBindingsParser::new(),
        }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        matches!(self.state, State::Start)
            && self.levels.is_empty()
            && self.pending.is_none()
            && self.sorted_bindings_parser.is_pristine()
    }

    pub(crate) fn clear(&mut self) {
        self.state = State::Start;
        self.levels.clear();
        self.pending = None;
        self.sorted_bindings_parser.clear();
    }
}

impl<H: SmtHandler> TermSlot<H> {
    #[inline]
    pub(crate) fn progress(
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<ControlFlow<H::Term>, ParserError<H::Error>> {
        let span = token.span();
        let term = match resources.term_slot.pending.take() {
            Some(pending) => {
                if pending.is_annotation {
                    // we are parsing attributes
                    match resources.attribute_slot.progress::<MultipleAttributes>(
                        handler,
                        &mut resources.s_expr_slot,
                        token,
                    )? {
                        ControlFlow::Continue(()) => {
                            // put the pending term back
                            resources.term_slot.pending = Some(pending);
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
                match Self::progress_inner(handler, resources, token)? {
                    ControlFlow::Continue(()) => return Ok(ControlFlow::Continue(())),
                    ControlFlow::Break(term) => term,
                }
            }
        };

        // we have parsed a term, set state to start
        let slot = &mut resources.term_slot;
        slot.state = State::Start;

        // return the term if there is no last level
        // PERFORMANCE: take the last level as mutable instead of wholly consuming it
        let Some(last_level) = slot.levels.last_mut() else {
            // root level, return the term
            return Ok(ControlFlow::Break(term));
        };

        // update the last level with the term
        match last_level {
            Level::Application { .. } => {
                // push the produced term into the term arena
                // there no need to update anything else as lower-level terms
                // remember where their arguments start im the arena
                resources.store.terms.push(term);
            }
            Level::LetBinding { .. } => {
                // push the produced term into the term arena
                // its name is already in the arena symbols
                resources.store.terms.push(term);
                slot.state = State::LetBindingClose;
            }
            Level::BinderInner {
                end_kind,
                num_close,
            } => {
                // end the binder
                let (end_kind, num_close) = (*end_kind, *num_close);
                slot.levels.pop();

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
                slot.pending = Some(Pending {
                    term,
                    is_annotation: false,
                });
            }
            Level::Annotation => {
                // put the term into pending and start parsing attributes
                slot.levels.pop();
                slot.pending = Some(Pending {
                    term,
                    is_annotation: true,
                });
            }
            Level::MatchScrutinee => {
                // the scrutinee has been parsed, start the match in the handler
                slot.levels.pop();
                handle_err(handler.start_match(term), span)?;
                // the case terms will be processed on a new level
                slot.levels.push(Level::MatchCase { num_cases: 0 });
                slot.state = State::MatchCasesOpen;
            }
            Level::MatchCase { num_cases } => {
                // a case term has been parsed, end the case in the handler
                handle_err(handler.end_match_case(term), span)?;
                // increment the number of cases and move to expect
                // the closing match case parenthesis
                *num_cases += 1;
                slot.state = State::MatchCaseClose;
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

impl<H: SmtHandler> TermSlot<H> {
    #[inline]
    fn progress_inner(
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<ControlFlow<H::Term>, ParserError<H::Error>> {
        let slot = &mut resources.term_slot;

        match slot.state {
            State::Start => {
                // the start state is also reached before every inner term, so only
                // an empty level stack means the category is being entered
                if slot.levels.is_empty() {
                    debug_assert!(slot.is_pristine(), "must be pristine when starting");
                }
                Self::parse_term_start(handler, resources, token)
            }
            State::Open => {
                Self::parse_term_open(resources, token)?;
                Ok(ControlFlow::Continue(()))
            }
            State::QualifiedIdent => {
                match resources.qualified_ident_slot.progress(
                    handler,
                    &mut resources.sort_slot,
                    &mut resources.ident_slot,
                    token,
                )? {
                    ControlFlow::Break(qualified_ident) => {
                        // a term that is a qualified identifier, handle it and break
                        let term = SmtTerm::QualifiedIdent(qualified_ident);
                        let term = handle_err(handler.handle_term(term), token.span())?;
                        Ok(ControlFlow::Break(term))
                    }
                    ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
                }
            }
            State::ApplicationIdent => {
                match resources.qualified_ident_slot.progress(
                    handler,
                    &mut resources.sort_slot,
                    &mut resources.ident_slot,
                    token,
                )? {
                    ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
                    ControlFlow::Break(ident) => {
                        // start a new level
                        slot.start_level(Level::Application {
                            ident,
                            arena_args_start: resources.store.terms.len(),
                        });
                        Ok(ControlFlow::Continue(()))
                    }
                }
            }
            State::LetAllBindingsOpen => {
                // expect an opening parenthesis and move to the single binding
                OpenParenParser::expect(token)?;
                slot.state = State::LetBindingOpen;
                Ok(ControlFlow::Continue(()))
            }
            State::LetBindingOpen => {
                // parse the let binding and continue
                Self::parse_let_binding_open(handler, resources, token)?;
                Ok(ControlFlow::Continue(()))
            }
            State::LetBindingSymbol => {
                // expect a symbol that will be the binding name
                let TokenKind::Symbol(name) = token.kind() else {
                    return Err(ParserError::category_error(
                        CategoryErrorKind::ExpectedToken(&[TokenType::Symbol]),
                        token.span(),
                    ));
                };
                // push the name into the arena
                // the binding term knows where the binding names start
                let store = &mut resources.store;
                let name = store.push_text(name.as_slice());
                store.symbols.push(name);
                // go to the start state to parse the binding term
                slot.state = State::Start;
                Ok(ControlFlow::Continue(()))
            }
            State::LetBindingClose => {
                // expect a close parenthesis
                CloseParenParser::expect(token)?;
                // move to before binding open, a next binding can be opened
                slot.state = State::LetBindingOpen;
                Ok(ControlFlow::Continue(()))
            }
            State::SortedBinderVars(binder_kind) => {
                let span = token.span();

                let flow = slot.sorted_bindings_parser.progress_and_open(
                    handler,
                    &mut resources.sorted_var_slot,
                    &mut resources.sort_slot,
                    &mut resources.ident_slot,
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
                        slot.start_level(Level::BinderInner {
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
                slot.state = State::MatchCaseOpen;
                Ok(ControlFlow::Continue(()))
            }
            State::MatchCaseOpen => {
                // parse the match case and continue
                slot.parse_match_case_open(handler, token)?;
                Ok(ControlFlow::Continue(()))
            }
            State::MatchPattern => {
                // parse the match pattern
                let span = token.span();
                if let ControlFlow::Break(pattern) = resources.pattern_slot.progress(token)? {
                    // a match case is starting, call the handler
                    handle_err(handler.start_match_case(pattern), span)?;
                    // move the start state to parse the case term
                    slot.state = State::Start;
                }
                Ok(ControlFlow::Continue(()))
            }
            State::MatchCaseClose => {
                // expect a closing parenthesis
                CloseParenParser::expect(token)?;
                // move to await a match case or a closing parenthesis
                slot.state = State::MatchCaseOpen;
                Ok(ControlFlow::Continue(()))
            }
        }
    }

    #[inline]
    fn parse_term_start(
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<ControlFlow<H::Term>, ParserError<H::Error>> {
        let span = token.span();
        let slot = &mut resources.term_slot;
        let term = match token.kind() {
            TokenKind::ParenOpen => {
                // application, binder, or annotation
                // move to operator parsing
                slot.state = State::Open;
                return Ok(ControlFlow::Continue(()));
            }
            TokenKind::ParenClose => {
                // this is only permitted when we are ending an application
                // pop the level
                let Some(Level::Application {
                    ident,
                    arena_args_start,
                }) = slot.levels.pop()
                else {
                    return Err(ParserError::category_error(
                        CategoryErrorKind::ExpectedTerm,
                        span,
                    ));
                };
                let store = &mut resources.store;
                // the application must contain at least one argument
                if store.terms.len() == arena_args_start {
                    return Err(ParserError::category_error(
                        CategoryErrorKind::EmptyTermApplication,
                        span,
                    ));
                }
                // construct and handle the term, the arguments are consumed
                store.hand_over_terms(arena_args_start, |args| {
                    let term = SmtTerm::Application(SmtApplication {
                        function: ident,
                        args,
                    });
                    handle_err(handler.handle_term(term), span)
                })?
            }
            TokenKind::Symbol(name) => {
                // a term that is a qualified identifier that is just a symbol
                let term =
                    SmtTerm::QualifiedIdent(SmtQualifiedIdent::new_simple(name.into_owned()));
                handle_err(handler.handle_term(term), span)?
            }
            kind => {
                // handle special constants
                match parse_special_constant(kind) {
                    Ok(special_constant) => {
                        // a term that is just a special constant
                        let term = SmtTerm::SpecialConstant(special_constant);
                        handle_err(handler.handle_term(term), span)?
                    }
                    Err(_) => {
                        return Err(ParserError::category_error(
                            CategoryErrorKind::ExpectedTerm,
                            span,
                        ));
                    }
                }
            }
        };
        Ok(ControlFlow::Break(term))
    }

    #[inline]
    fn parse_term_open(
        resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<(), ParserError<H::Error>> {
        let span = token.span();
        let slot = &mut resources.term_slot;

        let state = match token.kind() {
            TokenKind::Symbol(fn_name) => {
                // this is an application where the function identifier is just a symbol
                // start a new level, remember where its arguments will start in the arena
                let fn_ident = SmtQualifiedIdent::new_simple(fn_name.into_owned());
                slot.start_level(Level::Application {
                    ident: fn_ident,
                    arena_args_start: resources.store.terms.len(),
                });
                return Ok(());
            }
            TokenKind::Reserved(Reserved::Let) => {
                // add a level for let bindings and move before the bindings opening
                // remember where the bindings start in the arena
                let store = &resources.store;
                slot.levels.push(Level::LetBinding {
                    arena_text_start: store.text.len(),
                    arena_names_start: store.symbols.len(),
                    arena_terms_start: store.terms.len(),
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
                slot.start_level(Level::MatchScrutinee);
                return Ok(());
            }
            TokenKind::Reserved(Reserved::ExclamationMark) => {
                // this is an annotation
                // we are parsing its annotated term next, add a level for it
                slot.start_level(Level::Annotation);
                return Ok(());
            }
            TokenKind::Reserved(Reserved::Underscore) => {
                // this is actually a term composed of an indexed identifier
                // move the qualified ident parser after the underscore
                // (meaning the ident will be unqualified but indexed)
                resources
                    .qualified_ident_slot
                    .move_after_underscore(&mut resources.ident_slot);
                State::QualifiedIdent
            }
            TokenKind::Reserved(Reserved::As) => {
                // this is actually a term composed of a qualified identifier
                // move the qualified ident parser after the 'as' reserved word
                // (meaning the ident will be qualified)
                resources.qualified_ident_slot.move_after_as();
                State::QualifiedIdent
            }
            TokenKind::ParenOpen => {
                // this is an application where the function identifier is qualified or indexed
                // move the qualified ident parser after the parenthesis open
                resources.qualified_ident_slot.move_after_open_paren();
                State::ApplicationIdent
            }
            _ => {
                return Err(ParserError::category_error(
                    CategoryErrorKind::ExpectedOperator,
                    span,
                ));
            }
        };
        slot.state = state;
        Ok(())
    }

    /// Parses an opening of a let binding.
    ///
    /// This cannot produce a term as we still need the parenthesis
    /// that closes the bindings followed by the rest of the term.
    fn parse_let_binding_open(
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<(), ParserError<H::Error>> {
        let span = token.span();
        let slot = &mut resources.term_slot;
        match token.kind() {
            TokenKind::ParenOpen => {
                // opening a new binding, we will parse the symbol next
                slot.state = State::LetBindingSymbol;
                Ok(())
            }
            TokenKind::ParenClose => {
                // bindings are closed, inner term will be next

                // retrieve where the bindings start in the arena
                let Some(Level::LetBinding {
                    arena_text_start,
                    arena_names_start,
                    arena_terms_start,
                }) = slot.levels.pop()
                else {
                    panic!("last level should be a let binding when closing bindings")
                };

                let store = &mut resources.store;
                // there must be at least one binding
                if store.symbols.len() == arena_names_start {
                    return Err(ParserError::category_error(
                        CategoryErrorKind::EmptyLetBindings,
                        span,
                    ));
                }

                // tell the handler we are starting a let, the bindings are consumed
                store.hand_over_bindings(
                    arena_text_start,
                    arena_names_start,
                    arena_terms_start,
                    |bindings| handle_err(handler.start_let(bindings), span),
                )?;

                // add a new level for the inner term in the let
                // we open it once, so we also need to close it once
                slot.start_level(Level::BinderInner {
                    end_kind: BinderEndKind::Let,
                    num_close: 1,
                });
                Ok(())
            }
            _ => {
                // expected open or close parenthesis
                Err(ParserError::category_error(
                    CategoryErrorKind::ExpectedToken(&[
                        TokenType::ParenOpen,
                        TokenType::ParenClose,
                    ]),
                    span,
                ))
            }
        }
    }

    /// Parses an opening of a let binding.
    ///
    /// This cannot produce a term as we still need the parenthesis
    /// that closes the match cases followed by the rest of the term.
    fn parse_match_case_open(
        &mut self,
        handler: &mut H,
        token: &Token,
    ) -> Result<(), ParserError<H::Error>> {
        let span = token.span();
        match token.kind() {
            TokenKind::ParenOpen => {
                // a new case is being opened, we will parse the pattern next
                self.state = State::MatchPattern;
                Ok(())
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
                Ok(())
            }
            _ => Err(ParserError::category_error(
                CategoryErrorKind::ExpectedToken(&[TokenType::ParenOpen, TokenType::ParenClose]),
                span,
            )),
        }
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

struct SortedBindingsParser {
    state: SortedBindingsParserState,
    num_opened: u64,
}

impl SortedBindingsParser {
    fn new() -> Self {
        Self {
            state: SortedBindingsParserState::Start,
            num_opened: 0,
        }
    }

    fn is_pristine(&self) -> bool {
        matches!(self.state, SortedBindingsParserState::Start) && self.num_opened == 0
    }

    fn clear(&mut self) {
        self.state = SortedBindingsParserState::Start;
        self.num_opened = 0;
    }
}

impl SortedBindingsParser {
    fn progress_and_open<H: SmtHandler>(
        &mut self,
        handler: &mut H,
        sorted_var_slot: &mut SortedVarSlot<H>,
        sort_slot: &mut SortSlot<H>,
        ident_slot: &mut IdentSlot,
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
        match sorted_var_slot.progress(handler, sort_slot, ident_slot, token)? {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckStandardSyntax, read::parser::category::tests::parse_all_with};

    #[test]
    fn slots_are_pristine_after_every_term() {
        // every term shape enters the term slot and, through it, the slots
        // of the categories a term contains; all must be back in their
        // initial state afterwards
        for input in [
            &b"x"[..],
            b"(f x 1)",
            b"((_ extract 3 0) x)",
            b"(as nil (List Int))",
            b"(let ((a x) (b y)) (g a b))",
            b"(let ((a x)) (let ((b a)) b))",
            b"(forall ((x Int) (y (_ BitVec 8))) (p x y))",
            b"(lambda ((x Int)) (f x))",
            b"(! (f x) :named n :pattern ((f x)))",
            b"(match l ((nil l2) ((cons h t) (cons h (append t l2)))))",
        ] {
            let mut resources = ParserResources::new();
            parse_all_with(
                TermParser::<CheckStandardSyntax>::new(),
                &mut resources,
                input,
            );
            assert!(resources.are_pristine(), "after {input:?}");
        }
    }
}

use std::ops::ControlFlow;

use crate::{
    SmtApplication, SmtHandler, SmtQualifiedIdentView, SmtQuantifierKind, SmtSpan, SmtSymbolView,
    SmtTerm,
    read::parser::{
        Arena, SyntaxErrorKind, CloseParenParser, OpenParenParser, Parser, ParserError,
        ParserResources, QualifiedIdentHandle,
        category::{attribute::MultipleAttributes, parse_special_constant},
        handle_err,
    },
    token::{GeneralReserved, Reserved, Token, TokenCursor, TokenKind, TokenType},
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
        /// The function identifier, stored in the arena.
        function: QualifiedIdentHandle<H>,
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

impl<H: SmtHandler> Parser<H> for TermParser<H> {
    type Result = H::Term;

    #[inline(always)]
    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: Token,
    ) -> Result<ControlFlow<H::Term>, ParserError<H::Error>> {
        // progress the slot with the token
        TermSlot::progress(handler, resources, token)
    }

    #[inline(always)]
    fn progress_all(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut TokenCursor<'_>,
    ) -> Result<ControlFlow<H::Term>, ParserError<H::Error>> {
        // progress the slot with the cursor
        TermSlot::progress_all(handler, resources, cursor)
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
    pub(crate) fn progress_all(
        handler: &mut H,
        resources: &mut ParserResources<H>,
        cursor: &mut TokenCursor,
    ) -> Result<ControlFlow<H::Term>, ParserError<H::Error>> {
        while let Some(token) = cursor.take() {
            if matches!(resources.term_slot.state, State::Start)
                && resources.term_slot.pending.is_none()
            {
                // PERFORMANCE: dispatch common term idioms fast.
                match token.ty() {
                    TokenType::UnquotedSymbol | TokenType::QuotedSymbol => {
                        if let TokenKind::Symbol(name) = resources.arena.token_kind(token) {
                            // this is an unqualified, non-indexed symbol, dispatch it
                            let term = SmtTerm::QualifiedIdent(SmtQualifiedIdentView {
                                ident: resources.arena.simple_ident_view(name),
                                sort: None,
                            });
                            let term = handle_err(handler.handle_term(term), token.span())?;
                            if let ControlFlow::Break(term) =
                                Self::finish_term(handler, resources, term, token.span())?
                            {
                                return Ok(ControlFlow::Break(term));
                            }
                            continue;
                        }
                    }
                    TokenType::ParenOpen => {
                        if let Some(peeked) = cursor.peek() {
                            match resources.arena.token_kind(peeked) {
                                TokenKind::Symbol(fn_name) => {
                                    // this is an application start
                                    // consume the peeked token and dispatch
                                    cursor.advance(1);
                                    let function = QualifiedIdentHandle::unqualified(
                                        resources.arena.push_nonindexed_ident(fn_name),
                                    );
                                    resources
                                        .term_slot
                                        .start_application(&resources.arena, function);
                                    continue;
                                }
                                TokenKind::Reserved(Reserved::General(GeneralReserved::Let)) => {
                                    // the proper way to start a let binder is "(let((name"
                                    // we need two more opening parentheses and a symbol
                                    if cursor
                                        .get(1)
                                        .is_some_and(|t| matches!(t.ty(), TokenType::ParenOpen))
                                        && cursor
                                            .get(2)
                                            .is_some_and(|t| matches!(t.ty(), TokenType::ParenOpen))
                                        && let Some(name_token) = cursor.get(3)
                                        && let TokenKind::Symbol(name) =
                                            resources.arena.token_kind(name_token)
                                    {
                                        // this is a let binder
                                        // consume the four peeked tokens
                                        cursor.advance(4);
                                        // dispatch the let and push the first binding name
                                        resources.term_slot.start_let(&mut resources.arena);
                                        resources
                                            .term_slot
                                            .push_binding_name(&mut resources.arena, name);
                                        continue;
                                    }
                                }
                                TokenKind::Reserved(Reserved::General(
                                    GeneralReserved::Underscore,
                                )) => {
                                    // an indexed identifier starts with "(_ name"
                                    if let Some(name_token) = cursor.get(1)
                                        && let TokenKind::Symbol(name) =
                                            resources.arena.token_kind(name_token)
                                    {
                                        // this is an indexed identifier
                                        // consume the two peeked tokens
                                        cursor.advance(2);
                                        // move the qualified ident after the indexed name
                                        resources.qualified_ident_slot.move_after_indexed_name(
                                            &mut resources.ident_slot,
                                            &mut resources.arena,
                                            name,
                                        );
                                        // change the state to qualified ident parsing
                                        resources.term_slot.state = State::QualifiedIdent;
                                        continue;
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    _ => {}
                }
            }

            match Self::progress(handler, resources, token)? {
                ControlFlow::Continue(()) => {}
                ControlFlow::Break(term) => {
                    // we are done
                    return Ok(ControlFlow::Break(term));
                }
            }
        }
        // not done yet
        Ok(ControlFlow::Continue(()))
    }

    #[inline]
    pub(crate) fn progress(
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: Token,
    ) -> Result<ControlFlow<H::Term>, ParserError<H::Error>> {
        let span = token.span();
        let term = match resources.term_slot.pending.take() {
            Some(pending) => {
                if pending.is_annotation {
                    // we are parsing attributes
                    match resources.attribute_slot.progress::<H, MultipleAttributes>(
                        handler,
                        &mut resources.arena,
                        &mut resources.s_expr_slot,
                        token,
                    )? {
                        ControlFlow::Continue(()) => {
                            // put the pending term back
                            resources.term_slot.pending = Some(pending);
                            return Ok(ControlFlow::Continue(()));
                        }
                        ControlFlow::Break(arena_attributes_start) => {
                            let arena = &mut resources.arena;
                            // check that there is at least one attribute
                            if arena.attributes.len() == arena_attributes_start {
                                return Err(ParserError::category_error(
                                    SyntaxErrorKind::EmptyAnnotation,
                                    span,
                                ));
                            }
                            // produce the annotated term, the attributes are consumed
                            arena.hand_over_attributes(arena_attributes_start, |attributes| {
                                handle_err(handler.annotate_term(pending.term, attributes), span)
                            })?
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

        Self::finish_term(handler, resources, term, span)
    }
}

impl<H: SmtHandler> TermSlot<H> {
    /// Processes a newly created term, updating the level above it if there is one.
    #[inline]
    fn finish_term(
        handler: &mut H,
        resources: &mut ParserResources<H>,
        term: H::Term,
        span: SmtSpan,
    ) -> Result<ControlFlow<H::Term>, ParserError<H::Error>> {
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
                resources.arena.terms.push(term);
            }
            Level::LetBinding { .. } => {
                // push the produced term into the term arena
                // its name is already in the arena symbols
                resources.arena.terms.push(term);
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

    #[inline]
    fn progress_inner(
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: Token,
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
                    &mut resources.arena,
                    &mut resources.sort_slot,
                    &mut resources.ident_slot,
                    token,
                )? {
                    ControlFlow::Break(qualified_ident) => {
                        // a term that is a qualified identifier, handle it and break
                        let span = token.span();
                        let term = resources.arena.hand_over_qualified_ident(
                            qualified_ident,
                            |qualified_ident| {
                                let term = SmtTerm::QualifiedIdent(qualified_ident);
                                handle_err(handler.handle_term(term), span)
                            },
                        )?;
                        Ok(ControlFlow::Break(term))
                    }
                    ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
                }
            }
            State::ApplicationIdent => {
                match resources.qualified_ident_slot.progress(
                    handler,
                    &mut resources.arena,
                    &mut resources.sort_slot,
                    &mut resources.ident_slot,
                    token,
                )? {
                    ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
                    ControlFlow::Break(function) => {
                        // start a new application level
                        resources
                            .term_slot
                            .start_application(&resources.arena, function);
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
                let TokenKind::Symbol(name) = resources.arena.token_kind(token) else {
                    return Err(ParserError::category_error(
                        SyntaxErrorKind::ExpectedSymbol,
                        token.span(),
                    ));
                };
                resources
                    .term_slot
                    .push_binding_name(&mut resources.arena, name);
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

                let flow = SortedBindingsParser::progress_and_open(
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
                            let err_kind: SyntaxErrorKind = match binder_kind {
                                SortedBinderKind::Exists | SortedBinderKind::Forall => {
                                    SyntaxErrorKind::EmptyQuantifierBindings
                                }
                                SortedBinderKind::Lambda => SyntaxErrorKind::EmptyLambdaBindings,
                            };
                            return Err(ParserError::category_error(err_kind, span));
                        }

                        let end_kind = match binder_kind {
                            SortedBinderKind::Exists => BinderEndKind::Quantifier,
                            SortedBinderKind::Forall => BinderEndKind::Quantifier,
                            SortedBinderKind::Lambda => BinderEndKind::Lambda,
                        };

                        // push a level to handle the inner term and then properly close all opened binders
                        resources.term_slot.start_level(Level::BinderInner {
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
                slot.parse_match_case_open(handler, &resources.arena, token)?;
                Ok(ControlFlow::Continue(()))
            }
            State::MatchPattern => {
                // parse the match pattern
                let span = token.span();
                if let ControlFlow::Break(pattern) = resources
                    .pattern_slot
                    .progress(&mut resources.arena, token)?
                {
                    // a match case is starting, call the handler with the pattern handed over
                    resources.arena.hand_over_pattern(pattern, |pattern| {
                        handle_err(handler.start_match_case(pattern), span)
                    })?;
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
        token: Token,
    ) -> Result<ControlFlow<H::Term>, ParserError<H::Error>> {
        let span = token.span();
        let slot = &mut resources.term_slot;
        let term = match resources.arena.token_kind(token) {
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
                    function,
                    arena_args_start,
                }) = slot.levels.pop()
                else {
                    return Err(ParserError::category_error(
                        SyntaxErrorKind::ExpectedTerm,
                        span,
                    ));
                };
                let arena = &mut resources.arena;
                // the application must contain at least one argument
                if arena.terms.len() == arena_args_start {
                    return Err(ParserError::category_error(
                        SyntaxErrorKind::EmptyTermApplication,
                        span,
                    ));
                }
                // construct and handle the term, the head and the arguments are consumed
                arena.hand_over_application(function, arena_args_start, |function, args| {
                    let term = SmtTerm::Application(SmtApplication { function, args });
                    handle_err(handler.handle_term(term), span)
                })?
            }
            TokenKind::Symbol(name) => {
                // a term that is a qualified identifier that is just a symbol,
                // handed over straight from the token
                let term = SmtTerm::QualifiedIdent(SmtQualifiedIdentView {
                    ident: resources.arena.simple_ident_view(name),
                    sort: None,
                });
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
                            SyntaxErrorKind::ExpectedTerm,
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
        token: Token,
    ) -> Result<(), ParserError<H::Error>> {
        let span = token.span();
        let slot = &mut resources.term_slot;

        let state = match resources.arena.token_kind(token) {
            TokenKind::Symbol(fn_name) => {
                // this is an application where the function identifier is just a symbol
                let function = QualifiedIdentHandle::unqualified(
                    resources.arena.push_nonindexed_ident(fn_name),
                );
                slot.start_application(&resources.arena, function);
                return Ok(());
            }
            TokenKind::Reserved(Reserved::General(GeneralReserved::Let)) => {
                // this is a let, start it
                slot.start_let(&mut resources.arena);
                return Ok(());
            }
            TokenKind::Reserved(Reserved::General(GeneralReserved::Lambda)) => {
                // this is a lambda, move to parsing its variables
                State::SortedBinderVars(SortedBinderKind::Lambda)
            }
            TokenKind::Reserved(Reserved::General(GeneralReserved::Forall)) => {
                // this is a universal binder, move to parsing its variables
                State::SortedBinderVars(SortedBinderKind::Forall)
            }
            TokenKind::Reserved(Reserved::General(GeneralReserved::Exists)) => {
                // this is an existential binder, move to parsing its variables
                State::SortedBinderVars(SortedBinderKind::Exists)
            }
            TokenKind::Reserved(Reserved::General(GeneralReserved::Match)) => {
                // this is a match
                // we are parsing its scrutinee next, add a level for it
                slot.start_level(Level::MatchScrutinee);
                return Ok(());
            }
            TokenKind::Reserved(Reserved::General(GeneralReserved::ExclamationMark)) => {
                // this is an annotation
                // we are parsing its annotated term next, add a level for it
                slot.start_level(Level::Annotation);
                return Ok(());
            }
            TokenKind::Reserved(Reserved::General(GeneralReserved::Underscore)) => {
                // this is actually a term composed of an indexed identifier
                // move the qualified ident parser after the underscore
                // (meaning the ident will be unqualified but indexed)
                resources
                    .qualified_ident_slot
                    .move_after_underscore(&mut resources.ident_slot);
                State::QualifiedIdent
            }
            TokenKind::Reserved(Reserved::General(GeneralReserved::As)) => {
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
                    SyntaxErrorKind::ExpectedOperator,
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
        token: Token,
    ) -> Result<(), ParserError<H::Error>> {
        let span = token.span();
        let slot = &mut resources.term_slot;
        match resources.arena.token_kind(token) {
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

                let arena = &mut resources.arena;
                // there must be at least one binding
                if arena.symbols.len() == arena_names_start {
                    return Err(ParserError::category_error(
                        SyntaxErrorKind::EmptyLetBindings,
                        span,
                    ));
                }

                // tell the handler we are starting a let, the bindings are consumed
                arena.hand_over_bindings(
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
                    SyntaxErrorKind::ExpectedToken(&[
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
        arena: &Arena<H>,
        token: Token,
    ) -> Result<(), ParserError<H::Error>> {
        let span = token.span();
        match arena.token_kind(token) {
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
                        SyntaxErrorKind::EmptyMatchCases,
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
                SyntaxErrorKind::ExpectedToken(&[TokenType::ParenOpen, TokenType::ParenClose]),
                span,
            )),
        }
    }

    #[inline]
    fn push_binding_name(&mut self, arena: &mut Arena<H>, name: SmtSymbolView) {
        // push the name into the arena
        // the binding term knows where the binding names start
        let name = arena.push_text(name.as_slice());
        arena.symbols.push(name);
        // go to the start state to parse the binding term
        self.state = State::Start;
    }

    #[inline]
    fn start_application(&mut self, arena: &Arena<H>, function: QualifiedIdentHandle<H>) {
        // a new level; the head is in the arena, its arguments follow from here
        self.start_level(Level::Application {
            function,
            arena_args_start: arena.terms.len(),
        });
    }

    #[inline]
    fn start_let(&mut self, arena: &mut Arena<H>) {
        // add a level for let bindings and move before the bindings opening
        // remember where the bindings start in the arena
        self.levels.push(Level::LetBinding {
            arena_text_start: arena.text.len(),
            arena_names_start: arena.symbols.len(),
            arena_terms_start: arena.terms.len(),
        });
        self.state = State::LetAllBindingsOpen;
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
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: Token,
        open_fn: impl Fn(&mut H, SmtSymbolView<'_>, H::Sort) -> Result<(), H::Error>,
    ) -> Result<ControlFlow<u64>, ParserError<H::Error>> {
        let this = &mut resources.term_slot.sorted_bindings_parser;
        let token = match this.state {
            SortedBindingsParserState::Start => {
                // expect an opening parenthesis
                OpenParenParser::expect(token)?;
                this.state = SortedBindingsParserState::AwaitingBinder;
                return Ok(ControlFlow::Continue(()));
            }
            SortedBindingsParserState::AwaitingBinder => {
                // either a new sorted variable
                // or a closing parenthesis ending binders
                if matches!(token.ty(), TokenType::ParenClose) {
                    let num_opened = this.num_opened;
                    // reset before break
                    this.state = SortedBindingsParserState::Start;
                    this.num_opened = 0;
                    return Ok(ControlFlow::Break(num_opened));
                }
                // parse the binder
                this.state = SortedBindingsParserState::ParsingBinder;
                token
            }
            SortedBindingsParserState::ParsingBinder => token,
        };

        // parse the sorted variable
        let span = token.span();
        match resources.sorted_var_slot.progress(
            handler,
            &mut resources.arena,
            &mut resources.sort_slot,
            &mut resources.ident_slot,
            token,
        )? {
            ControlFlow::Continue(()) => {}
            ControlFlow::Break((name, sort)) => {
                // start the binder with the name handed over, and increment opened
                resources
                    .arena
                    .hand_over_sorted_var(name, sort, |name, sort| {
                        handle_err(open_fn(handler, name, sort), span)
                    })?;
                this.num_opened += 1;
                // go back to awaiting a binder
                this.state = SortedBindingsParserState::AwaitingBinder;
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

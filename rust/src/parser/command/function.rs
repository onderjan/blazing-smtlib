use std::ops::ControlFlow;

use crate::{
    SmtCommandHandler, SmtFunctionSignature,
    parser::{
        SmtPairParser, SmtParenMaximumParser, SmtParenMultipleParser, SmtParenParser,
        SmtParenSortedVarsParser, SmtParse, SmtParseError, SmtParseState, SmtSortParser,
        SmtSymbolParser, SmtSyntaxErrorKind, SmtTermParser, handle_err, parse_by_token,
    },
    token::{SingleTokenProducer, SmtProduce},
};

/// Parses a function signature: name, parameters (name and sort), and result sort.
pub(super) struct FunctionSignatureParser<H: SmtCommandHandler> {
    inner: SmtPairParser<
        H,
        SmtSymbolParser,
        SmtPairParser<H, SmtParenSortedVarsParser<H>, SmtSortParser<H>>,
    >,
}

impl<H: SmtCommandHandler> FunctionSignatureParser<H> {
    fn new() -> Self {
        Self {
            inner: SmtPairParser::default(),
        }
    }
}

impl<H: SmtCommandHandler> Default for FunctionSignatureParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for FunctionSignatureParser<H> {
    type Result = SmtFunctionSignature<H>;

    fn parse<C: SmtProduce>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<SmtFunctionSignature<H>>, SmtParseError<H::Error>> {
        Ok(self.inner.parse(handler, parse_state, cursor)?.map_break(
            |(name, (params, result_sort))| SmtFunctionSignature {
                name,
                params,
                result_sort,
            },
        ))
    }
}

/// Parses a function body inside `define-funs-rec` or `define-fun-rec`, calling the handler for its start and end.
pub(super) struct RecursiveBodyParser<H: SmtCommandHandler> {
    is_inner: bool,
    term_parser: SmtTermParser<H>,
}

impl<H: SmtCommandHandler> RecursiveBodyParser<H> {
    fn new() -> Self {
        Self {
            is_inner: false,
            term_parser: SmtTermParser::new(),
        }
    }
}

impl<H: SmtCommandHandler> Default for RecursiveBodyParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for RecursiveBodyParser<H> {
    type Result = ();

    fn parse<C: SmtProduce>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        parse_by_token(cursor, |cursor, token| {
            self.progress(handler, parse_state, cursor, token)
        })
    }
}

impl<H: SmtCommandHandler> RecursiveBodyParser<H> {
    /// Progresses the parser by one token.
    fn progress<Z: SmtProduce>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &Z,
        token: Z::Token,
    ) -> Result<ControlFlow<()>, SmtParseError<H::Error>> {
        if !self.is_inner {
            // signal the handler that we are starting a body term
            handle_err(handler.start_recursive_body())?;
            self.is_inner = true;
        }

        match self.term_parser.parse(
            handler,
            parse_state,
            &mut SingleTokenProducer::new(cursor, token),
        )? {
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(term) => {
                // signal the handler that the body term has ended
                handle_err(handler.end_recursive_body(term))?;
                // reset and break
                self.is_inner = false;
                Ok(ControlFlow::Break(()))
            }
        }
    }
}

/// Parser of parameters of the command `define-funs-rec`.
///
/// The commands using this parser do not call the
/// handler after ending, as everything is handled by the parser.
pub(super) struct DefineFunsRecParser<H: SmtCommandHandler> {
    state: DefineFunsRecState,

    signatures_parser: SmtParenMultipleParser<H, SmtParenParser<H, FunctionSignatureParser<H>>>,
    bodies_parser: SmtParenMaximumParser<H, RecursiveBodyParser<H>>,
}

enum DefineFunsRecState {
    Signatures,
    Bodies,
}

impl<H: SmtCommandHandler> DefineFunsRecParser<H> {
    pub fn new() -> Self {
        // the number of maximum elements for bodies parser will be
        // resized before each parse, it does not matter in the initial state
        Self {
            state: DefineFunsRecState::Signatures,
            signatures_parser: SmtParenMultipleParser::default(),
            bodies_parser: SmtParenMaximumParser::new(RecursiveBodyParser::new(), 0),
        }
    }
}

impl<H: SmtCommandHandler> Default for DefineFunsRecParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtCommandHandler> SmtParse<H> for DefineFunsRecParser<H> {
    type Result = ();

    fn parse<C: SmtProduce>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &mut C,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<H::Error>> {
        parse_by_token(cursor, |cursor, token| {
            self.progress(handler, parse_state, cursor, token)
        })
    }
}

impl<H: SmtCommandHandler> DefineFunsRecParser<H> {
    /// Progresses the parser by one token.
    fn progress<Z: SmtProduce>(
        &mut self,
        handler: &mut H,
        parse_state: &mut SmtParseState<H>,
        cursor: &Z,
        token: Z::Token,
    ) -> Result<ControlFlow<()>, SmtParseError<H::Error>> {
        match self.state {
            DefineFunsRecState::Signatures => {
                // parse the signatures
                if let ControlFlow::Break(signatures) = self.signatures_parser.parse(
                    handler,
                    parse_state,
                    &mut SingleTokenProducer::new(cursor, token),
                )? {
                    // there must be at least one signature
                    if signatures.is_empty() {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::EmptyFunctionSignatures,
                        ));
                    }

                    // remember how many signatures we have and set it as a maximum for bodies
                    self.bodies_parser.set_maximum(signatures.len());

                    // start recursive function bodies in the handler, passing the signatures
                    handle_err(handler.start_define_funs_rec(signatures))?;
                    // move to parsing the bodies
                    self.state = DefineFunsRecState::Bodies;
                }
            }
            DefineFunsRecState::Bodies => {
                // parse bodies
                if let ControlFlow::Break(bodies) = self.bodies_parser.parse(
                    handler,
                    parse_state,
                    &mut SingleTokenProducer::new(cursor, token),
                )? {
                    // the parser returned a vector of units corresponding to the number of bodies
                    // bounded by the maximum which is the number of signatures
                    if bodies.len() != self.bodies_parser.max_elements() {
                        // not enough bodies processed
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::ExpectedFunctionBody,
                        ));
                    }

                    // end the recursive function definitions in the handler, reset, and break
                    // the bodies parser can have a changed number of maximum elements,
                    // but it will be changed before it is used next time
                    handle_err(handler.end_define_funs_rec())?;
                    self.state = DefineFunsRecState::Signatures;
                    return Ok(ControlFlow::Break(()));
                }
            }
        }

        Ok(ControlFlow::Continue(()))
    }
}

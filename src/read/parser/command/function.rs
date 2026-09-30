use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtFunctionSignature,
    read::parser::{
        SyntaxErrorKind, Parser, PairParser, ParenMaximumParser, ParenMultipleParser,
        ParenParser, ParenSortedVarsParser, ParserError, ParserResources, SortParser, SymbolParser,
        TermParser, handle_err,
    },
    token::Token,
};

/// Parses a function signature: name, parameters (name and sort), and result sort.
pub(super) struct FunctionSignatureParser<H: CommandHandler> {
    inner: PairParser<H, SymbolParser, PairParser<H, ParenSortedVarsParser<H>, SortParser<H>>>,
}

impl<H: CommandHandler> FunctionSignatureParser<H> {
    fn new() -> Self {
        Self {
            inner: PairParser::default(),
        }
    }
}

impl<H: CommandHandler> Default for FunctionSignatureParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler> Parser<H> for FunctionSignatureParser<H> {
    type Result = SmtFunctionSignature<H>;

    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: Token,
    ) -> Result<ControlFlow<SmtFunctionSignature<H>>, ParserError<H::Error>> {
        Ok(self.inner.progress(handler, resources, token)?.map_break(
            |(name, (params, result_sort))| SmtFunctionSignature {
                name,
                params,
                result_sort,
            },
        ))
    }
}

/// Parses a function body inside `define-funs-rec` or `define-fun-rec`, calling the handler for its start and end.
pub(super) struct RecursiveBodyParser<H: CommandHandler> {
    is_inner: bool,
    term_parser: TermParser<H>,
}

impl<H: CommandHandler> RecursiveBodyParser<H> {
    fn new() -> Self {
        Self {
            is_inner: false,
            term_parser: TermParser::new(),
        }
    }
}

impl<H: CommandHandler> Default for RecursiveBodyParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler> Parser<H> for RecursiveBodyParser<H> {
    type Result = ();

    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        let span = token.span();
        if !self.is_inner {
            // signal the handler that we are starting a body term
            handle_err(handler.start_recursive_body(), span)?;
            self.is_inner = true;
        }

        match self.term_parser.progress(handler, resources, token)? {
            ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
            ControlFlow::Break(term) => {
                // signal the handler that the body term has ended
                handle_err(handler.end_recursive_body(term), span)?;
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
pub(super) struct DefineFunsRecParser<H: CommandHandler> {
    state: DefineFunsRecState,

    signatures_parser: ParenMultipleParser<H, ParenParser<H, FunctionSignatureParser<H>>>,
    bodies_parser: ParenMaximumParser<H, RecursiveBodyParser<H>>,
}

enum DefineFunsRecState {
    Signatures,
    Bodies,
}

impl<H: CommandHandler> DefineFunsRecParser<H> {
    pub fn new() -> Self {
        // the number of maximum elements for bodies parser will be
        // resized before each parse, it does not matter in the initial state
        Self {
            state: DefineFunsRecState::Signatures,
            signatures_parser: ParenMultipleParser::default(),
            bodies_parser: ParenMaximumParser::new(RecursiveBodyParser::new(), 0),
        }
    }
}

impl<H: CommandHandler> Default for DefineFunsRecParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler> Parser<H> for DefineFunsRecParser<H> {
    type Result = ();

    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        let span = token.span();
        match self.state {
            DefineFunsRecState::Signatures => {
                // parse the signatures
                if let ControlFlow::Break(signatures) =
                    self.signatures_parser.progress(handler, resources, token)?
                {
                    // there must be at least one signature
                    if signatures.is_empty() {
                        return Err(ParserError::category_error(
                            SyntaxErrorKind::EmptyFunctionSignatures,
                            span,
                        ));
                    }

                    // remember how many signatures we have and set it as a maximum for bodies
                    self.bodies_parser.set_maximum(signatures.len());

                    // start recursive function bodies in the handler, passing the signatures
                    handle_err(handler.start_define_funs_rec(signatures), span)?;
                    // move to parsing the bodies
                    self.state = DefineFunsRecState::Bodies;
                }
            }
            DefineFunsRecState::Bodies => {
                // parse bodies
                if let ControlFlow::Break(bodies) =
                    self.bodies_parser.progress(handler, resources, token)?
                {
                    // the parser returned a vector of units corresponding to the number of bodies
                    // bounded by the maximum which is the number of signatures
                    if bodies.len() != self.bodies_parser.max_elements() {
                        // not enough bodies processed
                        return Err(ParserError::category_error(
                            SyntaxErrorKind::ExpectedFunctionBody,
                            span,
                        ));
                    }

                    // end the recursive function definitions in the handler, reset, and break
                    // the bodies parser can have a changed number of maximum elements,
                    // but it will be changed before it is used next time
                    handle_err(handler.end_define_funs_rec(), span)?;
                    self.state = DefineFunsRecState::Signatures;
                    return Ok(ControlFlow::Break(()));
                }
            }
        }

        Ok(ControlFlow::Continue(()))
    }
}

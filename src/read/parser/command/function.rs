use std::ops::ControlFlow;

use crate::{
    CommandHandler, SmtFunctionSignature,
    read::parser::{
        CategoryErrorKind, CategoryParser, PairParser, ParenMaximumParser, ParenMultipleParser,
        ParenParser, ParenSortedVarsParser, ParserError, SortParser, SymbolParser, TermParser,
        handle_err,
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
            inner: PairParser::new(),
        }
    }
}

impl<H: CommandHandler> Default for FunctionSignatureParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler> CategoryParser<H> for FunctionSignatureParser<H> {
    type Result = SmtFunctionSignature<H>;

    fn restart(&mut self) {
        self.inner.restart();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: &Token,
    ) -> Result<ControlFlow<SmtFunctionSignature<H>>, ParserError<H::Error>> {
        Ok(self
            .inner
            .progress(handler, token)?
            .map_break(|(name, (params, result_sort))| SmtFunctionSignature {
                name,
                params,
                result_sort,
            }))
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

impl<H: CommandHandler> CategoryParser<H> for RecursiveBodyParser<H> {
    type Result = ();

    fn restart(&mut self) {
        self.is_inner = false;
        self.term_parser.restart();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: &Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        let span = token.span();
        if !self.is_inner {
            // signal the handler that we are starting a body term
            handle_err(handler.start_recursive_body(), span)?;
            self.is_inner = true;
        }

        match self.term_parser.progress(handler, token)? {
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
    num_signatures: usize,

    signatures_parser: ParenMultipleParser<H, ParenParser<H, FunctionSignatureParser<H>>>,
    bodies_parser: ParenMaximumParser<H, RecursiveBodyParser<H>>,
}

enum DefineFunsRecState {
    Signatures,
    Bodies,
}

impl<H: CommandHandler> DefineFunsRecParser<H> {
    pub fn new() -> Self {
        Self {
            state: DefineFunsRecState::Signatures,
            num_signatures: 0,
            signatures_parser: ParenMultipleParser::new(),
            bodies_parser: ParenMaximumParser::new(),
        }
    }
}

impl<H: CommandHandler> Default for DefineFunsRecParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: CommandHandler> CategoryParser<H> for DefineFunsRecParser<H> {
    type Result = ();

    fn restart(&mut self) {
        self.state = DefineFunsRecState::Signatures;
        self.num_signatures = 0;
        self.signatures_parser.restart();
        self.bodies_parser.start(0);
    }

    fn progress(
        &mut self,
        handler: &mut H,
        token: &Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<H::Error>> {
        let span = token.span();
        match self.state {
            DefineFunsRecState::Signatures => {
                // parse the signatures
                if let ControlFlow::Break(signatures) =
                    self.signatures_parser.progress(handler, token)?
                {
                    // there must be at least one signature
                    if signatures.is_empty() {
                        return Err(ParserError::category_error(
                            CategoryErrorKind::EmptyFunctionSignatures,
                            span,
                        ));
                    }

                    // remember how many signatures we have and set it as a maximum for bodies
                    self.num_signatures = signatures.len();
                    self.bodies_parser.start(self.num_signatures);

                    // start recursive function bodies in the handler, passing the signatures
                    handle_err(handler.start_define_funs_rec(signatures), span)?;
                    // move to parsing the bodies
                    self.state = DefineFunsRecState::Bodies;
                }
            }
            DefineFunsRecState::Bodies => {
                // parse bodies
                if let ControlFlow::Break(bodies) = self.bodies_parser.progress(handler, token)? {
                    // the parser returned a vector of units corresponding to the number of bodies
                    // bounded by the maximum which is the number of signatures
                    if bodies.len() != self.num_signatures {
                        // not enough bodies processed
                        return Err(ParserError::category_error(
                            CategoryErrorKind::ExpectedFunctionBody,
                            span,
                        ));
                    }

                    // end the recursive function definitions in the handler, reset, and break
                    handle_err(handler.end_define_funs_rec(), span)?;
                    self.state = DefineFunsRecState::Signatures;
                    self.num_signatures = 0;
                    return Ok(ControlFlow::Break(()));
                }
            }
        }

        Ok(ControlFlow::Continue(()))
    }
}

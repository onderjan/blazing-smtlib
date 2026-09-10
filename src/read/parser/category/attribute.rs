use std::ops::ControlFlow;

use crate::{
    SmtAttributeValue, SmtHandler, SmtKeyword, SmtSpan,
    read::parser::{
        CloseParenParser, ClosedMultipleParser, ParserError, ParserResources,
        category::{
            CategoryErrorKind, CategoryParser, parse_special_constant, s_expr::SExprParser,
        },
        handle_err,
    },
    token::{Token, TokenKind, TokenType},
};

/// A parser that reads an SMT-LIB attribute followed by a closing parenthesis.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct ClosedAttributeParser<H: SmtHandler>(CollectingParser<H, SingleAttribute<H>>);

/// A parser that reads multiple SMT-LIB attributes followed by a closing parenthesis.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct ClosedMultipleAttributeParser<H: SmtHandler>(CollectingParser<H, MultipleAttributes<H>>);

struct CollectingParser<H: SmtHandler, C: AttributeCollection<H>> {
    /// Current state.
    state: State,

    /// Collection of processed attributes.
    collection: C,

    closed_s_exprs_parser: ClosedMultipleParser<H, SExprParser<H>>,
}

trait AttributeCollection<H: SmtHandler>: Default {
    type Output;
    fn next_allowed(&self) -> bool;
    fn reset(&mut self);
    fn push(&mut self, attribute: H::Attribute);
    fn finish(&mut self, span: SmtSpan) -> Result<Self::Output, ParserError<H::Error>>;
}

/// Attribute-parsing state.
enum State {
    /// Waiting for the keyword that will name the next attribute.
    Start,
    /// Waiting for a value or a closing parenthesis.
    AfterName(SmtKeyword),
    /// Parsing S-expressions that will end with a closing parenthesis.
    InsideSExpr(SmtKeyword),
}

impl<H: SmtHandler, C: AttributeCollection<H>> CollectingParser<H, C> {
    pub fn new() -> Self {
        Self {
            state: State::Start,
            collection: C::default(),
            closed_s_exprs_parser: ClosedMultipleParser::default(),
        }
    }
}

impl<H: SmtHandler, C: AttributeCollection<H>> Default for CollectingParser<H, C> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler, C: AttributeCollection<H>> CategoryParser<H> for CollectingParser<H, C> {
    type Result = C::Output;

    fn restart(&mut self) {
        self.state = State::Start;
        self.collection.reset();
        self.closed_s_exprs_parser.restart();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources,
        token: &Token,
    ) -> Result<ControlFlow<C::Output>, ParserError<H::Error>> {
        let span = token.span();
        if !self.collection.next_allowed() {
            // no more attributes are allowed, just expect a closing parenthesis
            CloseParenParser::expect(token)?;
            return Ok(ControlFlow::Break(self.collection.finish(span)?));
        }

        let mut state = State::Start;
        std::mem::swap(&mut state, &mut self.state);

        match state {
            State::Start => {
                match token.kind() {
                    TokenKind::ParenClose => {
                        // finish the attribute
                        return Ok(ControlFlow::Break(self.collection.finish(span)?));
                    }
                    TokenKind::Keyword(keyword) => {
                        // we received an attribute name, handle it
                        self.state = State::AfterName(keyword.into_owned());
                    }
                    _ => {
                        return Err(ParserError::category_error(
                            CategoryErrorKind::ExpectedAttribute,
                            span,
                        ));
                    }
                }
            }
            State::AfterName(name) => {
                enum Decision {
                    FinishAttribute,
                    StartNextAttribute(SmtKeyword),
                    Break,
                }

                let (value, decision) = match token.kind() {
                    TokenKind::Symbol(symbol) => (
                        Some(SmtAttributeValue::Symbol(symbol.into_owned())),
                        Decision::FinishAttribute,
                    ),
                    TokenKind::ParenOpen => {
                        // start a list of sexprs ending with closing parenthesis
                        self.state = State::InsideSExpr(name);
                        return Ok(ControlFlow::Continue(()));
                    }
                    TokenKind::ParenClose => {
                        // an attribute with only a name followed by the parenthesis
                        // since we already have a closing parenthesis here,
                        // we need to immediately finish after pushing the attribute
                        (None, Decision::Break)
                    }
                    TokenKind::Keyword(keyword) => {
                        // the current attribute was just a name
                        // the new state will be after the new name given by the keyword
                        // push the previous attribute to the collection,

                        (None, Decision::StartNextAttribute(keyword.into_owned()))
                    }
                    kind => {
                        if let Ok(special_constant) = parse_special_constant(kind) {
                            (
                                Some(SmtAttributeValue::SpecialConstant(special_constant)),
                                Decision::FinishAttribute,
                            )
                        } else {
                            return Err(ParserError::category_error(
                                CategoryErrorKind::ExpectedAttribute,
                                span,
                            ));
                        }
                    }
                };

                // handle the attribute and push to the collection
                let result = handle_err(handler.handle_attribute(name, value), span)?;
                self.collection.push(result);
                // if we received a closing parenthesis, we need to finish immediately
                match decision {
                    Decision::FinishAttribute => {
                        // fine, fall through
                    }
                    Decision::Break => {
                        // break
                        return Ok(ControlFlow::Break(self.collection.finish(span)?));
                    }
                    Decision::StartNextAttribute(keyword) => {
                        // check if we actually can start a next keyword
                        if !self.collection.next_allowed() {
                            // it turns out that we actually expected a closing parenthesis
                            return Err(ParserError::category_error(
                                CategoryErrorKind::ExpectedToken(&[TokenType::ParenClose]),
                                span,
                            ));
                        }
                        // move after name
                        self.state = State::AfterName(keyword);
                    }
                }
            }
            State::InsideSExpr(name) => {
                match self
                    .closed_s_exprs_parser
                    .progress(handler, resources, token)?
                {
                    ControlFlow::Continue(()) => {
                        // put the state back
                        self.state = State::InsideSExpr(name);
                    }
                    ControlFlow::Break(s_exprs) => {
                        // the s-expr closing parenthesis was consumed,
                        // the attribute closing parenthesis was not consumed yet
                        // we must keep the attribute for now
                        let value = SmtAttributeValue::SExprs(s_exprs);
                        let attribute =
                            handle_err(handler.handle_attribute(name, Some(value)), span)?;
                        // no additional reset steps necessary, as the state has already been replaced
                        // by Start and the SExpr parser is untouched
                        self.collection.push(attribute);
                    }
                }
            }
        }

        Ok(ControlFlow::Continue(()))
    }
}

struct SingleAttribute<H: SmtHandler>(Option<H::Attribute>);

impl<H: SmtHandler> Default for SingleAttribute<H> {
    fn default() -> Self {
        Self(None)
    }
}

impl<H: SmtHandler> AttributeCollection<H> for SingleAttribute<H> {
    type Output = H::Attribute;

    fn next_allowed(&self) -> bool {
        self.0.is_none()
    }

    fn reset(&mut self) {
        self.0 = None;
    }

    fn push(&mut self, attribute: H::Attribute) {
        // the progress function is responsible for ensuring
        // this is not called when next_allowed() is false
        self.0 = Some(attribute);
    }

    fn finish(&mut self, span: SmtSpan) -> Result<Self::Output, ParserError<H::Error>> {
        match self.0.take() {
            Some(attribute) => Ok(attribute),
            None => Err(ParserError::category_error(
                CategoryErrorKind::ExpectedAttribute,
                span,
            )),
        }
    }
}

struct MultipleAttributes<H: SmtHandler>(Vec<H::Attribute>);

impl<H: SmtHandler> Default for MultipleAttributes<H> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<H: SmtHandler> AttributeCollection<H> for MultipleAttributes<H> {
    type Output = Vec<H::Attribute>;

    fn next_allowed(&self) -> bool {
        true
    }

    fn reset(&mut self) {
        self.0.clear();
    }

    fn push(&mut self, attribute: H::Attribute) {
        self.0.push(attribute);
    }

    fn finish(&mut self, _span: SmtSpan) -> Result<Self::Output, ParserError<H::Error>> {
        let mut result = Vec::new();
        std::mem::swap(&mut self.0, &mut result);
        Ok(result)
    }
}

// mechanical newtype impls

impl<H: SmtHandler> ClosedAttributeParser<H> {
    pub fn new() -> Self {
        Self(CollectingParser::new())
    }
}

impl<H: SmtHandler> Default for ClosedAttributeParser<H> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<H: SmtHandler> CategoryParser<H> for ClosedAttributeParser<H> {
    type Result = H::Attribute;

    fn restart(&mut self) {
        self.0.restart();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources,
        token: &Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<<H as SmtHandler>::Error>> {
        self.0.progress(handler, resources, token)
    }
}

impl<H: SmtHandler> ClosedMultipleAttributeParser<H> {
    pub fn new() -> Self {
        Self(CollectingParser::new())
    }
}

impl<H: SmtHandler> Default for ClosedMultipleAttributeParser<H> {
    fn default() -> Self {
        Self(Default::default())
    }
}

impl<H: SmtHandler> CategoryParser<H> for ClosedMultipleAttributeParser<H> {
    type Result = Vec<H::Attribute>;

    fn restart(&mut self) {
        self.0.restart();
    }

    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources,
        token: &Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<<H as SmtHandler>::Error>> {
        self.0.progress(handler, resources, token)
    }
}

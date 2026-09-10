use std::ops::ControlFlow;

use crate::{
    SmtAttributeValue, SmtHandler, SmtKeyword, SmtSpan,
    read::parser::{
        CloseParenParser, ParserError, ParserResources, SExprSlot,
        category::{
            CategoryErrorKind, CategoryParser, parse_special_constant,
            resources::ClosedMultipleResource,
        },
        handle_err,
    },
    token::{Token, TokenKind, TokenType},
};

/// A parser that reads an SMT-LIB attribute followed by a closing parenthesis.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct ClosedAttributeParser<H: SmtHandler> {
    _priv: std::marker::PhantomData<H>,
}

impl<H: SmtHandler> ClosedAttributeParser<H> {
    pub fn new() -> Self {
        Self {
            _priv: std::marker::PhantomData,
        }
    }
}

impl<H: SmtHandler> Default for ClosedAttributeParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for ClosedAttributeParser<H> {
    type Result = H::Attribute;

    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<<H as SmtHandler>::Error>> {
        resources.attribute_slot.progress::<SingleAttribute>(
            handler,
            &mut resources.s_expr_slot,
            token,
        )
    }
}

/// A parser that reads multiple SMT-LIB attributes followed by a closing parenthesis.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct ClosedMultipleAttributeParser<H: SmtHandler> {
    _priv: std::marker::PhantomData<H>,
}

impl<H: SmtHandler> ClosedMultipleAttributeParser<H> {
    pub fn new() -> Self {
        Self {
            _priv: std::marker::PhantomData,
        }
    }
}

impl<H: SmtHandler> Default for ClosedMultipleAttributeParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for ClosedMultipleAttributeParser<H> {
    type Result = Vec<H::Attribute>;

    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<ControlFlow<Self::Result>, ParserError<<H as SmtHandler>::Error>> {
        resources.attribute_slot.progress::<MultipleAttributes>(
            handler,
            &mut resources.s_expr_slot,
            token,
        )
    }
}

trait AttributeCollection<H: SmtHandler> {
    type Output;

    fn next_allowed(num_elements: usize) -> bool;

    fn finish(
        attributes: &mut Vec<H::Attribute>,
        span: SmtSpan,
    ) -> Result<Self::Output, ParserError<H::Error>>;
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

pub(crate) struct AttributeSlot<H: SmtHandler + ?Sized> {
    state: State,
    attributes: Vec<H::Attribute>,
    s_exprs: ClosedMultipleResource<H::SExpr>,
}

impl<H: SmtHandler + ?Sized> AttributeSlot<H> {
    pub(crate) fn new() -> Self {
        Self {
            state: State::Start,
            attributes: Vec::new(),
            s_exprs: ClosedMultipleResource::new(),
        }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        matches!(self.state, State::Start)
            && self.attributes.is_empty()
            && self.s_exprs.is_pristine()
    }

    pub(crate) fn clear(&mut self) {
        self.state = State::Start;
        self.attributes.clear();
        self.s_exprs.clear();
    }
}

impl<H: SmtHandler> AttributeSlot<H> {
    fn progress<C: AttributeCollection<H>>(
        &mut self,
        handler: &mut H,
        s_expr_slot: &mut SExprSlot<H>,
        token: &Token,
    ) -> Result<ControlFlow<C::Output>, ParserError<H::Error>> {
        let span = token.span();
        if !C::next_allowed(self.attributes.len()) {
            // no more attributes are allowed, just expect a closing parenthesis
            CloseParenParser::expect(token)?;
            return Ok(ControlFlow::Break(C::finish(&mut self.attributes, span)?));
        }

        let mut state = State::Start;
        std::mem::swap(&mut state, &mut self.state);

        match state {
            State::Start => {
                if self.attributes.is_empty() {
                    debug_assert!(self.is_pristine(), "must be pristine when starting");
                }
                match token.kind() {
                    TokenKind::ParenClose => {
                        // finish the attribute
                        return Ok(ControlFlow::Break(C::finish(&mut self.attributes, span)?));
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
                self.attributes.push(result);
                // if we received a closing parenthesis, we need to finish immediately
                match decision {
                    Decision::FinishAttribute => {
                        // fine, fall through
                    }
                    Decision::Break => {
                        // break
                        return Ok(ControlFlow::Break(C::finish(&mut self.attributes, span)?));
                    }
                    Decision::StartNextAttribute(keyword) => {
                        // check if we actually can start a next keyword
                        if !C::next_allowed(self.attributes.len()) {
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
                // progress s_exprs, which progress SExpr as an element
                match self
                    .s_exprs
                    .progress(token, |token| s_expr_slot.progress(handler, token))?
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
                        self.attributes.push(attribute);
                    }
                }
            }
        }

        Ok(ControlFlow::Continue(()))
    }
}

struct SingleAttribute;

impl<H: SmtHandler> AttributeCollection<H> for SingleAttribute {
    type Output = H::Attribute;

    fn next_allowed(num_elements: usize) -> bool {
        num_elements == 0
    }

    fn finish(
        attributes: &mut Vec<H::Attribute>,
        span: SmtSpan,
    ) -> Result<Self::Output, ParserError<H::Error>> {
        debug_assert!(
            attributes.len() <= 1,
            "at most one attribute should be parsed"
        );

        match attributes.drain(..).next() {
            Some(attribute) => Ok(attribute),
            None => Err(ParserError::category_error(
                CategoryErrorKind::ExpectedAttribute,
                span,
            )),
        }
    }
}

struct MultipleAttributes;

impl<H: SmtHandler> AttributeCollection<H> for MultipleAttributes {
    type Output = Vec<H::Attribute>;

    fn next_allowed(_num_elements: usize) -> bool {
        true
    }

    fn finish(
        attributes: &mut Vec<H::Attribute>,
        _span: SmtSpan,
    ) -> Result<Self::Output, ParserError<H::Error>> {
        Ok(std::mem::take(attributes))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CheckStandardSyntax, read::parser::category::tests::parse_all_with};

    #[test]
    fn slot_is_pristine_after_every_attribute_list() {
        // every value shape (none, symbol, constant, s-expression list) uses the
        // attribute slot and the s-expression list it owns; the slot must be back
        // in its initial state after a single attribute and after several
        for input in [
            &b":flag)"[..],
            b":named x)",
            b":weight 3)",
            b":pattern ((f x) y))",
        ] {
            let mut resources = ParserResources::new();
            parse_all_with(
                ClosedAttributeParser::<CheckStandardSyntax>::new(),
                &mut resources,
                input,
            );
            assert!(resources.are_pristine(), "after {input:?}");
        }
        for input in [
            &b":a x :b (1 (2 3)) :c)"[..],
            b":pattern ((f x)) :qid q)",
            b")",
        ] {
            let mut resources = ParserResources::new();
            parse_all_with(
                ClosedMultipleAttributeParser::<CheckStandardSyntax>::new(),
                &mut resources,
                input,
            );
            assert!(resources.are_pristine(), "after {input:?}");
        }
    }
}

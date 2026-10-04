use std::ops::ControlFlow;

use crate::{
    SmtAttributeValue, SmtHandler, SmtKeywordView, SmtSpan,
    read::parser::{
        Arena, SExprSlot, SmtCloseParenParser, SmtParse, SmtParseError, SmtParseState,
        SmtSyntaxErrorKind, TextHandle, category::parse_special_constant, handle_err,
        parse_by_token,
    },
    token::{SmtBatchCursor, SmtSyntaxToken, SmtToken, SmtTokenCategory, SmtVersion},
};

/// A parser that reads an SMT-LIB attribute followed by a closing parenthesis.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct SmtClosedAttributeParser<H: SmtHandler> {
    _priv: std::marker::PhantomData<H>,
}

impl<H: SmtHandler> SmtClosedAttributeParser<H> {
    pub fn new() -> Self {
        Self {
            _priv: std::marker::PhantomData,
        }
    }
}

impl<H: SmtHandler> Default for SmtClosedAttributeParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> SmtParse<H> for SmtClosedAttributeParser<H> {
    type Result = H::Attribute;

    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut SmtParseState<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<<H as SmtHandler>::Error>> {
        let SmtParseState {
            attribute_slot,
            arena,
            s_expr_slot,
            ..
        } = resources;
        parse_by_token(cursor, |version, token| {
            attribute_slot.progress::<H, SingleAttribute>(
                handler,
                arena,
                s_expr_slot,
                version,
                token,
            )
        })
    }
}

/// A parser that reads multiple SMT-LIB attributes followed by a closing parenthesis.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct SmtClosedMultipleAttributeParser<H: SmtHandler> {
    _priv: std::marker::PhantomData<H>,
}

impl<H: SmtHandler> SmtClosedMultipleAttributeParser<H> {
    pub fn new() -> Self {
        Self {
            _priv: std::marker::PhantomData,
        }
    }
}

impl<H: SmtHandler> Default for SmtClosedMultipleAttributeParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> SmtParse<H> for SmtClosedMultipleAttributeParser<H> {
    type Result = Vec<H::Attribute>;

    fn parse(
        &mut self,
        handler: &mut H,
        resources: &mut SmtParseState<H>,
        cursor: &mut SmtBatchCursor,
    ) -> Result<ControlFlow<Self::Result>, SmtParseError<<H as SmtHandler>::Error>> {
        let SmtParseState {
            attribute_slot,
            arena,
            s_expr_slot,
            ..
        } = resources;
        parse_by_token(cursor, |version, token| {
            match attribute_slot.progress::<H, MultipleAttributes>(
                handler,
                arena,
                s_expr_slot,
                version,
                token,
            )? {
                ControlFlow::Continue(()) => Ok(ControlFlow::Continue(())),
                ControlFlow::Break(start) => {
                    // the attributes are at the end of the arena, hand them over
                    Ok(ControlFlow::Break(
                        arena.hand_over_attributes(start, |attributes| {
                            attributes.into_iter().collect()
                        }),
                    ))
                }
            }
        })
    }
}

pub(crate) trait AttributeCollection<H: SmtHandler + ?Sized> {
    type Output;

    /// Determines if it is allowed to add another element.
    fn next_allowed(num_elements: usize) -> bool;

    /// Finishes the collection of the attributes stored in the arena from `start` onward.
    fn finish(
        arena: &mut Arena<H>,
        start: usize,
        span: SmtSpan,
    ) -> Result<Self::Output, SmtParseError<H::Error>>;
}

/// Attribute-parsing state.
enum State {
    /// Waiting for the keyword that will name the next attribute.
    Start,
    /// Waiting for a value or a closing parenthesis.
    ///
    /// The name is stored in the arena text.
    AfterName(TextHandle),
    /// Parsing S-expressions that will end with a closing parenthesis.
    InsideSExpr {
        /// The name, stored in the arena text.
        name: TextHandle,
        /// The S-expressions are stored in the arena starting at this position.
        arena_s_exprs_start: usize,
        /// Whether we are between S-expressions, where a closing parenthesis ends them.
        outside: bool,
    },
}

pub(crate) struct AttributeSlot {
    state: State,
    /// The number of attributes handled so far.
    num_attributes: usize,
    /// The handled attributes are stored in the arena starting at this position.
    arena_attributes_start: usize,
}

impl AttributeSlot {
    pub(crate) fn new() -> Self {
        Self {
            state: State::Start,
            num_attributes: 0,
            arena_attributes_start: 0,
        }
    }

    pub(crate) fn is_pristine(&self) -> bool {
        matches!(self.state, State::Start) && self.num_attributes == 0
    }

    pub(crate) fn clear(&mut self) {
        self.state = State::Start;
        self.num_attributes = 0;
    }

    pub(crate) fn progress<H: SmtHandler + ?Sized, C: AttributeCollection<H>>(
        &mut self,
        handler: &mut H,
        arena: &mut Arena<H>,
        s_expr_slot: &mut SExprSlot,
        version: SmtVersion,
        token: SmtToken,
    ) -> Result<ControlFlow<C::Output>, SmtParseError<H::Error>> {
        let span = token.span();
        if !C::next_allowed(self.num_attributes) {
            // no more attributes are allowed, just expect a closing parenthesis
            SmtCloseParenParser::expect(token)?;
            return Ok(ControlFlow::Break(self.finish::<H, C>(arena, span)?));
        }

        let mut state = State::Start;
        std::mem::swap(&mut state, &mut self.state);

        match state {
            State::Start => {
                if self.num_attributes == 0 {
                    // the category is being entered, its attributes will start here
                    debug_assert!(self.is_pristine(), "must be pristine when starting");
                    self.arena_attributes_start = arena.attributes.len();
                }
                match token.syntax(version) {
                    SmtSyntaxToken::ParenClose => {
                        // finish the attribute
                        return Ok(ControlFlow::Break(self.finish::<H, C>(arena, span)?));
                    }
                    SmtSyntaxToken::Keyword(keyword) => {
                        // we received an attribute name, store it in the arena text
                        self.state = State::AfterName(arena.push_text(keyword.as_slice()));
                    }
                    _ => {
                        return Err(SmtParseError::category_error(
                            SmtSyntaxErrorKind::ExpectedAttribute,
                            span,
                        ));
                    }
                }
            }
            State::AfterName(name) => {
                enum Decision<'a> {
                    FinishAttribute,
                    StartNextAttribute(SmtKeywordView<'a>),
                    Break,
                }

                let (value, decision) = match token.syntax(version) {
                    SmtSyntaxToken::Symbol(symbol) => (
                        Some(SmtAttributeValue::Symbol(symbol)),
                        Decision::FinishAttribute,
                    ),
                    SmtSyntaxToken::ParenOpen => {
                        // start a list of sexprs ending with closing parenthesis
                        self.state = State::InsideSExpr {
                            name,
                            arena_s_exprs_start: arena.s_exprs.len(),
                            outside: true,
                        };
                        return Ok(ControlFlow::Continue(()));
                    }
                    SmtSyntaxToken::ParenClose => {
                        // an attribute with only a name followed by the parenthesis
                        // since we already have a closing parenthesis here,
                        // we need to immediately finish after pushing the attribute
                        (None, Decision::Break)
                    }
                    SmtSyntaxToken::Keyword(keyword) => {
                        // the current attribute was just a name
                        // the new state will be after the new name given by the keyword
                        // push the previous attribute to the collection,
                        (None, Decision::StartNextAttribute(keyword))
                    }
                    kind => {
                        if let Ok(special_constant) = parse_special_constant(kind) {
                            (
                                Some(SmtAttributeValue::SpecialConstant(special_constant)),
                                Decision::FinishAttribute,
                            )
                        } else {
                            return Err(SmtParseError::category_error(
                                SmtSyntaxErrorKind::ExpectedAttribute,
                                span,
                            ));
                        }
                    }
                };

                // handle the attribute with its name handed over
                let attribute = arena.hand_over_keyword(name, |name| {
                    handle_err(handler.handle_attribute(name, value), span)
                })?;
                // push the handled attribute to the arena
                arena.attributes.push(attribute);
                self.num_attributes += 1;
                // if we received a closing parenthesis, we need to finish immediately
                match decision {
                    Decision::FinishAttribute => {
                        // fine, fall through
                    }
                    Decision::Break => {
                        // break
                        return Ok(ControlFlow::Break(self.finish::<H, C>(arena, span)?));
                    }
                    Decision::StartNextAttribute(keyword) => {
                        // check if we actually can start a next keyword
                        if !C::next_allowed(self.num_attributes) {
                            // it turns out that we actually expected a closing parenthesis
                            return Err(SmtParseError::category_error(
                                SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose]),
                                span,
                            ));
                        }
                        // move after name, stored in the arena text
                        self.state = State::AfterName(arena.push_text(keyword.as_slice()));
                    }
                }
            }
            State::InsideSExpr {
                name,
                arena_s_exprs_start,
                outside,
            } => {
                if outside && matches!(token.category(), SmtTokenCategory::ParenClose) {
                    // the s-expr closing parenthesis was consumed,
                    // the attribute closing parenthesis was not consumed yet
                    // handle the attribute with its name and S-expressions handed over
                    let attribute = arena.hand_over_keyword_s_exprs(
                        name,
                        arena_s_exprs_start,
                        |name, s_exprs| {
                            let value = SmtAttributeValue::SExprs(s_exprs);
                            handle_err(handler.handle_attribute(name, Some(value)), span)
                        },
                    )?;
                    // no additional reset steps necessary, as the state has already been
                    // replaced by Start and the S-expression slot is untouched
                    arena.attributes.push(attribute);
                    self.num_attributes += 1;
                } else {
                    // inside an S-expression, progress it
                    let outside = match s_expr_slot.progress(handler, arena, version, token)? {
                        ControlFlow::Continue(()) => false,
                        ControlFlow::Break(s_expr) => {
                            // push the finished S-expression to its arena
                            arena.s_exprs.push(s_expr);
                            true
                        }
                    };
                    // put the state back
                    self.state = State::InsideSExpr {
                        name,
                        arena_s_exprs_start,
                        outside,
                    };
                }
            }
        }

        Ok(ControlFlow::Continue(()))
    }

    /// Finishes the attribute list, resetting the slot.
    fn finish<H: SmtHandler + ?Sized, C: AttributeCollection<H>>(
        &mut self,
        arena: &mut Arena<H>,
        span: SmtSpan,
    ) -> Result<C::Output, SmtParseError<H::Error>> {
        self.num_attributes = 0;
        C::finish(arena, self.arena_attributes_start, span)
    }
}

struct SingleAttribute;

impl<H: SmtHandler + ?Sized> AttributeCollection<H> for SingleAttribute {
    type Output = H::Attribute;

    fn next_allowed(num_elements: usize) -> bool {
        num_elements == 0
    }

    fn finish(
        arena: &mut Arena<H>,
        start: usize,
        span: SmtSpan,
    ) -> Result<Self::Output, SmtParseError<H::Error>> {
        debug_assert!(
            arena.attributes.len() <= start + 1,
            "at most one attribute should be parsed"
        );

        if arena.attributes.len() == start {
            return Err(SmtParseError::category_error(
                SmtSyntaxErrorKind::ExpectedAttribute,
                span,
            ));
        }
        Ok(arena
            .attributes
            .pop()
            .expect("the single attribute should be in the arena"))
    }
}

pub(crate) struct MultipleAttributes;

impl<H: SmtHandler + ?Sized> AttributeCollection<H> for MultipleAttributes {
    /// Where the attributes start in the arena.
    type Output = usize;

    fn next_allowed(_num_elements: usize) -> bool {
        true
    }

    fn finish(
        _arena: &mut Arena<H>,
        start: usize,
        _span: SmtSpan,
    ) -> Result<Self::Output, SmtParseError<H::Error>> {
        Ok(start)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{SmtSyntaxChecker, read::parser::category::tests::parse_all_with};

    #[test]
    fn slot_is_pristine_after_every_attribute_list() {
        // every value shape (none, symbol, constant, s-expression list) uses the
        // attribute slot and the arena; the slot must be back in its initial
        // state after a single attribute and after several
        for input in [
            &b":flag)"[..],
            b":named x)",
            b":weight 3)",
            b":pattern ((f x) y))",
        ] {
            let mut resources = SmtParseState::new();
            parse_all_with(
                SmtClosedAttributeParser::<SmtSyntaxChecker>::new(),
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
            let mut resources = SmtParseState::new();
            parse_all_with(
                SmtClosedMultipleAttributeParser::<SmtSyntaxChecker>::new(),
                &mut resources,
                input,
            );
            assert!(resources.are_pristine(), "after {input:?}");
        }
    }
}

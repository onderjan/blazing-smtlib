use std::ops::ControlFlow;

use crate::{
    SmtHandler, SmtQualifiedIdent,
    read::parser::{
        ClosedParser, PairParser, ParserError, ParserResources,
        category::{CategoryErrorKind, CategoryParser, ident::IdentParser, sort::SortParser},
    },
    token::{Reserved, Token, TokenKind, TokenType},
};

#[derive(Clone, Copy)]
enum State {
    Start,
    /// After "(".
    Open,
    /// After "(_".
    UnqualifiedIndexed,
    /// After "(as": reads ident, then sort.
    Qualified,
}

/// A parser that reads an SMT-LIB qualified identifier.
///
/// This parser is self-restarting: after returning Break,
/// it is in the default state.
pub struct QualifiedIdentParser<H: SmtHandler> {
    state: State,

    qualified_parser: PairParser<H, IdentParser, ClosedParser<H, SortParser<H>>>,
}

impl<H: SmtHandler> QualifiedIdentParser<H> {
    pub fn new() -> Self {
        Self {
            state: State::Start,
            qualified_parser: PairParser::default(),
        }
    }

    pub fn move_after_open_paren(&mut self) {
        self.state = State::Open;
    }

    pub fn move_after_underscore(&mut self, resources: &mut ParserResources<H>) {
        // the ident parser must be after underscore as well
        resources.ident_slot.move_after_underscore();
        self.state = State::UnqualifiedIndexed;
    }

    pub fn move_after_as(&mut self) {
        self.state = State::Qualified;
    }
}

impl<H: SmtHandler> Default for QualifiedIdentParser<H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<H: SmtHandler> CategoryParser<H> for QualifiedIdentParser<H> {
    type Result = SmtQualifiedIdent<H>;

    fn progress(
        &mut self,
        handler: &mut H,
        resources: &mut ParserResources<H>,
        token: &Token,
    ) -> Result<ControlFlow<SmtQualifiedIdent<H>>, ParserError<H::Error>> {
        let span = token.span();
        match self.state {
            State::Start => match token.kind() {
                TokenKind::Symbol(name) => {
                    // we are in a start state, no need to reset anything

                    // return a simple ident
                    return Ok(ControlFlow::Break(SmtQualifiedIdent::new_simple(
                        name.into_owned(),
                    )));
                }
                TokenKind::ParenOpen => self.state = State::Open,
                _ => {
                    return Err(ParserError::category_error(
                        CategoryErrorKind::ExpectedIdent,
                        span,
                    ));
                }
            },
            State::Open => {
                match token.kind() {
                    TokenKind::Reserved(Reserved::Underscore) => {
                        // unqualified indexed ident
                        // move after underscore
                        resources.ident_slot.move_after_underscore();
                        self.state = State::UnqualifiedIndexed;
                    }
                    TokenKind::Reserved(Reserved::As) => {
                        // qualified ident, parse identifier next
                        self.state = State::Qualified;
                    }
                    _ => {
                        let kind = CategoryErrorKind::ExpectedToken(&[
                            TokenType::Reserved(Reserved::Underscore),
                            TokenType::Reserved(Reserved::As),
                        ]);
                        return Err(ParserError::category_error(kind, span));
                    }
                }
            }
            State::UnqualifiedIndexed => {
                if let ControlFlow::Break(ident) = resources.ident_slot.progress(token)? {
                    // the closing parenthesis was already consumed by the IdentParser

                    // we only need to reset the state:
                    // the ident parser was reset, the qualified parser is untouched
                    self.state = State::Start;

                    // return an unqualified but indexed ident
                    return Ok(ControlFlow::Break(SmtQualifiedIdent::new_unqualified(
                        ident,
                    )));
                }
            }

            State::Qualified => {
                if let ControlFlow::Break((ident, sort)) =
                    self.qualified_parser.progress(handler, resources, token)?
                {
                    // we only need to reset the state:
                    // the ident parser is untouched, the qualified parser was reset
                    self.state = State::Start;

                    // return a qualified ident
                    return Ok(ControlFlow::Break(SmtQualifiedIdent::new_qualified(
                        ident, sort,
                    )));
                }
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
    fn entry_points() {
        // the callers that already consumed `(`, `( _` or `( as` enter the
        // parser in the corresponding state, so it accepts the rest of the
        // qualified identifier
        let mut resources = ParserResources::new();
        let mut parser = QualifiedIdentParser::<CheckStandardSyntax>::new();
        parser.move_after_open_paren();
        let qi = parse_all_with(parser, &mut resources, b"_ f 1)");
        assert_eq!(qi.ident.name.as_slice(), b"f");
        assert_eq!(qi.ident.indices.len(), 1);
        assert!(qi.sort.is_none());
        assert!(resources.are_pristine());

        // regression: the entry point must put the ident slot after the
        // underscore as well, or `f` alone would finish the identifier
        let mut resources = ParserResources::new();
        let mut parser = QualifiedIdentParser::<CheckStandardSyntax>::new();
        parser.move_after_underscore(&mut resources);
        let qi = parse_all_with(parser, &mut resources, b"f 1)");
        assert_eq!(qi.ident.name.as_slice(), b"f");
        assert_eq!(qi.ident.indices.len(), 1);
        assert!(qi.sort.is_none());
        assert!(resources.are_pristine());

        let mut resources = ParserResources::new();
        let mut parser = QualifiedIdentParser::<CheckStandardSyntax>::new();
        parser.move_after_as();
        let qi = parse_all_with(parser, &mut resources, b"x Bool)");
        assert_eq!(qi.ident.name.as_slice(), b"x");
        assert!(qi.sort.is_some());
        assert!(resources.are_pristine());
    }
}

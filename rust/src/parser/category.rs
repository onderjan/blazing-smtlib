use crate::{SmtSpecialConstantView, token::SmtSyntaxToken};

mod attribute;
mod combinator;
mod ident;
mod pattern;
mod qualified_ident;
mod s_expr;
mod sort;
mod sorted_var;
mod term;
mod token;

pub use {
    attribute::{SmtClosedAttributeParser, SmtClosedMultipleAttributeParser},
    combinator::{
        SmtClosedMaximumParser, SmtClosedMultipleParser, SmtClosedParser, SmtOpenedParser,
        SmtPairParser, SmtParenMaximumParser, SmtParenMultipleParser, SmtParenParser,
    },
    ident::SmtIdentParser,
    pattern::SmtPatternParser,
    qualified_ident::SmtQualifiedIdentParser,
    s_expr::SmtSExprParser,
    sort::SmtSortParser,
    sorted_var::SmtSortedVarParser,
    term::SmtTermParser,
    token::{
        SmtCloseParenParser, SmtKeywordParser, SmtNumeralParser, SmtOpenParenParser,
        SmtStringParser, SmtSymbolParser,
    },
};

pub(crate) use attribute::{AttributeSlot, SingleAttribute};
pub(crate) use ident::IdentSlot;
pub(crate) use pattern::PatternSlot;
pub(crate) use qualified_ident::QualifiedIdentSlot;
pub(crate) use s_expr::SExprSlot;
pub(crate) use sort::SortSlot;
pub(crate) use sorted_var::SortedVarSlot;
pub(crate) use term::TermSlot;

pub type SmtParenSortedVarsParser<H> = SmtParenMultipleParser<H, SmtSortedVarParser<H>>;

#[inline]
fn parse_special_constant<'a>(
    kind: SmtSyntaxToken<'a>,
) -> Result<SmtSpecialConstantView<'a>, SmtSyntaxToken<'a>> {
    let constant = match kind {
        SmtSyntaxToken::Numeral(value) => SmtSpecialConstantView::Numeral(value),
        SmtSyntaxToken::Decimal(decimal) => SmtSpecialConstantView::Decimal(decimal),
        SmtSyntaxToken::Hexadecimal(value) => SmtSpecialConstantView::Hexadecimal(value),
        SmtSyntaxToken::Binary(value) => SmtSpecialConstantView::Binary(value),
        SmtSyntaxToken::String(string) => SmtSpecialConstantView::String(string),
        kind => return Err(kind),
    };
    Ok(constant)
}

#[cfg(test)]
pub(crate) mod tests {
    use std::ops::ControlFlow;

    use crate::{
        NonstandardCommandError, SmtSyntaxChecker,
        lexer::SmtLexer,
        parser::{SmtParse, SmtParseError, SmtParseState},
        token::{SmtBatchCursor, SmtConsume, SmtTokenCategory, SmtVersion},
    };

    /// Drives `parser` over `parse_state` through the whole input with the
    /// standard syntax checker as the handler, requiring that it finishes
    /// exactly at the end of the input, and returns its result.
    ///
    /// Lets unit tests enter a category through its crate-private entry
    /// points before driving it.
    pub(crate) fn parse_all_with<P: SmtParse<SmtSyntaxChecker>>(
        parser: P,
        parse_state: &mut SmtParseState<SmtSyntaxChecker>,
        input: &[u8],
    ) -> P::Result {
        struct Drive<'r, P: SmtParse<SmtSyntaxChecker>> {
            parser: P,
            parse_state: &'r mut SmtParseState<SmtSyntaxChecker>,
            result: Option<P::Result>,
            unconsumed: usize,
        }

        impl<P: SmtParse<SmtSyntaxChecker>> SmtConsume for Drive<'_, P> {
            type Result = ();
            type Error = SmtParseError<NonstandardCommandError>;
            const CONSUMES_WHITESPACE_AND_COMMENTS: bool = false;

            fn consume(
                &mut self,
                cursor: &mut SmtBatchCursor<'_>,
            ) -> Result<ControlFlow<()>, Self::Error> {
                while !cursor.is_empty() {
                    if self.result.is_some() {
                        // count the tokens left after the result, except the end of the input
                        while let Some(token) = cursor.next() {
                            if !matches!(token.category(), SmtTokenCategory::EndOfFile) {
                                self.unconsumed += 1;
                            }
                        }
                        return Ok(ControlFlow::Continue(()));
                    }
                    if let ControlFlow::Break(result) =
                        self.parser
                            .parse(&mut SmtSyntaxChecker, self.parse_state, cursor)?
                    {
                        self.result = Some(result);
                    }
                }
                Ok(ControlFlow::Continue(()))
            }
        }

        let mut drive = Drive {
            parser,
            parse_state,
            result: None,
            unconsumed: 0,
        };
        let _ = SmtLexer::new(&mut drive, SmtVersion::V2_7)
            .lex_all(input)
            .expect("test input must lex and parse");
        assert_eq!(
            drive.unconsumed, 0,
            "tokens left unconsumed after the result"
        );
        drive
            .result
            .expect("the parser must finish before the end of the input")
    }
}

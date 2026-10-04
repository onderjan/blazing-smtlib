use crate::{SmtSpecialConstantView, token::SmtSyntaxToken};

mod arena;
mod attribute;
mod combinator;
mod ident;
mod pattern;
mod qualified_ident;
mod resources;
mod s_expr;
mod sort;
mod sorted_var;
mod term;
mod token;

pub use {
    attribute::{ClosedAttributeParser, ClosedMultipleAttributeParser},
    combinator::{
        ClosedMaximumParser, ClosedMultipleParser, ClosedParser, OpenedParser, PairParser,
        ParenMaximumParser, ParenMultipleParser, ParenParser,
    },
    ident::IdentParser,
    pattern::PatternParser,
    qualified_ident::QualifiedIdentParser,
    resources::ParserResources,
    s_expr::SExprParser,
    sort::SortParser,
    sorted_var::SortedVarParser,
    term::TermParser,
    token::{
        CloseParenParser, KeywordParser, NumeralParser, OpenParenParser, StringParser, SymbolParser,
    },
};

pub(crate) use arena::{
    Arena, ArenaAccess, IdentHandle, IndexHandle, PatternHandle, QualifiedIdentHandle,
    SimplePatternHandle, TextHandle,
};
pub(crate) use ident::IdentSlot;
pub(crate) use pattern::PatternSlot;
pub(crate) use qualified_ident::QualifiedIdentSlot;
pub(crate) use s_expr::SExprSlot;
pub(crate) use sort::SortSlot;
pub(crate) use sorted_var::SortedVarSlot;
pub(crate) use term::TermSlot;

pub type ParenSortedVarsParser<H> = ParenMultipleParser<H, SortedVarParser<H>>;

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
        CheckStandardSyntax, NonstandardCommandError,
        read::{
            lexer::Lexer,
            parser::{Parser, ParserError, ParserResources},
        },
        token::{SmtTokenCategory, SmtVersion, TokenCursor, TokenHandler},
    };

    /// Drives `parser` over `resources` through the whole input with the
    /// standard syntax checker as the handler, requiring that it finishes
    /// exactly at the end of the input, and returns its result.
    ///
    /// Lets unit tests enter a category through its crate-private entry
    /// points before driving it.
    pub(crate) fn parse_all_with<P: Parser<CheckStandardSyntax>>(
        parser: P,
        resources: &mut ParserResources<CheckStandardSyntax>,
        input: &[u8],
    ) -> P::Result {
        struct Drive<'r, P: Parser<CheckStandardSyntax>> {
            parser: P,
            resources: &'r mut ParserResources<CheckStandardSyntax>,
            result: Option<P::Result>,
            unconsumed: usize,
        }

        impl<P: Parser<CheckStandardSyntax>> TokenHandler for Drive<'_, P> {
            type Result = ();
            type Error = ParserError<NonstandardCommandError>;

            fn handle_tokens(
                &mut self,
                cursor: &mut TokenCursor<'_>,
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
                            .parse(&mut CheckStandardSyntax, self.resources, cursor)?
                    {
                        self.result = Some(result);
                    }
                }
                Ok(ControlFlow::Continue(()))
            }
        }

        let mut drive = Drive {
            parser,
            resources,
            result: None,
            unconsumed: 0,
        };
        let _ = Lexer::new(&mut drive, SmtVersion::V2_7)
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

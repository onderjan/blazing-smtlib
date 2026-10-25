use crate::{grammar::SmtSpecialConstant, token::SmtSyntaxToken};

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
        SmtTuple3Parser, SmtTuple4Parser, SmtTuple5Parser, SmtTuple6Parser, SmtTuple7Parser,
        SmtTuple8Parser,
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
) -> Result<SmtSpecialConstant<'a>, SmtSyntaxToken<'a>> {
    let constant = match kind {
        SmtSyntaxToken::Numeral(value) => SmtSpecialConstant::Numeral(value),
        SmtSyntaxToken::Decimal(decimal) => SmtSpecialConstant::Decimal(decimal),
        SmtSyntaxToken::Hexadecimal(value) => SmtSpecialConstant::Hexadecimal(value),
        SmtSyntaxToken::Binary(value) => SmtSpecialConstant::Binary(value),
        SmtSyntaxToken::String(string) => SmtSpecialConstant::String(string),
        kind => return Err(kind),
    };
    Ok(constant)
}

#[cfg(test)]
pub(crate) mod tests {
    use std::ops::ControlFlow;

    use crate::{
        SmtNonstandardCommandError, SmtSyntaxChecker, SmtVersion,
        lexer::SmtLexer,
        parser::{SmtParse, SmtParseError, SmtParseState},
        token::{SmtConsume, SmtConsumeFrom, SmtCursor, SmtSyntaxToken},
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
            type Error = SmtParseError<SmtNonstandardCommandError>;
            const IS_CONCRETE: bool = false;
        }

        impl<P: SmtParse<SmtSyntaxChecker>, Z: SmtCursor> SmtConsumeFrom<Z> for Drive<'_, P> {
            fn consume(&mut self, cursor: &mut Z) -> Result<ControlFlow<()>, Self::Error> {
                while !cursor.is_empty() {
                    if self.result.is_some() {
                        // count the tokens left after the result, and break at
                        // the end of the input, as every consumer must
                        while let Some(token) = cursor.next() {
                            if matches!(cursor.syntax(&token), SmtSyntaxToken::EndOfFile) {
                                return Ok(ControlFlow::Break(()));
                            }
                            self.unconsumed += 1;
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

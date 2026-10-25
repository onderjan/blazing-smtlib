//! Tests that every parser of the library can be named by a user: the
//! category parsers, the token parsers, the combinators and their aliases, and
//! the command and script parsers, each through `blazing_smtlib::parser`, and
//! each a parser for a handler of the user's choice.
//!
//! They check the Rust interface itself (which items are exported), so they
//! run the Rust library whatever `parse_backend` selects. A parser that stops
//! being exported makes this file fail to compile.

use blazing_smtlib::{
    SmtNonstandardCommandError, SmtSyntaxChecker,
    parser::{
        SmtCloseParenParser, SmtClosedAttributeParser, SmtClosedMaximumParser,
        SmtClosedMultipleAttributeParser, SmtClosedMultipleParser, SmtClosedParser,
        SmtCommandParser, SmtCommandPayloadParser, SmtCommandRule, SmtIdentParser,
        SmtKeywordParser, SmtNumeralParser, SmtOpenParenParser, SmtOpenedParser, SmtPairParser,
        SmtParenMaximumParser, SmtParenMultipleParser, SmtParenParser, SmtParenSortedVarsParser,
        SmtParse, SmtPatternParser, SmtQualifiedIdentParser, SmtSExprParser, SmtScriptParser,
        SmtSimplePatternParser, SmtSortParser, SmtSortedVarParser, SmtStringParser,
        SmtSymbolParser, SmtTermParser, SmtTuple3Parser, SmtTuple4Parser, SmtTuple5Parser,
        SmtTuple6Parser, SmtTuple7Parser, SmtTuple8Parser,
    },
};

type H = SmtSyntaxChecker;
type S = SmtSymbolParser;

/// Compiles only for a parser for the handler `H`.
fn parser_for_h<P: SmtParse<H>>() {}

/// A command rule that takes a closing parenthesis and does nothing with it.
struct Empty;

impl SmtCommandRule<H> for Empty {
    type Parser = SmtCloseParenParser;

    fn handle(
        &mut self,
        _handler: &mut H,
        _result: <SmtCloseParenParser as SmtParse<H>>::Result,
    ) -> Result<(), SmtNonstandardCommandError> {
        Ok(())
    }
}

#[test]
fn the_token_parsers_are_exported() {
    parser_for_h::<SmtSymbolParser>();
    parser_for_h::<SmtOpenParenParser>();
    parser_for_h::<SmtCloseParenParser>();
    parser_for_h::<SmtNumeralParser>();
    parser_for_h::<SmtKeywordParser>();
    parser_for_h::<SmtStringParser>();
}

#[test]
fn the_category_parsers_are_exported() {
    parser_for_h::<SmtIdentParser>();
    parser_for_h::<SmtSimplePatternParser>();
    parser_for_h::<SmtPatternParser<H>>();
    parser_for_h::<SmtQualifiedIdentParser<H>>();
    parser_for_h::<SmtSortParser<H>>();
    parser_for_h::<SmtSortedVarParser<H>>();
    parser_for_h::<SmtParenSortedVarsParser<H>>();
    parser_for_h::<SmtSExprParser<H>>();
    parser_for_h::<SmtTermParser<H>>();
    parser_for_h::<SmtClosedAttributeParser<H>>();
    parser_for_h::<SmtClosedMultipleAttributeParser<H>>();
}

#[test]
fn the_combinators_are_exported() {
    parser_for_h::<SmtClosedParser<H, S>>();
    parser_for_h::<SmtOpenedParser<H, S>>();
    parser_for_h::<SmtParenParser<H, S>>();
    parser_for_h::<SmtClosedMultipleParser<H, S>>();
    parser_for_h::<SmtParenMultipleParser<H, S>>();
    parser_for_h::<SmtClosedMaximumParser<H, S>>();
    parser_for_h::<SmtParenMaximumParser<H, S>>();
    parser_for_h::<SmtPairParser<H, S, S>>();
    parser_for_h::<SmtTuple3Parser<H, S, S, S>>();
    parser_for_h::<SmtTuple4Parser<H, S, S, S, S>>();
    parser_for_h::<SmtTuple5Parser<H, S, S, S, S, S>>();
    parser_for_h::<SmtTuple6Parser<H, S, S, S, S, S, S>>();
    parser_for_h::<SmtTuple7Parser<H, S, S, S, S, S, S, S>>();
    parser_for_h::<SmtTuple8Parser<H, S, S, S, S, S, S, S, S>>();
}

#[test]
fn the_command_and_script_parsers_are_exported() {
    parser_for_h::<SmtCommandPayloadParser<H, Empty>>();
    parser_for_h::<SmtCommandParser<H>>();
    parser_for_h::<SmtScriptParser<H>>();
}

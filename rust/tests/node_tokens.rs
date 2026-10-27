//! Public-API tests of appending the tokens of nodes: a handler builds every
//! sort, term, s-expression and attribute it is handed as the tokens their
//! views append, and the tokens of each are checked against the tokens of
//! its text. The owned nodes made from the views append the same tokens.
//!
//! They check the Rust interface itself and call the library directly.

use std::convert::Infallible;
use std::ops::ControlFlow;

use blazing_smtlib::{
    SmtHandler, SmtNodeTypes, SmtPartialCommandError, SmtPartialCommandHandler, SmtVersion,
    grammar::{
        SmtApplication, SmtAttributeValue, SmtIdent, SmtIndices, SmtIndicesBuf, SmtMatchCases,
        SmtMultiple, SmtNamedValues, SmtNamedValuesBuf, SmtPattern, SmtQualifiedIdent,
        SmtQuantifierKind, SmtSExpr, SmtSimplePatternsBuf, SmtSort, SmtTerm,
    },
    lexer::{SmtLexer, SmtLexerCursor},
    lexicon::{SmtKeyword, SmtSymbol},
    read_smt,
    token::{
        SmtAppendTokens, SmtConsume, SmtConsumeFrom, SmtCursor, SmtGeneralReserved, SmtReserved,
        SmtToken, SmtTokensBuf, SmtTokensCursor,
    },
};

/// A consumer that keeps the abstract tokens before the end of the input.
#[derive(Default)]
struct Keep {
    tokens: SmtTokensBuf,
}

impl SmtConsume for Keep {
    type Result = SmtTokensBuf;
    type Error = Infallible;
    const IS_CONCRETE: bool = false;
}

impl<'a> SmtConsumeFrom<SmtLexerCursor<'a>> for Keep {
    fn consume(
        &mut self,
        cursor: &mut SmtLexerCursor<'a>,
    ) -> Result<ControlFlow<SmtTokensBuf>, Infallible> {
        while let Some(token) = cursor.next() {
            match cursor.syntax(&token) {
                SmtToken::EndOfFile => {
                    return Ok(ControlFlow::Break(std::mem::take(&mut self.tokens)));
                }
                token => self.tokens.push(token),
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// Lexes the text into its abstract tokens.
fn lexed(text: &str) -> SmtTokensBuf {
    SmtLexer::new(Keep::default(), SmtVersion::V2_7)
        .lex_all(text.as_bytes())
        .expect("the text lexes")
        .into_value()
}

/// The tokens the value appends.
fn tokens_of<V: SmtAppendTokens + ?Sized>(value: &V) -> SmtTokensBuf {
    let mut cursor = SmtTokensCursor::new(SmtVersion::V2_7);
    value.append_tokens(&mut cursor);
    let mut tokens = SmtTokensBuf::new();
    while let Some(token) = cursor.next() {
        tokens.push(cursor.syntax(&token));
    }
    tokens
}

/// Asserts that the two values append the same tokens.
fn assert_same_tokens<A: SmtAppendTokens + ?Sized, B: SmtAppendTokens + ?Sized>(a: &A, b: &B) {
    assert_eq!(format!("{:?}", tokens_of(a)), format!("{:?}", tokens_of(b)));
}

/// Builds tokens out of single tokens and appended values.
struct Build(SmtTokensBuf);

impl Build {
    fn new() -> Self {
        Self(SmtTokensBuf::new())
    }

    fn token(mut self, token: SmtToken<'_>) -> Self {
        self.0.push(token);
        self
    }

    fn word(self, word: SmtGeneralReserved) -> Self {
        self.token(SmtToken::Reserved(SmtReserved::General(word)))
    }

    fn open(self) -> Self {
        self.token(SmtToken::ParenOpen)
    }

    fn close(self) -> Self {
        self.token(SmtToken::ParenClose)
    }

    fn value<V: SmtAppendTokens + ?Sized>(mut self, value: &V) -> Self {
        for token in tokens_of(value).iter() {
            self.0.push(token);
        }
        self
    }
}

type Error = SmtPartialCommandError<Infallible>;

/// Handler that builds every value as tokens, and keeps the tokens of what
/// each `assert`, `declare-const` and `set-info` is handed.
#[derive(Default)]
struct Retoken {
    items: Vec<SmtTokensBuf>,
}

impl SmtHandler for Retoken {
    type Error = Error;
    type SExpr = SmtTokensBuf;
    type Attribute = SmtTokensBuf;
    type Sort = SmtTokensBuf;
    type Term = SmtTokensBuf;
    type Scope = SmtTokensBuf;

    fn set_version(&mut self, _version: SmtVersion) {}

    fn handle_sort(&mut self, sort: SmtSort<'_, Self>) -> Result<SmtTokensBuf, Error> {
        let mut indices = SmtIndicesBuf::new();
        for index in sort.ident.indices.iter() {
            assert_same_tokens(&index, &index.into_owned());
            indices.push(index);
        }
        assert_same_tokens(&sort.ident.indices, &indices);
        assert_same_tokens(&sort.ident, &sort.ident.into_owned());
        Ok(tokens_of(&sort))
    }

    fn handle_term(&mut self, term: SmtTerm<'_, Self>) -> Result<SmtTokensBuf, Error> {
        let tokens = tokens_of(&term);
        match term {
            SmtTerm::SpecialConstant(constant) => {
                assert_same_tokens(&constant, &constant.into_owned());
            }
            SmtTerm::QualifiedIdent(ident) => {
                let viewed = tokens_of(&ident);
                assert_same_tokens(&viewed, &ident.into_owned());
            }
            SmtTerm::Application(application) => {
                let (function, _) = application.into_parts();
                let viewed = tokens_of(&function);
                assert_same_tokens(&viewed, &function.into_owned());
            }
        }
        Ok(tokens)
    }

    fn handle_s_expr(&mut self, expr: SmtSExpr<'_, Self>) -> Result<SmtTokensBuf, Error> {
        Ok(tokens_of(&expr))
    }

    fn handle_attribute(
        &mut self,
        name: SmtKeyword<'_>,
        value: Option<SmtAttributeValue<'_, Self>>,
    ) -> Result<SmtTokensBuf, Error> {
        let built = Build::new().value(&name);
        Ok(match value {
            None => built,
            Some(value) => built.value(&value),
        }
        .0)
    }

    fn annotate_term(
        &mut self,
        term: SmtTokensBuf,
        attributes: SmtMultiple<'_, Self::Attribute>,
    ) -> Result<SmtTokensBuf, Error> {
        Ok(Build::new()
            .open()
            .word(SmtGeneralReserved::ExclamationMark)
            .value(&term)
            .value(&attributes)
            .close()
            .0)
    }

    fn start_let(
        &mut self,
        bindings: SmtNamedValues<'_, SmtTokensBuf>,
    ) -> Result<SmtTokensBuf, Error> {
        let mut owned = SmtNamedValuesBuf::new();
        for (name, term) in bindings.iter() {
            owned.push(name, term.clone());
        }
        assert_same_tokens(&bindings, &owned);
        let built = Build::new().open().word(SmtGeneralReserved::Let).open();
        Ok(built.value(&bindings).close().0)
    }

    fn end_let(&mut self, scope: SmtTokensBuf, body: SmtTokensBuf) -> Result<SmtTokensBuf, Error> {
        Ok(Build(scope).value(&body).close().0)
    }

    fn start_quantifier(
        &mut self,
        kind: SmtQuantifierKind,
        vars: SmtNamedValues<'_, SmtTokensBuf>,
    ) -> Result<SmtTokensBuf, Error> {
        let word = match kind {
            SmtQuantifierKind::Exists => SmtGeneralReserved::Exists,
            SmtQuantifierKind::Forall => SmtGeneralReserved::Forall,
        };
        Ok(Build::new().open().word(word).open().value(&vars).close().0)
    }

    fn end_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        scope: SmtTokensBuf,
        body: SmtTokensBuf,
    ) -> Result<SmtTokensBuf, Error> {
        Ok(Build(scope).value(&body).close().0)
    }

    fn start_lambda(
        &mut self,
        vars: SmtNamedValues<'_, SmtTokensBuf>,
    ) -> Result<SmtTokensBuf, Error> {
        let mut owned = SmtNamedValuesBuf::new();
        for (name, sort) in vars.iter() {
            owned.push(name, sort.clone());
        }
        assert_same_tokens(&vars, &owned);
        let built = Build::new().open().word(SmtGeneralReserved::Lambda).open();
        Ok(built.value(&vars).close().0)
    }

    fn end_lambda(
        &mut self,
        scope: SmtTokensBuf,
        body: SmtTokensBuf,
    ) -> Result<SmtTokensBuf, Error> {
        Ok(Build(scope).value(&body).close().0)
    }

    fn start_match(&mut self, _scrutinee: &SmtTokensBuf) -> Result<(), Error> {
        Ok(())
    }

    fn start_match_case(
        &mut self,
        _scrutinee: &SmtTokensBuf,
        pattern: SmtPattern<'_>,
    ) -> Result<SmtTokensBuf, Error> {
        match pattern {
            SmtPattern::Simple(simple) => assert_same_tokens(&simple, &simple.into_owned()),
            SmtPattern::Application(application) => {
                let mut args = SmtSimplePatternsBuf::new();
                for arg in application.args().iter() {
                    args.push(arg);
                }
                assert_same_tokens(&application.args(), &args);
                assert_same_tokens(&application, &application.into_owned());
            }
        }
        assert_same_tokens(&pattern, &pattern.into_owned());
        Ok(Build::new().open().value(&pattern).0)
    }

    fn end_match_case(
        &mut self,
        scope: SmtTokensBuf,
        _scrutinee: &SmtTokensBuf,
        term: SmtTokensBuf,
    ) -> Result<SmtTokensBuf, Error> {
        Ok(Build(scope).value(&term).close().0)
    }

    fn end_match(
        &mut self,
        scrutinee: SmtTokensBuf,
        cases: SmtMatchCases<'_, Self>,
    ) -> Result<SmtTokensBuf, Error> {
        let mut built = Build::new()
            .open()
            .word(SmtGeneralReserved::Match)
            .value(&scrutinee)
            .open();
        for (_, case) in cases.iter() {
            built = built.value(case);
        }
        Ok(built.close().close().0)
    }
}

impl SmtPartialCommandHandler for Retoken {
    type HandlerError = Infallible;
    type NonstandardParser = Infallible;

    fn command_assert(&mut self, term: SmtTokensBuf) -> Result<(), Error> {
        self.items.push(term);
        Ok(())
    }

    fn command_declare_const(
        &mut self,
        _name: SmtSymbol<'_>,
        sort: SmtTokensBuf,
    ) -> Result<(), Error> {
        self.items.push(sort);
        Ok(())
    }

    fn command_set_info(&mut self, attribute: SmtTokensBuf) -> Result<(), Error> {
        self.items.push(attribute);
        Ok(())
    }
}

/// Reads the command, made of the start and the item, and asserts that the
/// handler is handed the item as its tokens.
fn assert_retokened(start: &str, item: &str) {
    let mut handler = Retoken::default();
    let script = format!("({start} {item})");
    read_smt(&mut handler, script.as_bytes()).expect("the script reads");
    assert_eq!(handler.items.len(), 1, "{script}");
    assert_eq!(
        format!("{:?}", handler.items[0]),
        format!("{:?}", lexed(item)),
        "{script}"
    );
}

#[test]
fn a_sort_appends_the_tokens_it_was_read_from() {
    for sort in [
        "Int",
        "|a sort|",
        "(_ BitVec 8)",
        "(_ FloatingPoint 11 53)",
        "(_ S a 1 |b c|)",
        "(Array Int Bool)",
        "(Array (_ BitVec 32) (List (Array Int (_ BitVec 8))))",
    ] {
        assert_retokened("declare-const x", sort);
    }
}

#[test]
fn a_term_appends_the_tokens_it_was_read_from() {
    for term in [
        "0",
        "12",
        "1.50",
        "#x1F",
        "#b01",
        "\"\"",
        "\"say \"\"hi\"\"\"",
        "x",
        "|a b|",
        "|let|",
        "(_ bv5 8)",
        "(_ x a 0)",
        "(as nil (List Int))",
        "(as (_ x 3) (_ BitVec 3))",
        "(f x)",
        "(f (g x 1) ((as h (Array Int Int)) y) ((_ extract 3 0) z))",
        "(let ((x 1)) x)",
        "(let ((x 1) (y (f 2))) (let ((z x)) (g x y z)))",
        "(forall ((x Int)) (exists ((y Int) (z (List Int))) (f x y z)))",
        "(lambda ((x Int) (y (_ BitVec 8))) (f x y))",
        "(match l ((nil 0) ((cons h t) h) ((pair _ b) b) (_ 1) (x x)))",
        "(! x :named a)",
        "(! (f x) :pattern ((g x) (h x)) :weight 3 :flag :text \"t\" :n #b1)",
    ] {
        assert_retokened("assert", term);
    }
}

#[test]
fn an_attribute_and_its_s_expressions_append_the_tokens_they_were_read_from() {
    for attribute in [
        ":flag",
        ":status sat",
        ":smt-lib-version 2.7",
        ":source |a\nb|",
        ":notes \"n\"",
        ":k ()",
        ":k (a 1 2.5 #x0 #b1 \"s\" :kw as _ ! let (nested (deeper)) ())",
    ] {
        assert_retokened("set-info", attribute);
    }
}

#[test]
fn a_list_appends_its_values_without_enclosing_parentheses() {
    // an owned list of named values appends each as ( name value )
    let mut named = SmtNamedValuesBuf::new();
    named.push(SmtSymbol::new_unquoted(b"x").unwrap(), lexed("Int"));
    named.push(SmtSymbol::new_unquoted(b"y").unwrap(), lexed("(List Int)"));
    assert_same_tokens(&named, &lexed("(x Int) (y (List Int))"));
    // an empty one appends nothing
    assert_same_tokens(&SmtNamedValuesBuf::<SmtTokensBuf>::new(), &lexed(""));
}

/// Node types of a program that builds terms to write them, without handling any.
struct WrittenNodes;

impl SmtNodeTypes for WrittenNodes {
    type SExpr = SmtTokensBuf;
    type Sort = SmtTokensBuf;
    type Term = SmtTokensBuf;
}

/// Tests the Rust interface itself: a term is built from node types alone, without a handler,
/// and appends its tokens. Calls the library directly.
#[test]
fn a_term_built_without_a_handler_appends_its_tokens() {
    let mut args = vec![lexed("a"), lexed("(g b)")];
    let function = SmtQualifiedIdent::<WrittenNodes> {
        ident: SmtIdent {
            name: SmtSymbol::new_unquoted(b"f").unwrap(),
            indices: SmtIndices::empty(),
        },
        sort: Some(lexed("Int")),
    };
    let application = SmtApplication::new(function, SmtMultiple::new(&mut args))
        .expect("the application has arguments");
    let term = SmtTerm::<WrittenNodes>::Application(application);
    assert_same_tokens(&term, &lexed("((as f Int) a (g b))"));
}

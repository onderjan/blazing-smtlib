//! Tests of the contract of `SmtParse::parse` over cursors written outside
//! the library.
//!
//! A parser handed a cursor that is not empty takes at least one token of it
//! before it returns, whatever it returns, errors included; and a parser is
//! never handed an empty cursor, so a combinator whose inner parser finishes
//! at the last token of a cursor waits for the next cursor before it calls
//! the parser after it.
//!
//! The tokens are lexed once into owned values and handed to the parsers in
//! pieces through a cursor of the tests' own, so that each piece can end
//! after any token. The parsers are called directly with the library's
//! syntax checker as the handler: these tests check the Rust interface
//! itself, so they run the Rust library whatever `parse_backend` selects.

use std::cell::RefCell;
use std::convert::Infallible;
use std::ops::ControlFlow;
use std::rc::Rc;

use blazing_smtlib::{
    SmtBinDigitsBuf, SmtDecimalBuf, SmtHandler, SmtHexDigitsBuf, SmtKeywordBuf, SmtNumeralBuf,
    SmtStringContentBuf, SmtSymbolBuf, SmtSyntaxChecker,
    lexer::SmtLexer,
    parser::{
        SmtCloseParenParser, SmtClosedAttributeParser, SmtClosedMaximumParser,
        SmtClosedMultipleAttributeParser, SmtClosedMultipleParser, SmtClosedParser,
        SmtCommandParser, SmtIdentParser, SmtKeywordParser, SmtNumeralParser, SmtOpenParenParser,
        SmtOpenedParser, SmtPairParser, SmtParenMaximumParser, SmtParenMultipleParser,
        SmtParenSortedVarsParser, SmtParse, SmtParseError, SmtParseState, SmtPatternParser,
        SmtQualifiedIdentParser, SmtSExprParser, SmtScriptParser, SmtSortParser,
        SmtSortedVarParser, SmtStringParser, SmtSymbolParser, SmtTermParser, SmtTuple3Parser,
        SmtTuple4Parser, SmtTuple5Parser, SmtTuple6Parser, SmtTuple7Parser, SmtTuple8Parser,
    },
    token::{
        SmtBatchCursor, SmtConsume, SmtConsumeFrom, SmtCursor, SmtReserved, SmtSyntaxToken,
        SmtVersion, SmtVersionPosture, SmtVersionRefused,
    },
};

// --- Tokens as owned values ---

/// A token the parsers see, owned, so that the tokens of a whole input,
/// the end of file included, can be kept together.
#[derive(Debug)]
enum Owned {
    Open,
    Close,
    Numeral(SmtNumeralBuf),
    Decimal(SmtDecimalBuf),
    Hexadecimal(SmtHexDigitsBuf),
    Binary(SmtBinDigitsBuf),
    String(SmtStringContentBuf),
    Keyword(SmtKeywordBuf),
    Symbol(SmtSymbolBuf),
    Reserved(SmtReserved),
    EndOfFile,
}

impl Owned {
    /// The owned token of a library token, or `None` for whitespace and
    /// comments, which the parsers are never handed.
    fn from_syntax(token: SmtSyntaxToken<'_>) -> Option<Self> {
        Some(match token {
            SmtSyntaxToken::ParenOpen => Owned::Open,
            SmtSyntaxToken::ParenClose => Owned::Close,
            SmtSyntaxToken::Numeral(value) => Owned::Numeral(value.into_owned()),
            SmtSyntaxToken::Decimal(value) => Owned::Decimal(value.into_owned()),
            SmtSyntaxToken::Hexadecimal(value) => Owned::Hexadecimal(value.into_owned()),
            SmtSyntaxToken::Binary(value) => Owned::Binary(value.into_owned()),
            SmtSyntaxToken::String(value) => Owned::String(value.into_owned()),
            SmtSyntaxToken::Keyword(value) => Owned::Keyword(value.into_owned()),
            SmtSyntaxToken::Symbol(value) => Owned::Symbol(value.into_owned()),
            SmtSyntaxToken::Reserved(reserved) => Owned::Reserved(reserved),
            SmtSyntaxToken::Whitespace(_) | SmtSyntaxToken::Comment(_) => return None,
            SmtSyntaxToken::EndOfFile => Owned::EndOfFile,
        })
    }

    /// The token as the library views it.
    fn syntax(&self) -> SmtSyntaxToken<'_> {
        match self {
            Owned::Open => SmtSyntaxToken::ParenOpen,
            Owned::Close => SmtSyntaxToken::ParenClose,
            Owned::Numeral(value) => SmtSyntaxToken::Numeral(value.as_view()),
            Owned::Decimal(value) => SmtSyntaxToken::Decimal(value.as_view()),
            Owned::Hexadecimal(value) => SmtSyntaxToken::Hexadecimal(value.as_view()),
            Owned::Binary(value) => SmtSyntaxToken::Binary(value.as_view()),
            Owned::String(value) => SmtSyntaxToken::String(value.as_view()),
            Owned::Keyword(value) => SmtSyntaxToken::Keyword(value.as_view()),
            Owned::Symbol(value) => SmtSyntaxToken::Symbol(value.as_view()),
            Owned::Reserved(reserved) => SmtSyntaxToken::Reserved(*reserved),
            Owned::EndOfFile => SmtSyntaxToken::EndOfFile,
        }
    }
}

/// A consumer that keeps every token the lexer hands over, as owned values.
struct Collect(Vec<Owned>);

impl SmtConsume for Collect {
    type Result = ();
    type Error = Infallible;
    const IS_CONCRETE: bool = false;
}

impl<'a> SmtConsumeFrom<SmtBatchCursor<'a>> for Collect {
    fn consume(&mut self, cursor: &mut SmtBatchCursor<'a>) -> Result<ControlFlow<()>, Infallible> {
        while let Some(token) = cursor.next() {
            let owned = Owned::from_syntax(cursor.syntax(&token));
            let at_end = matches!(owned, Some(Owned::EndOfFile));
            self.0.extend(owned);
            if at_end {
                return Ok(ControlFlow::Break(()));
            }
        }
        Ok(ControlFlow::Continue(()))
    }
}

/// The tokens of the input in 2.7, ending with the end of file.
fn tokens(input: &[u8]) -> Vec<Owned> {
    let mut lexer = SmtLexer::new(Collect(Vec::new()), SmtVersion::V2_7);
    lexer
        .lex_all(input)
        .unwrap_or_else(|err| panic!("test input {input:?} must lex, failed at {:?}", err.span()));
    std::mem::take(&mut lexer.consumer_mut().0)
}

// --- The cursor ---

/// A piece of the tokens, handed to a parser in one call.
///
/// The tokens were lexed in 2.7, so it refuses a switch to 2.0, under which
/// they would be lexed differently. Discarding the rest ends the piece at
/// the tokens consumed.
struct Piece<'d> {
    tokens: &'d [Owned],
    next: usize,
    version: SmtVersion,
    discarded: bool,
}

impl<'d> Piece<'d> {
    fn new(tokens: &'d [Owned]) -> Self {
        Self {
            tokens,
            next: 0,
            version: SmtVersion::V2_7,
            discarded: false,
        }
    }

    /// The number of tokens consumed from the piece.
    fn taken(&self) -> usize {
        self.next
    }
}

impl<'d> SmtCursor for Piece<'d> {
    type Token = &'d Owned;
    type Lookahead = ();

    fn syntax<'t>(&self, token: &'t &'d Owned) -> SmtSyntaxToken<'t> {
        token.syntax()
    }

    fn next(&mut self) -> Option<&'d Owned> {
        let token = self.tokens.get(self.next)?;
        self.next += 1;
        Some(token)
    }

    fn peek(&self) -> Option<&'d Owned> {
        self.tokens.get(self.next)
    }

    fn version(&self) -> SmtVersion {
        self.version
    }

    fn set_version(&mut self, version: SmtVersion) -> Result<(), SmtVersionRefused> {
        if version == SmtVersion::V2_0 {
            return Err(SmtVersionRefused);
        }
        self.version = version;
        Ok(())
    }

    fn discard_rest(&mut self) {
        self.tokens = &self.tokens[..self.next];
        self.discarded = true;
    }
}

// --- A parser that checks how it is called ---

/// A parser that takes one token and finishes with its number, after
/// logging the number. It panics if it is handed an empty cursor.
struct Probe {
    id: usize,
    log: Rc<RefCell<Vec<usize>>>,
}

impl<H: SmtHandler> SmtParse<H> for Probe {
    type Result = usize;

    fn parse<Z: SmtCursor>(
        &mut self,
        _handler: &mut H,
        _parse_state: &mut SmtParseState<H>,
        cursor: &mut Z,
    ) -> Result<ControlFlow<usize>, SmtParseError<H::Error>> {
        assert!(
            !cursor.is_empty(),
            "probe {} was handed an empty cursor",
            self.id
        );
        let _ = cursor.next();
        self.log.borrow_mut().push(self.id);
        Ok(ControlFlow::Break(self.id))
    }
}

/// Probes numbered from zero, sharing one log.
struct Probes {
    log: Rc<RefCell<Vec<usize>>>,
    count: usize,
}

impl Probes {
    fn new() -> Self {
        Self {
            log: Rc::new(RefCell::new(Vec::new())),
            count: 0,
        }
    }

    fn probe(&mut self) -> Probe {
        let probe = Probe {
            id: self.count,
            log: Rc::clone(&self.log),
        };
        self.count += 1;
        probe
    }

    fn calls(&self) -> Vec<usize> {
        self.log.borrow().clone()
    }
}

/// Hands the tokens of the input to the parser in pieces of the given
/// lengths, one call per piece, and returns the parser's result at the
/// break.
///
/// Panics unless every call takes the whole of its piece, every call but
/// the last returns `Continue` and the last breaks.
#[track_caller]
fn feed<P: SmtParse<SmtSyntaxChecker>>(mut parser: P, input: &[u8], pieces: &[usize]) -> P::Result {
    let tokens = tokens(input);
    let mut parse_state = SmtParseState::new();
    let mut start = 0;
    for (index, &length) in pieces.iter().enumerate() {
        let mut piece = Piece::new(&tokens[start..start + length]);
        let flow = parser
            .parse(&mut SmtSyntaxChecker, &mut parse_state, &mut piece)
            .unwrap_or_else(|err| panic!("unexpected error {err:?} in piece {index}"));
        assert_eq!(piece.taken(), length, "piece {index} is not taken whole");
        start += length;
        match flow {
            ControlFlow::Continue(()) => {
                assert!(index + 1 < pieces.len(), "the last piece does not finish")
            }
            ControlFlow::Break(result) => {
                assert_eq!(index + 1, pieces.len(), "piece {index} finishes early");
                return result;
            }
        }
    }
    panic!("no pieces were given")
}

// --- No empty cursor for the parser after a finished one ---

#[test]
fn pair_parser_waits_for_a_token_before_calling_the_second_parser() {
    // the first parser finishes at the last token of the piece
    let mut probes = Probes::new();
    let pair = SmtPairParser::new(SmtSymbolParser::new(), probes.probe());
    let (first, second) = feed(pair, b"a b", &[1, 1]);
    assert_eq!(first.as_slice(), b"a");
    assert_eq!(second, 0);
    assert_eq!(probes.calls(), [0]);

    // both parsers are probes, each finishing at the end of its piece
    let mut probes = Probes::new();
    let pair = SmtPairParser::new(probes.probe(), probes.probe());
    assert_eq!(feed(pair, b"a b", &[1, 1]), (0, 1));
    assert_eq!(probes.calls(), [0, 1]);

    // in one piece, the second parser is called in the same call
    let mut probes = Probes::new();
    let pair = SmtPairParser::new(probes.probe(), probes.probe());
    assert_eq!(feed(pair, b"a b", &[2]), (0, 1));
    assert_eq!(probes.calls(), [0, 1]);
}

#[test]
fn tuple_parsers_wait_for_a_token_before_calling_each_next_parser() {
    /// Feeds a tuple parser of probes one token per piece, then all tokens
    /// in one piece, checking the result and the order of the calls.
    macro_rules! check {
        ($tuple:ident: $($id:literal)+) => {{
            let ids = [$($id),+];
            let input = b"a ".repeat(ids.len());
            for pieces in [vec![1; ids.len()], vec![ids.len()]] {
                let mut probes = Probes::new();
                let parser = $tuple::new($({ let _ = $id; probes.probe() }),+);
                assert_eq!(
                    feed(parser, &input, &pieces),
                    ($($id,)+),
                    "{} in pieces {pieces:?}",
                    stringify!($tuple)
                );
                assert_eq!(probes.calls(), ids, "{} in pieces {pieces:?}", stringify!($tuple));
            }
        }};
    }
    check!(SmtTuple3Parser: 0 1 2);
    check!(SmtTuple4Parser: 0 1 2 3);
    check!(SmtTuple5Parser: 0 1 2 3 4);
    check!(SmtTuple6Parser: 0 1 2 3 4 5);
    check!(SmtTuple7Parser: 0 1 2 3 4 5 6);
    check!(SmtTuple8Parser: 0 1 2 3 4 5 6 7);
}

#[test]
fn paren_maximum_parser_waits_for_a_token_after_the_opening_parenthesis() {
    let mut probes = Probes::new();
    let parser = SmtParenMaximumParser::new(probes.probe(), 1);
    assert_eq!(feed(parser, b"(a)", &[1, 1, 1]), [0]);
    assert_eq!(probes.calls(), [0]);

    // with the element in the piece of the parenthesis
    let mut probes = Probes::new();
    let parser = SmtParenMaximumParser::new(probes.probe(), 1);
    assert_eq!(feed(parser, b"(a)", &[2, 1]), [0]);
    assert_eq!(probes.calls(), [0]);
}

// --- Every library parser takes a token at every call ---

/// Inputs valid and invalid for the various parsers, so that each parser is
/// called in the middle of its values, at their ends and at errors.
const INPUTS: &[&[u8]] = &[
    b"",
    b")",
    b"(",
    b"()",
    b"a",
    b"a b c)",
    b"1",
    b"1.5",
    b"#x1F",
    b"#b10",
    b"\"s\"",
    b":k",
    b":k v)",
    b"_",
    b"as",
    b"!",
    b"let",
    b"(a)",
    b"(a b) c",
    b"(_ a 1)",
    b"(_ a)",
    b"(as a b)",
    b"(x Int)",
    b"((x Int) (y Bool))",
    b"(f a (g b))",
    b"(let ((x 1)) x)",
    b"(! a :named n)",
    b"(forall ((x Int)) x)",
    b"(lambda ((x Int)) x)",
    b"(match x ((c y) y) (_ x))",
    b"(set-logic A)",
    b"(check-sat) (assert (f x))",
    b"(exit) a",
    b"(set-info :smt-lib-version 2.6)",
    b"(set-info :smt-lib-version 2.0)",
    b"(declare-datatypes ((D 0)) (((c))))",
    b"(define-funs-rec ((f () Int)) (1))",
    b"(foo a)",
];

/// Drives fresh parsers from `make` over every input, with the tokens in
/// pieces of one token and in one piece, and reports every call that took
/// no token of a cursor that was not empty, and every `Continue` that left
/// tokens in the cursor.
///
/// After a break, the same parser goes on with the tokens left; an error
/// ends the input.
fn violations<P: SmtParse<SmtSyntaxChecker>>(
    name: &str,
    make: impl Fn() -> P,
    found: &mut Vec<String>,
) {
    for input in INPUTS {
        let text = String::from_utf8_lossy(input);
        let tokens = tokens(input);
        let mut piece_lengths = vec![1];
        if tokens.len() > 1 {
            piece_lengths.push(tokens.len());
        }
        for piece_length in piece_lengths {
            let mut parser = make();
            let mut parse_state = SmtParseState::new();
            let mut start = 0;
            while start < tokens.len() {
                let end = tokens.len().min(start + piece_length);
                let mut piece = Piece::new(&tokens[start..end]);
                let result = parser.parse(&mut SmtSyntaxChecker, &mut parse_state, &mut piece);
                let returned = match &result {
                    Ok(ControlFlow::Continue(())) => "Continue".to_string(),
                    Ok(ControlFlow::Break(_)) => "Break".to_string(),
                    Err(err) => format!("{:?}", err.cause()),
                };
                if piece.taken() == 0 {
                    found.push(format!(
                        "{name} took no token of {text:?} at token {start} in pieces of \
                         {piece_length}, returning {returned}"
                    ));
                    break;
                }
                if matches!(result, Ok(ControlFlow::Continue(()))) && !piece.is_empty() {
                    found.push(format!(
                        "{name} returned Continue with tokens left in {text:?} at token \
                         {start} in pieces of {piece_length}"
                    ));
                    break;
                }
                if result.is_err() {
                    break;
                }
                start += piece.taken();
                if piece.discarded {
                    // only the end of file is left
                    start = tokens.len() - 1;
                }
            }
        }
    }
}

#[test]
fn every_library_parser_takes_a_token_at_every_call() {
    type H = SmtSyntaxChecker;
    let mut found = Vec::new();

    violations("symbol", SmtSymbolParser::new, &mut found);
    violations("numeral", SmtNumeralParser::new, &mut found);
    violations("keyword", SmtKeywordParser::new, &mut found);
    violations("string", SmtStringParser::new, &mut found);
    violations("open-paren", SmtOpenParenParser::new, &mut found);
    violations("close-paren", SmtCloseParenParser::new, &mut found);
    violations("ident", SmtIdentParser::new, &mut found);
    violations(
        "qualified-ident",
        SmtQualifiedIdentParser::<H>::new,
        &mut found,
    );
    violations("sort", SmtSortParser::<H>::new, &mut found);
    violations("term", SmtTermParser::<H>::new, &mut found);
    violations("s-expr", SmtSExprParser::<H>::new, &mut found);
    violations("sorted-var", SmtSortedVarParser::<H>::new, &mut found);
    violations("pattern", SmtPatternParser::<H>::new, &mut found);
    violations(
        "closed-attribute",
        SmtClosedAttributeParser::<H>::new,
        &mut found,
    );
    violations(
        "closed-multiple-attribute",
        SmtClosedMultipleAttributeParser::<H>::new,
        &mut found,
    );
    violations(
        "paren-sorted-vars",
        SmtParenSortedVarsParser::<H>::default,
        &mut found,
    );
    violations(
        "pair",
        || SmtPairParser::<H, _, _>::new(SmtSymbolParser::new(), SmtTermParser::new()),
        &mut found,
    );
    violations(
        "tuple3",
        || {
            SmtTuple3Parser::<H, _, _, _>::new(
                SmtSymbolParser::new(),
                SmtSortParser::new(),
                SmtTermParser::new(),
            )
        },
        &mut found,
    );
    violations(
        "closed",
        || SmtClosedParser::<H, _>::new(SmtTermParser::new()),
        &mut found,
    );
    violations(
        "opened",
        || SmtOpenedParser::<H, _>::new(SmtTermParser::new()),
        &mut found,
    );
    violations(
        "paren",
        || SmtOpenedParser::<H, _>::new(SmtClosedParser::new(SmtTermParser::new())),
        &mut found,
    );
    violations(
        "closed-multiple",
        || SmtClosedMultipleParser::<H, _>::new(SmtTermParser::new()),
        &mut found,
    );
    violations(
        "paren-multiple",
        || {
            SmtParenMultipleParser::<H, _>::new(
                SmtClosedMultipleParser::new(SmtSymbolParser::new()),
            )
        },
        &mut found,
    );
    violations(
        "closed-maximum",
        || SmtClosedMaximumParser::<H, _>::new(SmtSymbolParser::new(), 1),
        &mut found,
    );
    violations(
        "paren-maximum",
        || SmtParenMaximumParser::<H, _>::new(SmtSymbolParser::new(), 1),
        &mut found,
    );
    violations("command", SmtCommandParser::<H>::new, &mut found);
    violations(
        "script",
        || SmtScriptParser::<H>::new(SmtVersionPosture::default()),
        &mut found,
    );

    assert!(
        found.is_empty(),
        "parsers broke the contract:\n{}",
        found.join("\n")
    );
}

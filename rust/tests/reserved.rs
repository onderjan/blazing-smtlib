//! Public-API tests of reserved words through the whole reader: a quoted
//! symbol spelled like a reserved word is an ordinary name everywhere, the
//! unquoted word is rejected wherever a name is expected, and both hold
//! wherever the input is cut into slices.
//!
//! As in the SMT-LIB standard, the command names are reserved words too,
//! while a keyword spelled like a reserved word is an ordinary keyword.

mod common;
mod reserved_words;

use common::{assert_error_span, assert_parser_error, parse};
use reserved_words::{COMMAND_NAMES, reserved_words};

use std::ops::ControlFlow;

use smt_parser_rs::{
    CheckStandardSyntax, NonstandardCommandError,
    read::{SmtReadError, SmtReader},
    token::{SmtVersion, SmtVersionPosture},
};

/// A command with one place where a name is expected, marked `NAME`.
struct NameSite {
    template: &'static str,
    /// The reserved words that are valid in the place when unquoted,
    /// because they start a construct there instead of naming something.
    valid_unquoted: &'static [&'static str],
}

/// The reserved words that start a term after an opening parenthesis.
const TERM_HEADS: &[&str] = &["!", "_", "as", "exists", "forall", "lambda", "let", "match"];

/// Every place where the grammar takes a symbol as a name.
const NAME_SITES: &[NameSite] = &[
    // command signatures
    site("(declare-const NAME Bool)"),
    site("(declare-fun NAME (Int) Bool)"),
    site("(declare-fun f (NAME) Bool)"),
    site("(define-fun NAME () Bool true)"),
    site("(define-fun f ((NAME Int)) Int 0)"),
    site("(define-fun f () NAME true)"),
    site("(define-const NAME Int 0)"),
    site("(define-fun-rec NAME ((x Int)) Int x)"),
    site("(define-funs-rec ((NAME () Bool)) (true))"),
    site("(define-funs-rec ((f ((NAME Int)) Int)) (0))"),
    site("(declare-sort NAME 0)"),
    site("(declare-sort-parameter NAME)"),
    site("(define-sort NAME () Int)"),
    site("(define-sort S (NAME) Int)"),
    site("(set-logic NAME)"),
    // datatypes
    site("(declare-datatype NAME ((c)))"),
    site("(declare-datatype D ((NAME)))"),
    site("(declare-datatype D ((c (NAME Int))))"),
    site("(declare-datatype D (par (NAME) ((c))))"),
    site("(declare-datatypes ((NAME 0)) (((c))))"),
    // terms
    site("(assert NAME)"),
    NameSite {
        template: "(assert (NAME true))",
        valid_unquoted: TERM_HEADS,
    },
    site("(assert (f NAME))"),
    site("(assert (let ((NAME true)) true))"),
    site("(assert (forall ((NAME Int)) true))"),
    site("(assert (exists ((NAME Int)) true))"),
    site("(assert (lambda ((NAME Int)) true))"),
    site("(assert ((_ NAME 1) x))"),
    site("(assert ((_ f NAME) x))"),
    site("(assert (as NAME Int))"),
    site("(assert ((as NAME Int) x))"),
    site("(assert (! true :named NAME))"),
    site("(get-value (NAME))"),
    site("(check-sat-assuming (NAME))"),
    // match patterns, where an unquoted underscore is the wildcard
    NameSite {
        template: "(assert (match x ((NAME true))))",
        valid_unquoted: &["_"],
    },
    site("(assert (match x (((NAME y) true))))"),
    NameSite {
        template: "(assert (match x (((c NAME) true))))",
        valid_unquoted: &["_"],
    },
    // sorts, where an unquoted underscore starts an indexed sort
    site("(declare-const x NAME)"),
    site("(declare-const x (_ NAME 32))"),
    NameSite {
        template: "(declare-const x (NAME Int))",
        valid_unquoted: &["_"],
    },
    site("(declare-const x (Array NAME Int))"),
];

/// A name site where no reserved word is valid unquoted.
const fn site(template: &'static str) -> NameSite {
    NameSite {
        template,
        valid_unquoted: &[],
    }
}

/// Puts the name into the template, returning the input and the byte
/// offset of the name in it.
fn fill(template: &str, name: &str) -> (Vec<u8>, u64) {
    let offset = template
        .find("NAME")
        .expect("test bug: a template marks its name site");
    (
        template.replacen("NAME", name, 1).into_bytes(),
        offset as u64,
    )
}

fn text(input: &[u8]) -> String {
    String::from_utf8_lossy(input).into_owned()
}

#[test]
fn name_sites_are_valid_with_an_ordinary_name() {
    for site in NAME_SITES {
        let (input, _) = fill(site.template, "name");
        if let Err(err) = parse(&input) {
            panic!(
                "test bug: {:?} must parse, got an error at {:?}",
                text(&input),
                err.span()
            );
        }
    }
}

#[test]
fn quoted_reserved_words_are_names_everywhere() {
    let mut failures = Vec::new();
    for site in NAME_SITES {
        for word in reserved_words() {
            let (input, _) = fill(site.template, &format!("|{word}|"));
            if let Err(err) = parse(&input) {
                failures.push(format!("{:?}: error at {:?}", text(&input), err.span()));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} quoted reserved words were rejected as names:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn unquoted_reserved_words_are_rejected_as_names() {
    let mut failures = Vec::new();
    for site in NAME_SITES {
        for word in reserved_words().filter(|word| !site.valid_unquoted.contains(word)) {
            let (input, offset) = fill(site.template, word);
            let expected = (offset, offset + word.len() as u64);
            match parse(&input) {
                Ok(()) => failures.push(format!("{:?}: accepted", text(&input))),
                Err(err) => {
                    let span = err.span();
                    let actual = (span.start().offset(), span.end().offset());
                    if actual != expected {
                        failures.push(format!(
                            "{:?}: error at {actual:?}, expected at the word {expected:?}",
                            text(&input)
                        ));
                    }
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} unquoted reserved words were not rejected at the word:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn reserved_words_as_names_are_parser_errors() {
    // the lexer produces every symbol alike, so the parser rejects the word
    assert_parser_error(b"(declare-const let Bool)", 15, 18);
    assert_parser_error(b"(declare-const push Bool)", 15, 19);
}

#[test]
fn command_names_still_start_commands() {
    let input = b"(set-logic ALL)(declare-const x Bool)(push 1)(assert x)(check-sat)\
        (get-model)(pop 1)(echo \"done\")(exit)";
    if let Err(err) = parse(input) {
        panic!("error at {:?}", err.span());
    }
}

#[test]
fn keywords_spelled_like_reserved_words_are_keywords() {
    let templates = [
        "(set-info :NAME 1)",
        "(get-info :NAME)",
        "(assert (! true :NAME 1))",
    ];
    let mut failures = Vec::new();
    for template in templates {
        for word in reserved_words() {
            let (input, _) = fill(template, word);
            if let Err(err) = parse(&input) {
                failures.push(format!("{:?}: error at {:?}", text(&input), err.span()));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} keywords spelled like reserved words were rejected:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Reads the input as the given pieces, then the end of the input,
/// stopping at the first error.
fn read_pieces(pieces: &[&[u8]]) -> Result<(), SmtReadError<NonstandardCommandError>> {
    let mut handler = CheckStandardSyntax;
    let mut reader =
        SmtReader::script(&mut handler, SmtVersion::V2_7, SmtVersionPosture::default());
    for piece in pieces {
        if let ControlFlow::Break(_) = reader.read_slice(piece)? {
            return Ok(());
        }
    }
    reader.read_eof().map(|_| ())
}

/// Every way to feed the input: all two-piece splits, and byte by byte.
fn all_splits(input: &[u8]) -> Vec<Vec<&[u8]>> {
    let mut splits: Vec<Vec<&[u8]>> = (0..=input.len())
        .map(|at| {
            let (first, second) = input.split_at(at);
            vec![first, second]
        })
        .collect();
    splits.push(input.chunks(1).collect());
    splits
}

#[test]
fn quoted_reserved_words_are_names_across_slice_boundaries() {
    // a quoted symbol cut by a slice boundary is continued from the lexer's
    // own buffer, which must not lose that the symbol was quoted
    let inputs: [&[u8]; 3] = [
        b"(declare-fun |let| (|par|) |STRING|)\n(assert (|let| |_|))",
        b"(declare-const |check-sat| Bool)(assert |check-sat|)",
        b"(assert (match x ((|_| true) ((|match| |as|) false))))",
    ];
    for input in inputs {
        for pieces in all_splits(input) {
            if let Err(err) = read_pieces(&pieces) {
                panic!(
                    "{:?} fed as pieces of lengths {:?}: error at {:?}",
                    text(input),
                    pieces.iter().map(|piece| piece.len()).collect::<Vec<_>>(),
                    err.span()
                );
            }
        }
    }
}

#[test]
fn unquoted_reserved_words_are_rejected_across_slice_boundaries() {
    let inputs: [(&[u8], u64, u64); 3] = [
        (b"(declare-const let Bool)", 15, 18),
        (b"(declare-const push Bool)", 15, 19),
        (b"(assert (f check-sat-assuming))", 11, 29),
    ];
    for (input, start, end) in inputs {
        for pieces in all_splits(input) {
            let err = read_pieces(&pieces).expect_err(&format!(
                "{:?} fed as pieces of lengths {:?} must be rejected",
                text(input),
                pieces.iter().map(|piece| piece.len()).collect::<Vec<_>>()
            ));
            assert_error_span(&err, start, end);
        }
    }
}

#[test]
fn every_command_name_is_rejected_as_a_symbol_term() {
    // the same through a term with every command name, so that a word left
    // out of the reserved set shows up by name
    let accepted: Vec<&str> = COMMAND_NAMES
        .iter()
        .copied()
        .filter(|name| parse(format!("(assert (f {name}))").as_bytes()).is_ok())
        .collect();
    assert!(
        accepted.is_empty(),
        "command names accepted as symbols: {accepted:?}"
    );
}

#[test]
fn errors_at_the_end_of_input_point_at_the_end() {
    // the end of the input carries its location, even though it has no
    // content, so an error there is an empty span at the input's length
    let inputs: [&[u8]; 16] = [
        b"(",
        b"(assert",
        b"(assert (and x",
        b"(assert (let ((x",
        b"(assert (let ((x 1)",
        b"(assert (forall ((x Int)",
        b"(assert (match l ((",
        b"(assert (! x :named",
        b"(assert ((_ f 1",
        b"(assert (as x",
        b"(assert |x|",
        b"(assert (|let| x",
        b"(declare-fun f (Int",
        b"(declare-datatype D ((c (s Int",
        b"(set-info :k (a (b",
        b"(declare-const x Int)\n(assert x\n",
    ];
    for input in inputs {
        let err = parse(input).expect_err(&format!("{:?} must be rejected", text(input)));
        let span = err.span();
        assert_eq!(
            (span.start().offset(), span.end().offset()),
            (input.len() as u64, input.len() as u64),
            "error span for {:?}",
            text(input)
        );
    }
}

//! Public-API tests of SMT-LIB version handling through the whole reader:
//! the reserved words of each version, the version declaration
//! `(set-info :smt-lib-version <version>)` that switches between them,
//! the posture that limits the declarations, and the reset of both
//! at the end of every input.

mod reserved_words;

use reserved_words::reserved_words;

use std::ops::ControlFlow;

use blazing_smtlib::{
    NonstandardCommandError, SmtBytes, SmtSyntaxChecker,
    parser::{SmtCommandOutcome, SmtCommandParser, SmtSExprParser, SmtSyntaxErrorKind},
    reader::{SmtReadError, SmtReadErrorKind, SmtReader},
    token::{
        SmtCommandNameReserved, SmtGeneralReserved, SmtReserved, SmtTokenCategory, SmtVersion,
        SmtVersionPosture, SmtVersionPostureBuilder,
    },
};

type ReadError = SmtReadError<NonstandardCommandError>;

/// The versions with their spelling in a declaration, oldest first.
const VERSIONS: [(SmtVersion, &str); 4] = [
    (SmtVersion::V2_0, "2.0"),
    (SmtVersion::V2_5, "2.5"),
    (SmtVersion::V2_6, "2.6"),
    (SmtVersion::V2_7, "2.7"),
];

/// The version that made the word reserved.
fn introduced_in(word: &str) -> SmtVersion {
    match word {
        "lambda" | "declare-sort-parameter" | "define-const" => SmtVersion::V2_7,
        "match" | "declare-datatype" | "declare-datatypes" => SmtVersion::V2_6,
        "BINARY"
        | "HEXADECIMAL"
        | "check-sat-assuming"
        | "declare-const"
        | "define-fun-rec"
        | "define-funs-rec"
        | "echo"
        | "get-model"
        | "get-unsat-assumptions"
        | "reset"
        | "reset-assertions" => SmtVersion::V2_5,
        _ => SmtVersion::V2_0,
    }
}

/// The default posture with 2.0 allowed as well: every version can be declared, once.
fn every_version_allowed() -> SmtVersionPosture {
    posture(|builder| {
        builder.add_allowed(SmtVersion::V2_0);
    })
}

/// Reads the input as a script in the given pieces, then the end of the input,
/// stopping at the first error.
fn read_pieces(
    pieces: &[&[u8]],
    initial: SmtVersion,
    posture: SmtVersionPosture,
) -> Result<(), ReadError> {
    let mut handler = SmtSyntaxChecker;
    let mut reader = SmtReader::script(&mut handler, initial, posture);
    for piece in pieces {
        if let ControlFlow::Break(_) = reader.read_slice(piece)? {
            return Ok(());
        }
    }
    reader.read_eof().map(|_| ())
}

/// The outcome of reading the input: nothing, or the error kind with the
/// byte offsets of its span.
type Outcome = Result<(), (String, u64, u64)>;

fn outcome(result: Result<(), ReadError>) -> Outcome {
    result.map_err(|err| {
        (
            format!("{:?}", err.kind()),
            err.span().start().offset(),
            err.span().end().offset(),
        )
    })
}

/// Reads the input whole, in every two-piece split and byte by byte,
/// requires the same outcome each time, and returns it.
#[track_caller]
fn read(input: &str, initial: SmtVersion, posture: SmtVersionPosture) -> Outcome {
    let input = input.as_bytes();
    let whole = outcome(read_pieces(&[input], initial, posture.clone()));
    for at in 0..=input.len() {
        let (first, second) = input.split_at(at);
        assert_eq!(
            outcome(read_pieces(&[first, second], initial, posture.clone())),
            whole,
            "the outcome differs when {:?} is split at {at}",
            String::from_utf8_lossy(input)
        );
    }
    let bytes: Vec<&[u8]> = input.chunks(1).collect();
    assert_eq!(
        outcome(read_pieces(&bytes, initial, posture)),
        whole,
        "the outcome differs when {:?} is fed byte by byte",
        String::from_utf8_lossy(input)
    );
    whole
}

/// Reads the input under the default posture, starting in version 2.7.
#[track_caller]
fn read_default(input: &str) -> Outcome {
    read(input, SmtVersion::V2_7, SmtVersionPosture::default())
}

/// Reads the input with every version allowed, starting in version 2.7.
#[track_caller]
fn read_any_version(input: &str) -> Outcome {
    read(input, SmtVersion::V2_7, every_version_allowed())
}

/// Requires a syntax error of the given kind spanning the given byte offsets.
#[track_caller]
fn assert_syntax_error(outcome: Outcome, kind: SmtSyntaxErrorKind, start: u64, end: u64) {
    assert_eq!(
        outcome,
        Err((
            format!("{:?}", SmtReadErrorKind::<()>::Syntax(kind)),
            start,
            end
        ))
    );
}

fn posture(build: impl FnOnce(&mut SmtVersionPostureBuilder)) -> SmtVersionPosture {
    let mut builder = SmtVersionPostureBuilder::new();
    build(&mut builder);
    builder.build()
}

#[test]
fn the_lookups_find_a_word_from_its_version_on() {
    for (version, _) in VERSIONS {
        for word in reserved_words() {
            let expected = version >= introduced_in(word);
            // the word itself is known from the latest version
            let reserved = SmtReserved::from_bytes_opt(word.as_bytes(), SmtVersion::V2_7)
                .unwrap_or_else(|| panic!("{word:?} should be reserved in the latest version"));
            let symbol = SmtBytes::from_vec(word.as_bytes().to_vec());
            let group = match reserved {
                SmtReserved::General(_) => {
                    SmtGeneralReserved::from_bytes_opt(word.as_bytes(), version).is_some()
                }
                SmtReserved::CommandName(_) => {
                    SmtCommandNameReserved::from_bytes_opt(word.as_bytes(), version).is_some()
                }
            };
            let found = [
                SmtReserved::from_bytes_opt(word.as_bytes(), version) == Some(reserved),
                SmtReserved::from_symbol_opt(&symbol, version) == Some(reserved),
                group,
                reserved.is_in_version(version),
            ];
            assert_eq!(found, [expected; 4], "{word:?} in {version:?}");
            // and when it is not reserved yet, nothing else is found in its place
            if !expected {
                assert_eq!(SmtReserved::from_bytes_opt(word.as_bytes(), version), None);
            }
        }
    }
}

#[test]
fn each_version_reserves_exactly_its_words() {
    // a reserved word cannot name a function, a word not yet reserved can;
    // the version is either the initial one or declared from another one
    let mut failures = Vec::new();
    for (index, (version, spelling)) in VERSIONS.into_iter().enumerate() {
        for word in reserved_words() {
            let reserved = version >= introduced_in(word);
            let declare = format!("(declare-fun {word} () Bool)");
            let switched = format!("(set-info :smt-lib-version {spelling}){declare}");
            let (other, _) = VERSIONS[(index + 1) % VERSIONS.len()];
            for (input, initial) in [(&declare, version), (&switched, other)] {
                let rejected =
                    read_pieces(&[input.as_bytes()], initial, every_version_allowed()).is_err();
                if rejected != reserved {
                    failures.push(format!(
                        "{input} from {initial:?}: rejected {rejected}, reserved {reserved}"
                    ));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} words are not reserved as their version says:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn a_command_of_a_later_version_is_nonstandard() {
    // a command name that is not yet reserved is a symbol,
    // so the command goes to the handler as a nonstandard one
    for (command, since) in [
        ("(check-sat-assuming ())", SmtVersion::V2_5),
        ("(declare-const c Bool)", SmtVersion::V2_5),
        ("(define-fun-rec f () Bool true)", SmtVersion::V2_5),
        ("(define-funs-rec ((f () Bool)) (true))", SmtVersion::V2_5),
        ("(echo \"x\")", SmtVersion::V2_5),
        ("(get-model)", SmtVersion::V2_5),
        ("(get-unsat-assumptions)", SmtVersion::V2_5),
        ("(reset)", SmtVersion::V2_5),
        ("(reset-assertions)", SmtVersion::V2_5),
        ("(declare-datatype T ((c)))", SmtVersion::V2_6),
        ("(declare-datatypes ((T 0)) (((c))))", SmtVersion::V2_6),
        ("(declare-sort-parameter A)", SmtVersion::V2_7),
        ("(define-const c Bool true)", SmtVersion::V2_7),
    ] {
        for (version, spelling) in VERSIONS {
            let input = format!("(set-info :smt-lib-version {spelling}){command}");
            let result = read_any_version(&input);
            if version >= since {
                assert_eq!(result, Ok(()), "{command} is standard in {version:?}");
            } else {
                let (kind, start, _) = result.expect_err("the command is not standard yet");
                assert!(
                    kind.starts_with("Handler(NonstandardCommandError("),
                    "{command} in {version:?}: {kind}"
                );
                // the error is at the command name, after the declaration and the parenthesis
                assert_eq!(start, 32, "{command} in {version:?}");
            }
        }
    }
}

#[test]
fn a_declaration_applies_after_its_command() {
    // not to the commands before it
    let result = read_default("(declare-const lambda Bool)(set-info :smt-lib-version 2.6)");
    assert_syntax_error(result, SmtSyntaxErrorKind::ExpectedSymbol, 15, 21);
    // to all the commands after it, whatever the input is cut into
    assert_eq!(
        read_default(
            "(set-info :smt-lib-version 2.6)(declare-const lambda Bool)(assert lambda)\n\
             (push 1)(declare-const define-const Bool)(assert (and lambda define-const))"
        ),
        Ok(())
    );
    // and it can move forward as well as back
    let result = read(
        "(declare-const lambda Bool)(set-info :smt-lib-version 2.7)(assert lambda)",
        SmtVersion::V2_6,
        SmtVersionPosture::default(),
    );
    assert_syntax_error(result, SmtSyntaxErrorKind::ExpectedTerm, 66, 72);
}

#[test]
fn only_the_set_info_attribute_declares_a_version() {
    for input in [
        // another key, also one that only starts or continues like the version key
        "(set-info :status sat)",
        "(set-info :smt-lib-versio 2.6)",
        "(set-info :smt-lib-versions 2.6)",
        // the key deeper in the value, or inside a quoted symbol
        "(set-info :source (:smt-lib-version 2.6))",
        "(set-info :source |:smt-lib-version 2.6|)",
        // the same attribute as an option or a term annotation, with any value
        "(set-option :smt-lib-version 2.6)",
        "(set-option :smt-lib-version nonsense)",
        "(assert (! true :smt-lib-version 2.6))",
    ] {
        // no version is declared: lambda stays reserved, and a real declaration is the first
        let script = format!("{input}(set-info :smt-lib-version 2.7)(declare-const lambda Bool)");
        let start = input.len() as u64 + 46;
        assert_syntax_error(
            read_default(&script),
            SmtSyntaxErrorKind::ExpectedSymbol,
            start,
            start + 6,
        );
    }
}

#[test]
fn a_version_that_is_not_supported_is_rejected() {
    // the value must be a decimal that names a version the posture allows;
    // the error is at the value, or at what stands in its place, and is
    // raised once the command is complete
    for (value, end) in [
        // a version that is not allowed by default
        ("2.0", 30),
        // versions the library does not know, and decimals that are no versions
        ("1.2", 30),
        ("2.8", 30),
        ("3.0", 30),
        ("2.60", 31),
        ("2.06", 31),
        // a version in another token kind
        ("2", 28),
        ("\"2.6\"", 32),
        ("|2.6|", 32),
        ("v2.6", 31),
        ("(2.6)", 28),
        // no value at all
        ("", 28),
    ] {
        let input = format!("(set-info :smt-lib-version {value})");
        assert_syntax_error(
            read_default(&input),
            SmtSyntaxErrorKind::UnsupportedVersion,
            27,
            end,
        );
    }

    // a command that is malformed is rejected for that first, like any other
    // command: the version is only looked at when the command is complete
    for (input, kind, start, end) in [
        // a keyword cannot be the value of an attribute
        (
            "(set-info :smt-lib-version :version)",
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose]),
            27,
            35,
        ),
        // a second value after one that names no version
        (
            "(set-info :smt-lib-version 9.9 x)",
            SmtSyntaxErrorKind::ExpectedToken(&[SmtTokenCategory::ParenClose]),
            31,
            32,
        ),
    ] {
        assert_syntax_error(read_default(input), kind, start, end);
    }

    // 2.0 has to be allowed explicitly
    assert_eq!(read_any_version("(set-info :smt-lib-version 2.0)"), Ok(()));

    // a version the library knows is rejected the same way when the posture excludes it
    for (excluded, spelling) in VERSIONS {
        let without = posture(|builder| {
            builder
                .add_allowed(SmtVersion::V2_0)
                .remove_allowed(excluded);
        });
        for (_, declared) in VERSIONS {
            let input = format!("(set-info :smt-lib-version {declared})");
            let result = read(&input, SmtVersion::V2_7, without.clone());
            if declared == spelling {
                assert_syntax_error(result, SmtSyntaxErrorKind::UnsupportedVersion, 27, 30);
            } else {
                assert_eq!(result, Ok(()), "{declared} without {excluded:?}");
            }
        }
    }
    let none = posture(|builder| {
        builder.clear_allowed();
    });
    let result = read("(set-info :smt-lib-version 2.7)", SmtVersion::V2_7, none);
    assert_syntax_error(result, SmtSyntaxErrorKind::UnsupportedVersion, 27, 30);
}

#[test]
fn a_version_value_is_followed_by_the_closing_parenthesis() {
    let result = read_default("(set-info :smt-lib-version 2.6 2.6)");
    let (kind, start, end) = result.expect_err("a second value is no attribute");
    assert!(kind.starts_with("Syntax(ExpectedToken("), "{kind}");
    assert_eq!((start, end), (31, 34));
}

#[test]
fn the_number_of_declarations_is_limited() {
    let two = "(set-info :smt-lib-version 2.6)\n(set-info :smt-lib-version 2.5)";
    let same = "(set-info :smt-lib-version 2.7)\n(set-info :smt-lib-version 2.7)";

    // by default one declaration is allowed, also when the second one changes nothing
    for input in [two, same] {
        assert_syntax_error(
            read_default(input),
            SmtSyntaxErrorKind::TooManyVersionDeclarations(1),
            59,
            62,
        );
    }

    // with no declaration allowed, the first one is rejected
    let zero = posture(|builder| {
        builder.set_max_declarations(Some(0));
    });
    let result = read(
        "(set-info :smt-lib-version 2.7)",
        SmtVersion::V2_7,
        zero.clone(),
    );
    assert_syntax_error(
        result,
        SmtSyntaxErrorKind::TooManyVersionDeclarations(0),
        27,
        30,
    );
    assert_eq!(
        read("(set-info :status sat)", SmtVersion::V2_7, zero),
        Ok(())
    );

    // a higher limit counts the declarations, and no limit allows any number
    let three = format!("{two}\n(set-info :smt-lib-version 2.7)");
    let up_to_two = posture(|builder| {
        builder.set_max_declarations(Some(2));
    });
    assert_eq!(read(two, SmtVersion::V2_7, up_to_two.clone()), Ok(()));
    assert_syntax_error(
        read(&three, SmtVersion::V2_7, up_to_two),
        SmtSyntaxErrorKind::TooManyVersionDeclarations(2),
        91,
        94,
    );
    let unlimited = posture(|builder| {
        builder.set_max_declarations(None);
    });
    let input = format!("{three}(declare-const lambda Bool)");
    assert_syntax_error(
        read(&input, SmtVersion::V2_7, unlimited.clone()),
        SmtSyntaxErrorKind::ExpectedSymbol,
        110,
        116,
    );
    let input = format!("{two}(declare-const match Bool)");
    assert_eq!(read(&input, SmtVersion::V2_7, unlimited), Ok(()));

    // a rejected version is reported before the limit
    let result = read_default("(set-info :smt-lib-version 2.6)(set-info :smt-lib-version 2.0)");
    assert_syntax_error(result, SmtSyntaxErrorKind::UnsupportedVersion, 58, 61);
}

#[test]
fn the_version_and_the_declaration_count_reset_with_the_input() {
    let declared = b"(set-info :smt-lib-version 2.6)(declare-const lambda Bool)";
    let undeclared = b"(declare-const lambda Bool)";
    for ending in [&b""[..], b"(exit)"] {
        let mut handler = SmtSyntaxChecker;
        let mut reader =
            SmtReader::script(&mut handler, SmtVersion::V2_7, SmtVersionPosture::default());
        // every input may declare its version once: the count starts again
        for _ in 0..3 {
            assert!(matches!(
                reader.read_slice(declared),
                Ok(ControlFlow::Continue(()))
            ));
            let finished = if ending.is_empty() {
                reader.read_eof()
            } else {
                reader.read_slice(ending)
            };
            assert!(matches!(finished, Ok(ControlFlow::Break(_))));
        }
        // and the declared version is gone: the next input starts in the initial one
        let err = reader
            .read_slice(undeclared)
            .expect_err("lambda is reserved in the initial version");
        assert!(matches!(
            err.kind(),
            SmtReadErrorKind::Syntax(SmtSyntaxErrorKind::ExpectedSymbol)
        ));
    }
}

#[test]
fn a_command_parser_reports_the_declaration_without_applying_it() {
    // switching is the script parser's job: the one-command parser has nothing
    // to switch, so it finishes with the declared version and its span, applies
    // no posture, and the reader is back in its initial version for the next command
    let mut handler = SmtSyntaxChecker;
    let mut reader =
        SmtReader::with_parser(&mut handler, SmtCommandParser::new(), SmtVersion::V2_7);
    let mut stop = |input: &[u8]| -> Result<SmtCommandOutcome, ReadError> {
        match reader.read_slice(input)? {
            ControlFlow::Break(located) => Ok(*located.value()),
            ControlFlow::Continue(()) => panic!("the command must finish the reader"),
        }
    };

    for (version, spelling) in VERSIONS {
        // twice each, more than the default posture would allow
        for _ in 0..2 {
            let input = format!("(set-info :smt-lib-version {spelling})");
            match stop(input.as_bytes()).expect("a declaration of a known version") {
                SmtCommandOutcome::SetVersion(declared, span) => {
                    assert_eq!(declared, version);
                    assert_eq!((span.start().offset(), span.end().offset()), (27, 30));
                }
                other => panic!("expected a version declaration, got {other:?}"),
            }
        }
    }
    assert_eq!(
        stop(b"(set-info :status sat)").expect("another attribute"),
        SmtCommandOutcome::Command
    );
    // lambda is still reserved after the declarations of 2.5 and 2.6
    assert!(stop(b"(set-info :smt-lib-version 2.6)").is_ok());
    assert!(stop(b"(declare-const lambda Bool)").is_err());
}

#[test]
fn assumptions_are_literals_before_2_7() {
    let declarations = "(declare-const p Bool)(declare-const q Bool)";
    let check = |version: &str, assumptions: &str| {
        let input = format!(
            "(set-info :smt-lib-version {version}){declarations}\
             (check-sat-assuming ({assumptions}))(check-sat-assuming ((not p)))"
        );
        read_default(&input)
    };
    // the offset of the assumption list's content
    let start = (31 + declarations.len() + 21) as u64;

    // the command exists since 2.5
    let versions = || {
        VERSIONS
            .into_iter()
            .filter(|(version, _)| *version >= SmtVersion::V2_5)
    };

    // literals are assumptions in every version, also an empty list of them;
    // a quoted symbol is a symbol, `not` included
    for assumptions in [
        "",
        "p",
        "p q",
        "(not p)",
        "p (not q) true",
        "(|not| p)",
        "|not|",
    ] {
        for (_, spelling) in versions() {
            assert_eq!(
                check(spelling, assumptions),
                Ok(()),
                "{assumptions} in {spelling}"
            );
        }
    }

    // other terms are assumptions only since 2.7; before, the error is at the
    // first token that cannot continue a literal, given as (offset, length)
    for (assumptions, at, len) in [
        ("(and p q)", 1, 3),
        ("(not (not p))", 5, 1),
        ("(not p q)", 7, 1),
        ("(not)", 4, 1),
        ("(p)", 1, 1),
        ("p (! q :named n)", 3, 1),
        ("((_ is c) p)", 1, 1),
        ("((as p Bool))", 1, 1),
        ("1", 0, 1),
        ("#b1", 0, 3),
        ("\"p\"", 0, 3),
        (":p", 0, 2),
        ("(let ((x p)) x)", 1, 3),
    ] {
        for (version, spelling) in versions() {
            let result = check(spelling, assumptions);
            if version < SmtVersion::V2_7 {
                assert_syntax_error(
                    result,
                    SmtSyntaxErrorKind::ExpectedPropositionalLiteral,
                    start + at,
                    start + at + len,
                );
            } else if let Err((kind, _, _)) = result {
                // a term, so not a syntax error of the literal shape in 2.7
                assert!(
                    !kind.contains("ExpectedPropositionalLiteral"),
                    "{assumptions} in {spelling}: {kind}"
                );
            }
        }
    }
    // these are terms: accepted in 2.7
    for assumptions in [
        "(and p q)",
        "(not (not p))",
        "p (! q :named n)",
        "(let ((x p)) x)",
    ] {
        assert_eq!(check("2.7", assumptions), Ok(()), "{assumptions}");
    }

    // what is not a list at all is reported the same way in every version
    for (_, version) in versions() {
        let input = format!("(set-info :smt-lib-version {version})(check-sat-assuming p)");
        let (kind, start, end) = read_default(&input).expect_err("the list is missing");
        assert!(kind.starts_with("Syntax(ExpectedToken("), "{kind}");
        assert_eq!((start, end), (51, 52));
    }
}

/// Splits a text with one `@` in it into the text without the mark
/// and the byte offset where the mark was.
fn marked(text: &str) -> (String, u64) {
    let at = text.find('@').expect("the text must have a mark");
    (text.replacen('@', "", 1), at as u64)
}

#[test]
fn a_reserved_word_is_an_s_expression_since_2_6() {
    // inside an attribute value, in a set-info, a set-option and an annotation,
    // at the first level and deeper; the mark is where the word goes
    let sites = [
        "(set-info :a (@))",
        "(set-info :a (x @ y))",
        "(set-info :a (x (1 (@ :k)) \"s\"))",
        "(set-option :a (@))",
        "(assert (! true :a (@) :b))",
        "(assert (! true :pattern ((f @))))",
    ];
    let mut failures = Vec::new();
    for (version, spelling) in VERSIONS {
        for word in reserved_words() {
            for site in sites {
                let (template, at) =
                    marked(&format!("(set-info :smt-lib-version {spelling}){site}"));
                let mut input = template;
                input.insert_str(at as usize, word);
                // a word that is not reserved yet is a symbol, which always was an
                // S-expression; a reserved word is one from 2.6 on
                let reserved = version >= introduced_in(word);
                let expected = if reserved && version < SmtVersion::V2_6 {
                    Err((
                        "Syntax(ExpectedSExpr)".to_string(),
                        at,
                        at + word.len() as u64,
                    ))
                } else {
                    Ok(())
                };
                let result = outcome(read_pieces(
                    &[input.as_bytes()],
                    SmtVersion::V2_7,
                    every_version_allowed(),
                ));
                if result != expected {
                    failures.push(format!("{input}: {result:?}, expected {expected:?}"));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "{} reserved words in S-expressions are not handled as their version says:\n{}",
        failures.len(),
        failures.join("\n")
    );

    // the same holds wherever the input is cut
    assert_syntax_error(
        read_default("(set-info :smt-lib-version 2.5)(set-info :a (x (let) y))"),
        SmtSyntaxErrorKind::ExpectedSExpr,
        48,
        51,
    );
    assert_eq!(
        read_default("(set-info :smt-lib-version 2.6)(set-info :a (x (let) y))"),
        Ok(())
    );

    // a reserved word alone is no attribute value in any version
    for (_, spelling) in VERSIONS {
        let input = format!("(set-info :smt-lib-version {spelling})(set-info :a let)");
        assert_syntax_error(
            read_any_version(&input),
            SmtSyntaxErrorKind::ExpectedAttribute,
            44,
            47,
        );
    }
}

#[test]
fn a_reserved_word_alone_is_an_s_expression_since_2_6() {
    // the S-expression parser on its own takes the reserved word as a whole S-expression
    for (version, _) in VERSIONS {
        let mut handler = SmtSyntaxChecker;
        let mut reader = SmtReader::with_parser(&mut handler, SmtSExprParser::new(), version);
        let result = reader.read_slice(b"let ");
        if version < SmtVersion::V2_6 {
            let err = result.expect_err("a reserved word is no S-expression before 2.6");
            assert!(matches!(
                err.kind(),
                SmtReadErrorKind::Syntax(SmtSyntaxErrorKind::ExpectedSExpr)
            ));
            assert_eq!(
                (err.span().start().offset(), err.span().end().offset()),
                (0, 3)
            );
        } else {
            assert!(
                matches!(result, Ok(ControlFlow::Break(_))),
                "a reserved word is an S-expression in {version:?}"
            );
        }
    }
}

#[test]
fn the_underscore_is_a_match_pattern_since_2_7() {
    // `match` itself is reserved since 2.6, so the patterns exist in 2.6 and 2.7;
    // the mark is at the token the error is reported at
    let check = |spelling: &str, body: &str| {
        let (body, at) = marked(body);
        let prefix = format!("(set-info :smt-lib-version {spelling})(assert ");
        let at = at + prefix.len() as u64;
        (read_default(&format!("{prefix}{body})")), at)
    };

    // patterns without an underscore are the same in both versions
    for body in [
        "@(match x ((y true)))",
        "@(match x (((c y) true) (d false)))",
        "@(match x (((c y z) (match y ((|_| z))))))",
    ] {
        for spelling in ["2.6", "2.7"] {
            assert_eq!(check(spelling, body).0, Ok(()), "{body} in {spelling}");
        }
    }

    // the underscore as a whole pattern and as a constructor argument
    for (body, kind_2_6) in [
        (
            "(match x ((@_ true)))",
            SmtSyntaxErrorKind::ExpectedSymbolOrParenOpen,
        ),
        (
            "(match x (((c @_) true)))",
            SmtSyntaxErrorKind::ExpectedSymbol,
        ),
        (
            "(match x (((c y @_ z) true) (d false)))",
            SmtSyntaxErrorKind::ExpectedSymbol,
        ),
        (
            "(match x (((c y) true) (@_ false)))",
            SmtSyntaxErrorKind::ExpectedSymbolOrParenOpen,
        ),
    ] {
        let (result, at) = check("2.6", body);
        assert_syntax_error(result, kind_2_6, at, at + 1);
        assert_eq!(check("2.7", body).0, Ok(()), "{body} in 2.7");
    }

    // the underscore is never the constructor of a pattern
    for spelling in ["2.6", "2.7"] {
        let (result, at) = check(spelling, "(match x (((@_ y) true)))");
        assert_syntax_error(result, SmtSyntaxErrorKind::ExpectedSymbol, at, at + 1);
    }

    // what is no pattern at all is reported by what the version expects there
    for (body, kind_2_6, kind_2_7) in [
        (
            "(match x ((@1 true)))",
            SmtSyntaxErrorKind::ExpectedSymbolOrParenOpen,
            SmtSyntaxErrorKind::ExpectedSymbolUnderscoreOrParenOpen,
        ),
        (
            "(match x (((c @1) true)))",
            SmtSyntaxErrorKind::ExpectedSymbol,
            SmtSyntaxErrorKind::ExpectedSymbolOrUnderscore,
        ),
    ] {
        let (result, at) = check("2.6", body);
        assert_syntax_error(result, kind_2_6, at, at + 1);
        let (result, at) = check("2.7", body);
        assert_syntax_error(result, kind_2_7, at, at + 1);
    }
}

#[test]
fn an_index_is_a_numeral_before_2_5() {
    // numerals index an identifier in every version
    for body in [
        "((_ extract 3 0) x)",
        "(= x (_ bv1 8))",
        "(f (as (_ a 1 2) (_ BitVec 8)))",
    ] {
        for (_, spelling) in VERSIONS {
            let input = format!("(set-info :smt-lib-version {spelling})(assert {body})");
            assert_eq!(read_any_version(&input), Ok(()), "{body} in {spelling}");
        }
    }

    // a symbol does since 2.5; the mark is at the index
    for body in [
        "((_ is @c) x)",
        "(= x (_ a 1 @|b c| 2))",
        "(f (as (_ a @b) S))",
    ] {
        let (body, at) = marked(body);
        for (version, spelling) in VERSIONS {
            let prefix = format!("(set-info :smt-lib-version {spelling})(assert ");
            let result = read_any_version(&format!("{prefix}{body})"));
            if version >= SmtVersion::V2_5 {
                assert_eq!(result, Ok(()), "{body} in {spelling}");
            } else {
                let start = prefix.len() as u64 + at;
                let (kind, error_start, _) = result.expect_err("a symbol is no index in 2.0");
                assert_eq!(
                    (kind.as_str(), error_start),
                    ("Syntax(ExpectedIndexOrCloseParen)", start),
                    "{body} in {spelling}"
                );
            }
        }
    }
}

#[test]
fn the_string_escapes_follow_the_declared_version() {
    // each string is one string in one regime and cuts the input wrongly in the other;
    // the errors are those of the lexer, at the string
    let legacy = "(set-info :a \"x\\\"y\")";
    let modern = "(set-info :a \"x\"\"y\")";
    let to_2_0 = "(set-info :smt-lib-version 2.0)";
    let to_2_6 = "(set-info :smt-lib-version 2.6)";
    let read_from = |initial, input: String| read(&input, initial, every_version_allowed());

    for (initial, input, ok) in [
        // without a declaration, the initial version decides
        (SmtVersion::V2_0, legacy.to_string(), true),
        (SmtVersion::V2_0, modern.to_string(), false),
        (SmtVersion::V2_7, legacy.to_string(), false),
        (SmtVersion::V2_7, modern.to_string(), true),
        // a declaration takes effect on what follows it, in both directions
        (SmtVersion::V2_7, format!("{to_2_0}{legacy}"), true),
        (SmtVersion::V2_7, format!("{to_2_0}{modern}"), false),
        (SmtVersion::V2_0, format!("{to_2_6}{modern}"), true),
        (SmtVersion::V2_0, format!("{to_2_6}{legacy}"), false),
        // and not on what precedes it
        (SmtVersion::V2_7, format!("{modern}{to_2_0}{legacy}"), true),
        (SmtVersion::V2_7, format!("{legacy}{to_2_0}"), false),
        (SmtVersion::V2_0, format!("{legacy}{to_2_6}{modern}"), true),
        // a declaration of another version with the same strings changes nothing
        (SmtVersion::V2_7, format!("{to_2_6}{modern}"), true),
        (SmtVersion::V2_7, format!("{to_2_6}{legacy}"), false),
    ] {
        let result = read_from(initial, input.clone());
        match result {
            Ok(()) => assert!(ok, "{input} from {initial:?} should not lex"),
            Err((kind, _, _)) => {
                assert!(!ok, "{input} from {initial:?}: {kind}");
                assert!(
                    kind.starts_with("Lexical("),
                    "{input} from {initial:?}: {kind}"
                );
            }
        }
    }

    // what follows the declaration may lex only in the declared version, also when
    // the rest of the input had been cut wrongly before the declaration was parsed:
    // here the old regime ends the string at its second quote and the new one does not
    let tail = "(set-info :a \"x\\\" \") (check-sat)";
    assert_eq!(
        read_from(SmtVersion::V2_7, format!("{to_2_0}{tail}")),
        Ok(())
    );
    let tail = "(set-info :a \"x\\\")(check-sat)";
    assert_eq!(
        read_from(SmtVersion::V2_0, format!("{to_2_6}{tail}")),
        Ok(())
    );

    // several declarations switch back and forth
    let unlimited = posture(|builder| {
        builder
            .add_allowed(SmtVersion::V2_0)
            .set_max_declarations(None);
    });
    let input =
        format!("{modern}{to_2_0}{legacy}(set-info :smt-lib-version 2.5){modern}{to_2_0}{legacy}");
    assert_eq!(read(&input, SmtVersion::V2_6, unlimited), Ok(()));
}

#[test]
fn the_string_escapes_reset_with_the_input() {
    let declared = b"(set-info :smt-lib-version 2.0)(set-info :a \"x\\\"y\")";
    let legacy = b"(set-info :a \"x\\\"y\")";
    let mut handler = SmtSyntaxChecker;
    let mut reader = SmtReader::script(&mut handler, SmtVersion::V2_7, every_version_allowed());
    // every input can switch to the 2.0 strings ...
    for _ in 0..2 {
        assert!(matches!(
            reader.read_slice(declared),
            Ok(ControlFlow::Continue(()))
        ));
        assert!(matches!(reader.read_eof(), Ok(ControlFlow::Break(_))));
    }
    // ... and the next one starts with the strings of the initial version again
    let err = reader
        .read_slice(legacy)
        .expect_err("a backslash does not escape in the initial version");
    assert!(matches!(err.kind(), SmtReadErrorKind::Lexical(_)));
}

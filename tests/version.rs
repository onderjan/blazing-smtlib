//! Public-API tests of SMT-LIB version handling through the whole reader:
//! the reserved words of each version, the version declaration
//! `(set-info :smt-lib-version <version>)` that switches between them,
//! the posture that limits the declarations, and the reset of both
//! at the end of every input.

mod reserved_words;

use reserved_words::reserved_words;

use std::ops::ControlFlow;

use smt_parser_rs::{
    CheckStandardSyntax, NonstandardCommandError, String8,
    read::{
        SmtReadError, SmtReadErrorKind, SmtReader,
        parser::{CommandParser, CommandParserStop, SyntaxErrorKind},
    },
    token::{
        CommandNameReserved, GeneralReserved, Reserved, SmtVersion, SmtVersionPosture,
        SmtVersionPostureBuilder,
    },
};

type ReadError = SmtReadError<NonstandardCommandError>;

/// The versions with their spelling in a declaration, oldest first.
const VERSIONS: [(SmtVersion, &str); 3] = [
    (SmtVersion::V2_5, "2.5"),
    (SmtVersion::V2_6, "2.6"),
    (SmtVersion::V2_7, "2.7"),
];

/// The index in [`VERSIONS`] of the version that made the word reserved.
fn introduced_in(word: &str) -> usize {
    match word {
        "lambda" | "declare-sort-parameter" | "define-const" => 2,
        "match" | "declare-datatype" | "declare-datatypes" => 1,
        _ => 0,
    }
}

/// Reads the input as a script in the given pieces, then the end of the input,
/// stopping at the first error.
fn read_pieces(
    pieces: &[&[u8]],
    initial: SmtVersion,
    posture: SmtVersionPosture,
) -> Result<(), ReadError> {
    let mut handler = CheckStandardSyntax;
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

/// Requires a syntax error of the given kind spanning the given byte offsets.
#[track_caller]
fn assert_syntax_error(outcome: Outcome, kind: SyntaxErrorKind, start: u64, end: u64) {
    assert_eq!(
        outcome,
        Err((
            format!("{:?}", SmtReadErrorKind::<()>::Parser(kind)),
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
    for (index, (version, _)) in VERSIONS.into_iter().enumerate() {
        for word in reserved_words() {
            let expected = introduced_in(word) <= index;
            // the word itself is known from the latest version
            let reserved = Reserved::from_bytes_opt(word.as_bytes(), SmtVersion::V2_7)
                .unwrap_or_else(|| panic!("{word:?} should be reserved in the latest version"));
            let symbol = String8::from_vec(word.as_bytes().to_vec());
            let group = match reserved {
                Reserved::General(_) => {
                    GeneralReserved::from_bytes_opt(word.as_bytes(), version).is_some()
                }
                Reserved::CommandName(_) => {
                    CommandNameReserved::from_bytes_opt(word.as_bytes(), version).is_some()
                }
            };
            let found = [
                Reserved::from_bytes_opt(word.as_bytes(), version) == Some(reserved),
                Reserved::from_symbol_opt(&symbol, version) == Some(reserved),
                group,
                reserved.is_in_version(version),
            ];
            assert_eq!(found, [expected; 4], "{word:?} in {version:?}");
            // and when it is not reserved yet, nothing else is found in its place
            if !expected {
                assert_eq!(Reserved::from_bytes_opt(word.as_bytes(), version), None);
            }
        }
    }
}
#[test]
fn each_version_reserves_exactly_its_words() {
    // a reserved word cannot name a constant, a word not yet reserved can;
    // the version is either the initial one or declared from another one
    let mut failures = Vec::new();
    for (index, (version, spelling)) in VERSIONS.into_iter().enumerate() {
        for word in reserved_words() {
            let reserved = introduced_in(word) <= index;
            let declare = format!("(declare-const {word} Bool)");
            let switched = format!("(set-info :smt-lib-version {spelling}){declare}");
            let (other, _) = VERSIONS[(index + 1) % VERSIONS.len()];
            for (input, initial) in [(&declare, version), (&switched, other)] {
                let rejected =
                    read_pieces(&[input.as_bytes()], initial, SmtVersionPosture::default())
                        .is_err();
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
        ("(declare-datatype T ((c)))", 1),
        ("(declare-datatypes ((T 0)) (((c))))", 1),
        ("(declare-sort-parameter A)", 2),
        ("(define-const c Bool true)", 2),
    ] {
        for (index, (version, spelling)) in VERSIONS.into_iter().enumerate() {
            let input = format!("(set-info :smt-lib-version {spelling}){command}");
            let result = read_default(&input);
            if index >= since {
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
    assert_syntax_error(result, SyntaxErrorKind::ExpectedSymbol, 15, 21);
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
    assert_syntax_error(result, SyntaxErrorKind::ExpectedTerm, 66, 72);
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
            SyntaxErrorKind::ExpectedSymbol,
            start,
            start + 6,
        );
    }
}

#[test]
fn a_version_that_is_not_supported_is_rejected() {
    // the value must be a decimal that names a version the posture allows;
    // the error is at the value, or at what stands in its place
    for (value, end) in [
        // versions outside the supported ones, and decimals that are no versions
        ("2.0", 30),
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
        (":version", 35),
        ("(2.6)", 28),
        // no value at all
        ("", 28),
    ] {
        let input = format!("(set-info :smt-lib-version {value})");
        assert_syntax_error(
            read_default(&input),
            SyntaxErrorKind::UnsupportedVersion,
            27,
            end,
        );
    }

    // a version the library knows is rejected the same way when the posture excludes it
    for (excluded, spelling) in VERSIONS {
        let without = posture(|builder| {
            builder.remove_allowed(excluded);
        });
        for (_, declared) in VERSIONS {
            let input = format!("(set-info :smt-lib-version {declared})");
            let result = read(&input, SmtVersion::V2_7, without.clone());
            if declared == spelling {
                assert_syntax_error(result, SyntaxErrorKind::UnsupportedVersion, 27, 30);
            } else {
                assert_eq!(result, Ok(()), "{declared} without {excluded:?}");
            }
        }
    }
    let none = posture(|builder| {
        builder.clear_allowed();
    });
    let result = read("(set-info :smt-lib-version 2.7)", SmtVersion::V2_7, none);
    assert_syntax_error(result, SyntaxErrorKind::UnsupportedVersion, 27, 30);
}

#[test]
fn a_version_value_is_followed_by_the_closing_parenthesis() {
    let result = read_default("(set-info :smt-lib-version 2.6 2.6)");
    let (kind, start, end) = result.expect_err("a second value is no attribute");
    assert!(kind.starts_with("Parser(ExpectedToken("), "{kind}");
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
            SyntaxErrorKind::TooManyVersionDeclarations(1),
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
        SyntaxErrorKind::TooManyVersionDeclarations(0),
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
        SyntaxErrorKind::TooManyVersionDeclarations(2),
        91,
        94,
    );
    let unlimited = posture(|builder| {
        builder.set_max_declarations(None);
    });
    let input = format!("{three}(declare-const lambda Bool)");
    assert_syntax_error(
        read(&input, SmtVersion::V2_7, unlimited.clone()),
        SyntaxErrorKind::ExpectedSymbol,
        110,
        116,
    );
    let input = format!("{two}(declare-const match Bool)");
    assert_eq!(read(&input, SmtVersion::V2_7, unlimited), Ok(()));

    // a rejected version is reported before the limit
    let result = read_default("(set-info :smt-lib-version 2.6)(set-info :smt-lib-version 2.0)");
    assert_syntax_error(result, SyntaxErrorKind::UnsupportedVersion, 58, 61);
}

#[test]
fn the_version_and_the_declaration_count_reset_with_the_input() {
    let declared = b"(set-info :smt-lib-version 2.6)(declare-const lambda Bool)";
    let undeclared = b"(declare-const lambda Bool)";
    for ending in [&b""[..], b"(exit)"] {
        let mut handler = CheckStandardSyntax;
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
            SmtReadErrorKind::Parser(SyntaxErrorKind::ExpectedSymbol)
        ));
    }
}

#[test]
fn a_command_parser_reports_the_declaration_without_applying_it() {
    // PINNED, NOT DECIDED: the one-command parser finishes with the declared
    // version and its span, applies no posture and switches nothing, and the
    // reader is back in its initial version for the next command.
    let mut handler = CheckStandardSyntax;
    let mut reader = SmtReader::with_parser(&mut handler, CommandParser::new(), SmtVersion::V2_7);
    let mut stop = |input: &[u8]| -> Result<CommandParserStop, ReadError> {
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
                CommandParserStop::SetVersion(declared, span) => {
                    assert_eq!(declared, version);
                    assert_eq!((span.start().offset(), span.end().offset()), (27, 30));
                }
                other => panic!("expected a version declaration, got {other:?}"),
            }
        }
    }
    assert_eq!(
        stop(b"(set-info :status sat)").expect("another attribute"),
        CommandParserStop::Command
    );
    // lambda is still reserved after the declarations of 2.5 and 2.6
    assert!(stop(b"(set-info :smt-lib-version 2.6)").is_ok());
    assert!(stop(b"(declare-const lambda Bool)").is_err());
}

//! Tests of the library's `SmtSyntaxChecker` itself.
//!
//! They test the Rust interface itself: the checker is a handler of the Rust
//! library, which the Lean driver cannot run, so they call the Rust parser
//! directly whatever `BLAZING_SMTLIB_LEAN_DRIVER` says. The tests that run
//! through `parse_backend` use its stand-in `parse_backend::SyntaxChecker`
//! instead; these tests check that every call of the checker accepts, that a
//! nonstandard command is rejected by its name, and that the stand-in gives
//! the same outcome as the checker.

mod parse_backend;

use blazing_smtlib::{
    SmtNonstandardCommandError, SmtReadError, SmtReadErrorCause, SmtReader, SmtSyntaxChecker,
    SmtVersion, SmtVersionPosture, read_smt,
};
use parse_backend::{Adapt, SyntaxChecker};

/// A script that makes the parser call every method of the handler and of
/// the command handler but `nonstandard_command`.
const EVERY_CALL: &[u8] = b"\
(set-info :smt-lib-version 2.7)
(set-info :status sat)
(set-info :source |a source|)
(set-info :notes (a 1 1.5 #x0F #b01 \"s\" :k (b) _ ! as par))
(set-option :produce-models true)
(set-option :interactive-mode)
(set-logic ALL)
(declare-sort U 0)
(declare-sort-parameter A)
(define-sort Pair (X Y) (Array X Y))
(declare-const c Int)
(declare-fun f (Int Int) Int)
(define-const d Int 5)
(define-fun g ((x Int)) Int (+ x 1))
(define-fun-rec h ((x Int)) Int (h x))
(define-funs-rec ((p ((x Int)) Bool) (q ((x Int)) Bool)) ((q x) (p x)))
(declare-datatype List (par (T) ((nil) (cons (head T) (tail (List T))))))
(declare-datatypes ((Tree 0) (Forest 0))
  (((leaf) (node (kids Forest))) ((empty) (more (first Tree) (rest Forest)))))
(assert (! (forall ((x Int)) (exists ((y Int)) (= y x))) :named a1 :pattern ((f x x))))
(assert (let ((z 1) (w #x0F) (v #b01) (u 1.5) (t \"s\")) (> z 0)))
(assert (= ((_ extract 3 0) ((as const (Array Int Int)) 0)) (as c Int)))
(assert (= g (lambda ((x Int)) (+ x 1))))
(assert (match l ((nil 0) ((cons h t) h) (_ 1))))
(check-sat)
(check-sat-assuming (a1 (not a1)))
(get-value (c d))
(get-assertions)
(get-assignment)
(get-model)
(get-proof)
(get-unsat-assumptions)
(get-unsat-core)
(get-info :name)
(get-option :produce-models)
(echo \"hi\")
(push 1)
(pop 1)
(reset-assertions)
(reset)
(exit)
";

/// Inputs on which the stand-in is compared with the checker: valid
/// scripts and an input for every way reading can fail.
const INPUTS: &[&[u8]] = &[
    b"",
    b"; comment only",
    EVERY_CALL,
    b"(set-logic QF_UF)\n(check-sat)\n",
    b"(check-sat)\n(exit)\n(this is never parsed",
    b"(set-info :smt-lib-version 2.6)(declare-fun x () Int)",
    b"(set-info :smt-lib-version 2.6)(set-info :smt-lib-version 2.7)",
    b"(frobnicate 1)",
    b"(|check-sat|)",
    b"(check-sat)\n(my-command (f x) y)",
    b"(check-sat)\n(assert )",
    b"(check-sat)\n\n  \"abc",
    b"(assert (let ((x 1)) ))",
    b"(let ((x 1)) x)",
    b"(declare-const ! Bool)",
    b"(assert (match x ()))",
    b"(declare-sort-parameter A)",
    b"(check-sat",
    b")",
];

fn read_with_checker(input: &[u8]) -> Result<(), SmtReadError<SmtNonstandardCommandError>> {
    read_smt(&mut SmtSyntaxChecker, input)
}

fn read_with_stand_in(input: &[u8]) -> Result<(), SmtReadError<SmtNonstandardCommandError>> {
    read_smt(&mut Adapt(&mut SyntaxChecker), input)
}

/// The outcome of reading, as text: `ok`, or the cause and the span of the
/// error.
fn outcome(result: Result<(), SmtReadError<SmtNonstandardCommandError>>) -> String {
    match result {
        Ok(()) => "ok".to_string(),
        Err(err) => {
            let span = err.span();
            let (start, end) = (span.start(), span.end());
            format!(
                "{:?} at {}:{}:{}..{}:{}:{}",
                err.cause(),
                start.offset(),
                start.line(),
                start.column(),
                end.offset(),
                end.line(),
                end.column(),
            )
        }
    }
}

/// The name of the nonstandard command that the checker rejected, and the
/// span of the rejection as byte offsets.
#[track_caller]
fn rejected(input: &[u8]) -> (Vec<u8>, (u64, u64)) {
    let err = read_with_checker(input).expect_err("expected the checker to reject, got Ok");
    let span = err.span();
    let offsets = (span.start().offset(), span.end().offset());
    match err.into_cause() {
        SmtReadErrorCause::Handler(err) => {
            let name = err.into_name();
            (name.as_slice().to_vec(), offsets)
        }
        other => panic!("expected the checker's error, got {other:?}"),
    }
}

#[test]
fn every_call_of_the_checker_accepts() {
    if let Err(err) = read_with_checker(EVERY_CALL) {
        panic!("the checker rejected the script: {}", outcome(Err(err)));
    }
}

#[test]
fn every_call_of_the_checker_accepts_in_any_pieces() {
    for size in [1, 2, 7, 64] {
        let mut checker = SmtSyntaxChecker;
        let mut reader =
            SmtReader::script(&mut checker, SmtVersionPosture::default(), SmtVersion::V2_7);
        for piece in EVERY_CALL.chunks(size) {
            if let Err(err) = reader.read_slice(piece) {
                panic!(
                    "the checker rejected a piece of size {size}: {}",
                    outcome(Err(err))
                );
            }
        }
        if let Err(err) = reader.read_eof() {
            panic!(
                "the checker rejected the end of the input: {}",
                outcome(Err(err))
            );
        }
    }
}

#[test]
fn a_nonstandard_command_is_rejected_by_its_name() {
    assert_eq!(
        rejected(b"(frobnicate 1)"),
        (b"frobnicate".to_vec(), (1, 11))
    );
}

#[test]
fn a_quoted_standard_command_name_is_rejected_as_nonstandard() {
    assert_eq!(rejected(b"(|check-sat|)"), (b"check-sat".to_vec(), (1, 12)));
}

#[test]
fn a_nonstandard_command_after_standard_ones_is_rejected_at_its_name() {
    assert_eq!(
        rejected(b"(check-sat)\n(my-command (f x) y)"),
        (b"my-command".to_vec(), (13, 23))
    );
}

#[test]
fn the_stand_in_gives_the_outcome_of_the_checker() {
    for input in INPUTS {
        assert_eq!(
            outcome(read_with_stand_in(input)),
            outcome(read_with_checker(input)),
            "on {:?}",
            String::from_utf8_lossy(input)
        );
    }
}

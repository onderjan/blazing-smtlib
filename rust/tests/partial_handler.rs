//! Tests of `SmtPartialCommandHandler`: a handler that implements only some
//! commands is a command handler, the commands it implements work, and every
//! other command fails with an error naming exactly that command.
//!
//! They check the Rust interface itself (the trait's provided callbacks), so
//! they run the Rust library whatever `parse_backend` selects.

use std::collections::HashSet;

use blazing_smtlib::{
    SmtHandler, SmtPartialCommandError, SmtPartialCommandHandler, SmtReadError, SmtReadErrorCause,
    grammar::{
        SmtAttributeValue, SmtAttributes, SmtBindings, SmtFunctionSignature, SmtFunctionSignatures,
        SmtMatchCases, SmtPattern, SmtQuantifierKind, SmtSExpr, SmtSort, SmtSortArities,
        SmtSortedVars, SmtSymbols, SmtTerm,
    },
    lexicon::{SmtKeyword, SmtSymbol},
    read_smt,
    token::SmtCommandNameReserved,
    version::SmtVersion,
};

/// The error of the handler's own.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Refused;

type Error = SmtPartialCommandError<Refused>;

/// A solver that implements `set-logic`, `declare-const` and `check-sat`,
/// and, by `LEVEL`, more of the callbacks of the commands that make several:
///
/// - 1: the start callbacks of the commands,
/// - 2: also the start callbacks of each function body and datatype,
/// - 3: also the end callbacks of each function body and datatype.
///
/// It logs the callbacks it implements as they are called.
#[derive(Default)]
struct Solver<const LEVEL: u8> {
    log: Vec<&'static str>,
}

impl<const LEVEL: u8> SmtHandler for Solver<LEVEL> {
    type Error = Error;
    type SExpr = ();
    type Attribute = ();
    type Sort = ();
    type Term = ();
    type Scope = ();

    fn set_version(&mut self, _version: SmtVersion) {}

    fn handle_sort(&mut self, _sort: SmtSort<'_, Self>) -> Result<(), Error> {
        Ok(())
    }
    fn handle_term(&mut self, _term: SmtTerm<'_, Self>) -> Result<(), Error> {
        Ok(())
    }
    fn handle_s_expr(&mut self, _expr: SmtSExpr<'_, Self>) -> Result<(), Error> {
        Ok(())
    }
    fn handle_attribute(
        &mut self,
        _name: SmtKeyword<'_>,
        _value: Option<SmtAttributeValue<'_, Self>>,
    ) -> Result<(), Error> {
        Ok(())
    }
    fn annotate_term(
        &mut self,
        _term: (),
        _attributes: SmtAttributes<'_, Self>,
    ) -> Result<(), Error> {
        Ok(())
    }
    fn start_let(&mut self, _bindings: SmtBindings<'_, ()>) -> Result<(), Error> {
        Ok(())
    }
    fn end_let(&mut self, _scope: (), _body: ()) -> Result<(), Error> {
        Ok(())
    }
    fn start_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _vars: SmtSortedVars<'_, ()>,
    ) -> Result<(), Error> {
        Ok(())
    }
    fn end_quantifier(
        &mut self,
        _kind: SmtQuantifierKind,
        _scope: (),
        _body: (),
    ) -> Result<(), Error> {
        Ok(())
    }
    fn start_lambda(&mut self, _vars: SmtSortedVars<'_, ()>) -> Result<(), Error> {
        Ok(())
    }
    fn end_lambda(&mut self, _scope: (), _body: ()) -> Result<(), Error> {
        Ok(())
    }
    fn start_match(&mut self, _scrutinee: &()) -> Result<(), Error> {
        Ok(())
    }
    fn start_match_case(&mut self, _scrutinee: &(), _pattern: SmtPattern<'_>) -> Result<(), Error> {
        Ok(())
    }
    fn end_match_case(&mut self, _scope: (), _scrutinee: &(), _term: ()) -> Result<(), Error> {
        Ok(())
    }
    fn end_match(&mut self, _scrutinee: (), _cases: SmtMatchCases<'_, Self>) -> Result<(), Error> {
        Ok(())
    }
}

/// Checks a logic as the handler's own code would: with the handler's own
/// error, which `?` turns into the partial handler's.
fn check_logic(logic: SmtSymbol<'_>) -> Result<(), Refused> {
    if logic.as_slice() == b"BAD" {
        Err(Refused)
    } else {
        Ok(())
    }
}

/// The callbacks every level implements: the logic `BAD` is refused.
macro_rules! base_commands {
    () => {
        fn command_set_logic(&mut self, logic: SmtSymbol<'_>) -> Result<(), Error> {
            check_logic(logic)?;
            self.log.push("set-logic");
            Ok(())
        }
        fn command_declare_const(&mut self, _name: SmtSymbol<'_>, _sort: ()) -> Result<(), Error> {
            self.log.push("declare-const");
            Ok(())
        }
        fn command_check_sat(&mut self) -> Result<(), Error> {
            self.log.push("check-sat");
            Ok(())
        }
    };
}

/// The start callbacks of the commands, from level 1.
macro_rules! command_starts {
    () => {
        fn start_define_sort(
            &mut self,
            _name: SmtSymbol<'_>,
            _params: SmtSymbols<'_>,
        ) -> Result<(), Error> {
            self.log.push("start_define_sort");
            Ok(())
        }
        fn start_define_fun(
            &mut self,
            _signature: SmtFunctionSignature<'_, ()>,
        ) -> Result<(), Error> {
            self.log.push("start_define_fun");
            Ok(())
        }
        fn start_define_fun_rec(
            &mut self,
            _signature: SmtFunctionSignature<'_, ()>,
        ) -> Result<(), Error> {
            self.log.push("start_define_fun_rec");
            Ok(())
        }
        fn start_define_funs_rec(
            &mut self,
            _signatures: SmtFunctionSignatures<'_, ()>,
        ) -> Result<(), Error> {
            self.log.push("start_define_funs_rec");
            Ok(())
        }
        fn start_declare_datatype(
            &mut self,
            _name: SmtSymbol<'_>,
            _params: SmtSymbols<'_>,
        ) -> Result<(), Error> {
            self.log.push("start_declare_datatype");
            Ok(())
        }
        fn start_declare_datatypes(
            &mut self,
            _introductions: SmtSortArities<'_>,
        ) -> Result<(), Error> {
            self.log.push("start_declare_datatypes");
            Ok(())
        }
    };
}

/// The start callbacks of each function body and datatype, from level 2.
macro_rules! inner_starts {
    () => {
        fn start_recursive_body(
            &mut self,
            _signature: SmtFunctionSignature<'_, ()>,
        ) -> Result<(), Error> {
            self.log.push("start_recursive_body");
            Ok(())
        }
        fn start_datatype_declaration(
            &mut self,
            _sort_params: SmtSymbols<'_>,
        ) -> Result<(), Error> {
            self.log.push("start_datatype_declaration");
            Ok(())
        }
    };
}

/// The end callbacks of each function body and datatype, at level 3.
macro_rules! inner_ends {
    () => {
        fn end_recursive_body(&mut self, _term: ()) -> Result<(), Error> {
            self.log.push("end_recursive_body");
            Ok(())
        }
        fn end_datatype_declaration(
            &mut self,
            _constructors: blazing_smtlib::grammar::SmtConstructors<'_, ()>,
        ) -> Result<(), Error> {
            self.log.push("end_datatype_declaration");
            Ok(())
        }
    };
}

impl SmtPartialCommandHandler for Solver<0> {
    type HandlerError = Refused;
    type NonstandardParser = std::convert::Infallible;
    base_commands!();
}

impl SmtPartialCommandHandler for Solver<1> {
    type HandlerError = Refused;
    type NonstandardParser = std::convert::Infallible;
    base_commands!();
    command_starts!();
}

impl SmtPartialCommandHandler for Solver<2> {
    type HandlerError = Refused;
    type NonstandardParser = std::convert::Infallible;
    base_commands!();
    command_starts!();
    inner_starts!();
}

impl SmtPartialCommandHandler for Solver<3> {
    type HandlerError = Refused;
    type NonstandardParser = std::convert::Infallible;
    base_commands!();
    command_starts!();
    inner_starts!();
    inner_ends!();
}

/// What every script starts with: commands the solver implements.
const PREFIX: &str = "(set-logic ALL) (check-sat) ";

/// Reads the prefix and the command with the solver, and returns the
/// error and the callbacks logged after those of the prefix.
fn fail<const LEVEL: u8>(command: &str) -> (SmtReadError<Error>, Vec<&'static str>)
where
    Solver<LEVEL>: SmtPartialCommandHandler<HandlerError = Refused>,
{
    let mut solver = Solver::<LEVEL>::default();
    let script = format!("{PREFIX}{command}");
    let err = read_smt(&mut solver, script.as_bytes())
        .expect_err("the solver does not implement the command");
    assert_eq!(
        solver.log[..2],
        ["set-logic", "check-sat"],
        "the prefix of {command:?}"
    );
    assert!(
        err.span().start().offset() >= PREFIX.len() as u64,
        "the error at {:?} is not in {command:?}",
        err.span()
    );
    (err, solver.log.split_off(2))
}

/// Checks that each command fails at level `LEVEL` naming the command, after
/// the callbacks given with it, and returns the names.
#[track_caller]
fn check_unsupported<const LEVEL: u8>(
    cases: &[(&str, SmtCommandNameReserved, &[&str])],
) -> Vec<SmtCommandNameReserved>
where
    Solver<LEVEL>: SmtPartialCommandHandler<HandlerError = Refused>,
{
    let mut names = Vec::new();
    for &(command, name, callbacks) in cases {
        // the case names the command it reads
        let word = command[1..]
            .split([' ', ')'])
            .next()
            .expect("a command has a name");
        assert_eq!(
            SmtCommandNameReserved::from_bytes(word.as_bytes(), SmtVersion::V2_7),
            Some(name),
            "the case of {command:?} names another command"
        );
        let (err, log) = fail::<LEVEL>(command);
        assert!(
            matches!(
                err.cause(),
                SmtReadErrorCause::Handler(SmtPartialCommandError::Unsupported(unsupported))
                    if *unsupported == name
            ),
            "{:?} for {command:?} at level {LEVEL}",
            err.cause()
        );
        assert_eq!(log, callbacks, "for {command:?} at level {LEVEL}");
        names.push(name);
    }
    names
}

#[test]
fn implemented_commands_are_handled() {
    let mut solver = Solver::<0>::default();
    read_smt(
        &mut solver,
        &b"(set-logic ALL) (declare-const x Int) (check-sat)"[..],
    )
    .unwrap_or_else(|err| panic!("unexpected error {:?}", err.cause()));
    assert_eq!(solver.log, ["set-logic", "declare-const", "check-sat"]);
}

#[test]
fn an_error_of_an_implemented_callback_is_the_handlers_own() {
    let err = read_smt(
        &mut Solver::<0>::default(),
        &b"(check-sat) (set-logic BAD)"[..],
    )
    .expect_err("the logic is refused");
    assert!(
        matches!(
            err.cause(),
            SmtReadErrorCause::Handler(SmtPartialCommandError::Handler(Refused))
        ),
        "{:?}",
        err.cause()
    );
}

#[test]
fn every_unimplemented_standard_command_fails_naming_itself() {
    use SmtCommandNameReserved as N;
    let none: &[&str] = &[];
    let names = check_unsupported::<0>(&[
        ("(assert true)", N::Assert, none),
        ("(check-sat-assuming (a))", N::CheckSatAssuming, none),
        ("(declare-datatype D ((c)))", N::DeclareDatatype, none),
        (
            "(declare-datatypes ((D 0)) (((c))))",
            N::DeclareDatatypes,
            none,
        ),
        ("(declare-fun f (Int) Int)", N::DeclareFun, none),
        ("(declare-sort S 0)", N::DeclareSort, none),
        ("(declare-sort-parameter X)", N::DeclareSortParameter, none),
        ("(define-const c Int 1)", N::DefineConst, none),
        ("(define-fun f ((x Int)) Int x)", N::DefineFun, none),
        ("(define-fun-rec f ((x Int)) Int x)", N::DefineFunRec, none),
        (
            "(define-funs-rec ((f ((x Int)) Int)) (x))",
            N::DefineFunsRec,
            none,
        ),
        ("(define-sort S () Int)", N::DefineSort, none),
        ("(echo \"a\")", N::Echo, none),
        ("(exit)", N::Exit, none),
        ("(get-assertions)", N::GetAssertions, none),
        ("(get-assignment)", N::GetAssignment, none),
        ("(get-info :name)", N::GetInfo, none),
        ("(get-model)", N::GetModel, none),
        ("(get-option :x)", N::GetOption, none),
        ("(get-proof)", N::GetProof, none),
        ("(get-unsat-assumptions)", N::GetUnsatAssumptions, none),
        ("(get-unsat-core)", N::GetUnsatCore, none),
        ("(get-value (x))", N::GetValue, none),
        ("(pop 1)", N::Pop, none),
        ("(push 1)", N::Push, none),
        ("(reset)", N::Reset, none),
        ("(reset-assertions)", N::ResetAssertions, none),
        ("(set-info :source a)", N::SetInfo, none),
        ("(set-option :print-success true)", N::SetOption, none),
    ]);
    // with the three it implements, every standard command is covered once
    let mut covered: HashSet<_> = names.iter().copied().collect();
    assert_eq!(covered.len(), names.len(), "a command is checked twice");
    covered.extend([N::SetLogic, N::DeclareConst, N::CheckSat]);
    assert_eq!(covered.len(), 32, "a standard command is not checked");
}

#[test]
fn every_unimplemented_callback_of_a_command_fails_naming_the_command() {
    use SmtCommandNameReserved as N;
    // the end callbacks of the commands
    check_unsupported::<1>(&[
        (
            "(define-sort S () Int)",
            N::DefineSort,
            &["start_define_sort"],
        ),
        (
            "(define-fun f ((x Int)) Int x)",
            N::DefineFun,
            &["start_define_fun"],
        ),
        (
            "(define-fun-rec f ((x Int)) Int x)",
            N::DefineFunRec,
            &["start_define_fun_rec"],
        ),
        (
            "(declare-datatype D ((c)))",
            N::DeclareDatatype,
            &["start_declare_datatype"],
        ),
    ]);

    // the callbacks of each function body and datatype, then the end
    // callbacks of the commands
    let funs_rec = "(define-funs-rec ((f ((x Int)) Int)) (x))";
    let datatypes = "(declare-datatypes ((D 0)) (((c))))";
    check_unsupported::<1>(&[
        (funs_rec, N::DefineFunsRec, &["start_define_funs_rec"]),
        (datatypes, N::DeclareDatatypes, &["start_declare_datatypes"]),
    ]);
    check_unsupported::<2>(&[
        (
            funs_rec,
            N::DefineFunsRec,
            &["start_define_funs_rec", "start_recursive_body"],
        ),
        (
            datatypes,
            N::DeclareDatatypes,
            &["start_declare_datatypes", "start_datatype_declaration"],
        ),
    ]);
    check_unsupported::<3>(&[
        (
            funs_rec,
            N::DefineFunsRec,
            &[
                "start_define_funs_rec",
                "start_recursive_body",
                "end_recursive_body",
            ],
        ),
        (
            datatypes,
            N::DeclareDatatypes,
            &[
                "start_declare_datatypes",
                "start_datatype_declaration",
                "end_datatype_declaration",
            ],
        ),
    ]);
}

#[test]
fn a_nonstandard_command_fails_naming_itself() {
    let err = read_smt(
        &mut Solver::<0>::default(),
        &b"(check-sat) (minimize x)"[..],
    )
    .expect_err("the solver has no nonstandard commands");
    assert!(
        matches!(
            err.cause(),
            SmtReadErrorCause::Handler(SmtPartialCommandError::UnsupportedNonstandard(name))
                if name.as_slice() == b"minimize"
        ),
        "{:?}",
        err.cause()
    );
    // the error spans the name
    assert_eq!(
        (err.span().start().offset(), err.span().end().offset()),
        (13, 21)
    );
}

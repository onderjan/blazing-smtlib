//! The spellings of the reserved words, shared by the tests that go through all of them.

/// The reserved words of the grammar, which are not command names.
pub const GRAMMAR_WORDS: &[&str] = &[
    "!",
    "_",
    "as",
    "BINARY",
    "DECIMAL",
    "exists",
    "forall",
    "HEXADECIMAL",
    "lambda",
    "let",
    "match",
    "NUMERAL",
    "par",
    "STRING",
];

/// The standard command names, which the standard makes reserved words too.
pub const COMMAND_NAMES: &[&str] = &[
    "assert",
    "check-sat",
    "check-sat-assuming",
    "declare-const",
    "declare-datatype",
    "declare-datatypes",
    "declare-fun",
    "declare-sort",
    "declare-sort-parameter",
    "define-const",
    "define-fun",
    "define-fun-rec",
    "define-funs-rec",
    "define-sort",
    "echo",
    "exit",
    "get-assertions",
    "get-assignment",
    "get-info",
    "get-model",
    "get-option",
    "get-proof",
    "get-unsat-assumptions",
    "get-unsat-core",
    "get-value",
    "pop",
    "push",
    "reset",
    "reset-assertions",
    "set-info",
    "set-logic",
    "set-option",
];

/// Every reserved word: the grammar's words, then the command names.
pub fn reserved_words() -> impl Iterator<Item = &'static str> {
    GRAMMAR_WORDS.iter().chain(COMMAND_NAMES).copied()
}

# blazing-smtlib: Fast, safe, dependency-free SMT-LIB parsing

A high-performance strict parsing library for [SMT-LIB 2](https://smt-lib.org/)
with no dependencies other than [std](https://doc.rust-lang.org/std/) and no
unsafe code. SMT-LIB versions 2.0, 2.5, 2.6, and 2.7 are supported, with 2.0
disabled by default due to its deprecated status.

The library is designed for composability and, in addition to reading SMT-LIB
scripts, supports reading and writing of e.g. bare SMT-LIB terms, commands, or
full SMT-LIB solver responses using custom parsers.

A port of the library for the Lean language is also offered in the [library
repository](https://github.com/onderjan/blazing-smtlib).

## Usage

To read an SMT-LIB script from file and check its syntax is valid:

```rust,no_run
use blazing_smtlib::{read_smt_file, SmtSyntaxChecker};
read_smt_file(&mut SmtSyntaxChecker, "file.smt2").expect("should be a valid SMT-LIB script");
```

`SmtSyntaxChecker` implements `SmtHandler` that handles SMT-LIB syntactic
categories (identifiers, sorts, terms, etc.), and `SmtCommandHandler` that
handles standard SMT-LIB commands (`assert`, `check-sat`, etc.). SMT solvers can
implement `SmtHandler` and `SmtCommandHandler` to handle SMT-LIB scripts,
including custom parsing of non-standard commands. See the handler documentation
for details.

The function `read_smt_file` is a simplified caller for `SmtReader`, which
supports reading SMT-LIB scripts as well as other categories and commands. The
reader is itself a wrapper for `SmtLexer` and a selectable parser implementing
`SmtParse`; these can be used separately in applications such as token
pretty-printing or parsing user-constructed tokens.

Tokens and syntactic nodes can be written using `SmtWriter`, which is
configurable for various whitespace formats including 1:1 reconstruction.

## Speed and Memory Consumption

The library uses a hand-written speed-optimised lexer and parsers with token
batching, zero-copy tokens, and resource arenas, making parsing on the SMT-LIB
corpus typically more than an order of magnitude faster than other Rust SMT-LIB
parsing libraries such as
[smt2parser](https://docs.rs/smt2parser/0.6.1/smt2parser/) or
[yaspar](https://docs.rs/yaspar/2.7.2/yaspar/).

(TODO speed table)

As the library parsers do not construct an abstract syntax tree, but instead
call handlers in a streaming fashion, the library's memory consumption tends to
be negligible compared to a handler that stores mappings of declared or defined
symbols and terms, such as ones used for SMT solvers.

## Licence

Licensed under either of Apache License, Version 2.0 or MIT licence at your
option. Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in this crate by you, as defined in the Apache-2.0
licence, shall be dual licensed as above, without any additional terms or
conditions.

## Generative AI Policy

The core library code is human-written, with the shape of its API decided by the
maintainer. Generative AI is used only for experiments and for carefully
reviewed changes where the semantic shape is clear but implementing them by hand
is cumbersome (when explicitly prompted to do them). Generative AI is used to
write benchmarks and tests (including unit tests).

See the [repository](https://github.com/onderjan/blazing-smtlib) for more
information.

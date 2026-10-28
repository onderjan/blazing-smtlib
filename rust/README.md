# blazing-smtlib: Fast, safe, dependency-free SMT-LIB parsing

A high-performance strict parsing library for [SMT-LIB 2](https://smt-lib.org/)
with no dependencies other than [std](https://doc.rust-lang.org/std/) and no
unsafe code. SMT-LIB versions 2.0, 2.5, 2.6, and 2.7 are supported, with 2.0
disabled by default due to its deprecated status.

The library is designed for composability and, in addition to reading
SMT-LIB scripts, supports reading and writing of e.g. bare SMT-LIB terms,
commands, or full SMT-LIB solver responses using custom parsers.

**BSmtLib**, a port of **blazing-smtlib** for the Lean language, is also offered
in the [library repository](https://github.com/onderjan/blazing-smtlib).

## Usage

To read an SMT-LIB script from file and check its syntax is valid:

```rust,no_run
use blazing_smtlib::{read_smt_file, SmtSyntaxChecker};
read_smt_file(&mut SmtSyntaxChecker, "file.smt2").expect("should be a valid SMT-LIB script");
```

[`SmtSyntaxChecker`] implements [`SmtHandler`] that handles SMT-LIB syntactic
categories (sorts, terms, etc.), and [`SmtCommandHandler`] that
handles standard SMT-LIB commands (`assert`, `check-sat`, etc.). SMT solvers can
implement [`SmtHandler`] and [`SmtCommandHandler`] to handle SMT-LIB scripts,
including custom parsing of non-standard commands. See the handler documentation
for details.

The function [`read_smt_file`] is a simplified caller for [`SmtReader`], which
supports reading SMT-LIB scripts as well as other categories and commands. The
reader is itself a wrapper for [`SmtLexer`] and a selectable parser implementing
[`SmtParse`]; these can be used separately in applications such as token
pretty-printing or parsing user-constructed tokens.

Tokens and syntactic nodes can be written using [`SmtWriter`], which is
configurable for various whitespace formats including 1:1 reconstruction.

## Speed and Memory Consumption

The library contains a hand-written speed-optimised lexer and parsers with token
batching, zero-copy tokens, and resource arenas, making parsing on the SMT-LIB
corpus typically more than an order of magnitude faster than other commonly used
Rust SMT-LIB parsing libraries on medium-sized files.

| Library                                                              | Lexing (MB/s) | Parsing (MB/s) | Relative parsing time |
| -------------------------------------------------------------------- | ------------: | -------------: | --------------------: |
| **blazing-smtlib**                                                   |          1150 |            498 |                    1× |
| [**yaspar 2.7.2**](https://docs.rs/yaspar/2.7.2/yaspar/)             |            77 |             41 |                12.24× |
| [**smt2parser 0.6.1**](https://docs.rs/smt2parser/0.6.1/smt2parser/) |               |             29 |                17.41× |

The figures are geometric means over 9201 files from the 2025 SMT-LIB benchmark
corpus from 200 kB to 200 MB drawn by SMT-COMP-style rules, each read from
memory on an AMD Ryzen 9 9950X3D; the parsing comparisons are over 8856 files
both **yaspar** and **smt2parser** accepted[^1] (**blazing-smtlib** accepted all
9201). The lexer of **smt2parser** was not measured on its own.

As **blazing-smtlib** parsers do not construct an abstract syntax tree, but
instead call handlers in a streaming fashion, the library's memory consumption
tends to be negligible compared to a handler that stores mappings of declared or
defined symbols and terms, such as ones used for SMT solvers.

[^1]: **smt2parser** crashed on 8 files due to stack overflow; **yaspar**
    rejected 337 files, almost all of which declare the quoted symbol
    `|STRING|`, which it mistakes for the reserved word `STRING`; as **yaspar**
    only supports SMT-LIB 2.7 where `lambda` is a reserved word, it also
    rejected a few SMT-LIB 2.6 files that use `lambda` as a symbol.

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

[`SmtSyntaxChecker`]: https://docs.rs/blazing-smtlib/0.1.0/blazing_smtlib/struct.SmtSyntaxChecker.html
[`SmtHandler`]: https://docs.rs/blazing-smtlib/0.1.0/blazing_smtlib/trait.SmtHandler.html
[`SmtCommandHandler`]: https://docs.rs/blazing-smtlib/0.1.0/blazing_smtlib/trait.SmtCommandHandler.html
[`read_smt_file`]: https://docs.rs/blazing-smtlib/0.1.0/blazing_smtlib/fn.read_smt_file.html
[`SmtReader`]: https://docs.rs/blazing-smtlib/0.1.0/blazing_smtlib/struct.SmtReader.html
[`SmtLexer`]: https://docs.rs/blazing-smtlib/0.1.0/blazing_smtlib/lexer/struct.SmtLexer.html
[`SmtParse`]: https://docs.rs/blazing-smtlib/0.1.0/blazing_smtlib/parser/trait.SmtParse.html
[`SmtWriter`]: https://docs.rs/blazing-smtlib/0.1.0/blazing_smtlib/struct.SmtWriter.html

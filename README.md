# blazing-smtlib & BSmtLib: Fast, safe, dependency-free SMT-LIB parsing

**blazing-smtlib** is a high-performance strict parsing library for
[SMT-LIB 2](https://smt-lib.org/) in Rust, with no dependencies other than
[std](https://doc.rust-lang.org/std/) and no unsafe code. SMT-LIB versions 2.0,
2.5, 2.6, and 2.7 are supported, with 2.0 disabled by default due to its
deprecated status. The library is designed for composability and, in addition
to reading SMT-LIB scripts, supports reading and writing of e.g. bare SMT-LIB
terms, commands, or full SMT-LIB solver responses using custom parsers.

**BSmtLib** is a port of **blazing-smtlib** to Lean 4, with the same
architecture and public interface, adapted to Lean where needed. It has no
dependencies other than the Lean standard library, is panic-free, and is proven
to satisfy our formalised reading of the SMT-LIB standard.

## Repository structure

- [`rust/`](rust/README.md) – **blazing-smtlib**: the crate, its examples,
  tests, and benchmarks; published on
  [crates.io](https://crates.io/crates/blazing-smtlib) with its documentation on
  [docs.rs](https://docs.rs/blazing-smtlib).
- [`lean/`](lean/README.md) – **BSmtLib**: the library, the specification
  (`BSmtLibSpec`), the proofs (`Facts`), and the audit of the build.
- [`tools/`](tools/) – the drivers that run the Rust tests against **BSmtLib**
  (`lean-driver`) and answer the same requests with **blazing-smtlib**
  (`rust-lex-driver`).

## Testing

The Rust tests in `rust/tests` test both **blazing-smtlib** and **BSmtLib**:
**blazing-smtlib** by default and **BSmtLib** through a driver
(`tools/lean-driver`) that answers their requests with the Lean lexer,
parser, and writer, as described in
[`lean/driver-protocol.md`](lean/driver-protocol.md):

```
cd tools/lean-driver && lake build && cd ../../rust
BLAZING_SMTLIB_LEAN_DRIVER=../tools/lean-driver/.lake/build/bin/lean-driver cargo test
```

Beyond the tests, both libraries behave identically on every file of the 2025
SMT-LIB benchmark corpus.

## Speed and memory usage

| Library                   | Lexing (MB/s) | Parsing (MB/s) |
| ------------------------- | ------------: | -------------: |
| **blazing-smtlib** (Rust) |          1134 |            497 |
| **BSmtLib** (Lean)        |           273 |            116 |

The figures are geometric means over 9201 files from the 2025 SMT-LIB benchmark
corpus from 200 kB to 200 MB drawn by SMT-COMP-style rules, each read from
memory, in a 14-job parallel run on an AMD Ryzen 9 9950X3D.

As the parsers of both libraries do not construct an abstract syntax tree, but
instead call handlers in a streaming fashion, their memory consumption tends to
be negligible compared to a handler that stores mappings of declared or defined
symbols and terms, such as ones used for SMT solvers.

## Licence

Licensed under either of Apache License, Version 2.0 or MIT licence at your
option. Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in this repository by you, as defined in the Apache-2.0
licence, shall be dual licensed as above, without any additional terms or
conditions.

## Generative AI Policy

Generative AI (currently only Claude Code) is used for code review and help.
It makes no design decisions.

The main Rust library code is human-written, with the shape of its API
decided by the maintainer. Generative AI is used only for experiments and
for carefully reviewed changes where the semantic shape is clear but
implementing them by hand is cumbersome (when explicitly prompted to do them).
Generative AI is used to write benchmarks and tests (including unit tests).

The Lean library code is a port of the Rust library,
with generative AI used to port the code (as mechanically as possible).
The SMT-LIB corpus and library tests are used to check that both behave
identically.

Documentation (including examples) is either human-written or drafted
by generative AI and reviewed, then reworked if necessary. The Lean
documentation is ported from the Rust documentation by generative AI,
changed only where needed due to the language differences.

Commits are always done by a human, who reviews any generative-AI output.
Any commit that non-trivially uses generative AI either starts with
`Let <AI>...` (legacy style) or is signed off like so (new style):

```
Co-authored-by: <AI>
Signed-off-by: <committer>
```

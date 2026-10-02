# Instructions for AI agents

This repository holds a streaming parser for SMT-LIB in two implementations:

- `rust/`: the original implementation, published as the crate `blazing-smtlib`.
- `lean/`: a port of it to Lean 4.

The maintainer designs the library, reads every change and makes every commit.
The policy on the use of generative AI is in `README.md`; these instructions
are how agents follow it.

## For every agent

- Do not commit, push or rewrite history. Leave your changes in the working
  tree and say what you changed.
- Do not discard changes in the working tree that you did not make.
- Design decisions are the maintainer's. When a task needs a decision that has
  not been made, stop and ask in plain prose: what is open, the options with a
  concrete example, and what you recommend.
- The target is SMT-LIB 2.7; versions 2.0, 2.5 and 2.6 are supported where a
  script declares them. Where the standard allows several readings, the
  strict one is implemented.
- Comments describe the mechanism and the rule to follow. They do not quote
  measurements or refer to documents outside the repository. Documentation
  comments on public items state behaviour, not implementation.
- Every panic carries a message.
- The tree stays free of compiler and linter warnings.
- Tools and test harnesses are written in Rust or Lean, not in Python.

## Rust (`rust/`)

- The library code under `rust/src` is written by the maintainer. Make only
  mechanical changes to it, only when asked to, and only as far as asked.
- The examples under `rust/examples` are the public view of the library's
  contract and are written by the maintainer too. The same rule applies.
- Tests and benchmarks are written by agents when asked.
- A test that exposes a real defect stays failing. Do not mark it ignored and
  do not weaken it.
- Before handing a change back, run `cargo fmt`, `cargo clippy --all-targets`
  and `cargo test` in `rust/`.

## Lean (`lean/`)

- The Lean code is a port: a translation of the Rust implementation in the
  same checkout. The Rust code and its tests are the specification.
- The architecture is the same as in Rust: a streaming lexer, tokens handed
  over in batches, one parser per syntactic category, handler callbacks, no
  syntax tree. Where Lean forces a different shape, that is a design decision:
  ask.
- Parity of results comes first: the same tokens, the same errors with the
  same spans, the same handler events. Performance follows from the
  architecture and is worked on after parity. The speculative fast paths of
  the Rust code need not be ported at first.
- No `unsafe`. `partial` and panics are tolerated in the initial port and will
  be removed later, so keep them few and easy to find.
- No proofs are required.
- The Lean standard library is the only dependency unless the maintainer
  approves another.
- The toolchain is the Lean release pinned in `lean/lean-toolchain`. Do not
  change it, not even to a newer release, unless the maintainer asks.
  `tools/lean-lex-driver/lean-toolchain` is a copy of it, since elan looks for
  the toolchain file only in a package's directory and the directories above
  it; the two stay identical.
- There is one set of tests, the Rust one. The tests are not translated to
  Lean: a driver runs them against the Lean implementation. Do not write Lean
  copies of Rust tests.

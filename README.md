# blazing-smtlib: Fast, safe, dependency-free SMT-LIB parsing

Under construction.

## Licence

Licensed under either of Apache License, Version 2.0 or MIT licence at your
option. Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in this crate by you, as defined in the Apache-2.0
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

Commits are always done by a human, who reviews any generative-AI code.
Any commit that non-trivially uses generative AI either starts with 
`Let <AI>...` (legacy style) or is signed off like so (new style):

```
Co-authored-by: <AI>
Signed-off-by: <committer>
```

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
- Do not edit the working tree while it holds uncommitted changes of the
  maintainer's. Prepare the change as a patch outside the tracked files and
  say where it is.
- After the maintainer commits work of yours, look at the commit. `README.md`
  requires such a commit to carry `Co-authored-by` and `Signed-off-by`; if
  either is missing, say so at once. The maintainer's own commits need
  neither.
- Design decisions are the maintainer's. When a task needs a decision that has
  not been made, stop and ask in plain prose: what is open, the options with a
  concrete example, and what you recommend.
- If a ruling can be read in more than one way, say how you read it and wait.
  Do not build on your own reading.
- The target is SMT-LIB 2.7; versions 2.0, 2.5 and 2.6 are supported where a
  script declares them. Where the standard allows several readings, the
  strict one is implemented.
- Comments describe the mechanism and the rule to follow. They do not quote
  measurements or refer to documents outside the repository. Documentation
  comments on public items state behaviour, not implementation.
- When a change makes a documentation comment on a public item untrue, do not
  reword it: report it to the maintainer.
- Every public item has the prefix `Smt`; in Lean, the namespace `BSmtLib`
  takes its place. A trait is named by its verb (`SmtConsume`, `SmtParse`).
  An enum that says why something failed or classifies a defect is a `Kind`.
- Every panic carries a message.
- What is matched by text is in American English, for compatibility with
  other APIs: identifiers, the names of files and options, and output that
  programs or tests match (such as `Debug`). Everything else is in British
  English: comments, documentation and other prose, and messages for people,
  such as `Display` implementations, which are not to be matched.
- The tree stays free of compiler and linter warnings.
- Tools and test harnesses are written in Rust or Lean, not in Python.

## Documentation comments

- The first line is a short, simple summary. Detail, examples and "such as"
  go into the paragraphs after it.
- Data is described by a noun phrase (`SmtNumeralBuf`: "Owned numeral (base
  10)."), and what performs an action by its verb (`SmtLexer`: "Lexes SMT-LIB
  input, handing the tokens to a consumer."; `SmtCommandHandler`: "Handles
  commands."). A type that plays a role named by a trait names the role:
  "Handler that checks compliance with SMT-LIB syntax.", "Token consumer that
  adapts a parser to parse the consumed tokens."
- A noun phrase starts without an article ("Kind of the error."); an article
  goes inside it where the phrase reads awkwardly without one ("View of a
  decimal"). A first line that is a full sentence, as for some variants ("The
  handler failed."), keeps its article.
- An owned type and its view are "Owned X" and "View of X" ("View of a
  keyword", "View of whitespace content"). They share the paragraphs after the
  first line, and neither says which one views the other.
- An enum with few variants summarises them in parentheses: "Kind of a
  quantifier (existential or universal)."
- Errors: a type is "Error that forced lexing to stop." or "Error constructing
  a span that would be invalid."; the enum read by `kind()` is "Why lexing
  failed (lexical or consumer error)."; `kind()` is "Kind of the error." and
  `into_kind()` "Converts into the kind of the error."
- A handler callback names its command: "(`declare-sort`)" where it stands for
  the command, "(in `define-funs-rec`)" where it handles a part of it.
- "SMT-LIB" is written only where the context does not make it obvious: for
  commands, scripts, input, text, syntax and the standard.
- A restrictive clause takes "that" and no comma; ", which" opens only a
  non-restrictive one. A clause is preferred to a participle: "Iterator that
  moves …", not "Iterator moving …". "Error constructing …" is not such a
  participle but short for "Error that occurred while constructing …", and
  stays.
- Rules and their discussion come before the paragraph on content, which comes
  last: "The content is stripped of the base declaration, e.g. for the token
  `#b0101`, [as_slice](Self::as_slice) returns `b"0101"`."
- Items are linked without code formatting (`[SmtNumeral]`,
  `[as_slice](Self::as_slice)`, `[u32]`); literal characters, tokens and
  syntax are in code formatting (`` `0` ``, `` `|` ``, `` `#b0101` ``).
- Comment lines are at most 100 columns long.

## Rust (`rust/`)

- The library code under `rust/src` is written by the maintainer, who decides
  the shape of its API. Change it only when asked to, and only as far as asked,
  and only where the semantic shape of the change is clear but implementing it
  by hand is cumbersome. Experiments are done in scratch copies, not in
  `rust/src`.
- The examples under `rust/examples` are the public view of the library's
  contract and are written by the maintainer too. The same rule applies.
- Tests and benchmarks are written by agents when asked.
- A test of the lexer's behaviour is written against `rust/tests/lex_backend`,
  so that the driver runs it against the Lean port too. Only a test of the
  Rust interface itself calls the lexer directly, and says so.
- A test of the parser's, reader's or handler's behaviour is written against
  `rust/tests/parse_backend`, so that the driver runs it against the Lean port
  too. Only a test of the Rust interface itself calls the parser directly, and
  says so.
- For a test of new behaviour, check in a scratch copy that it fails when the
  behaviour is broken.
- A test that exposes a real defect stays failing. Do not mark it ignored and
  do not weaken it.
- A change of the library's behaviour and the tests it breaks go into
  separate commits: first the library, with those tests left failing, then
  the tests. Keep the two apart in what you hand over, and say which tests
  the first one breaks. A rename goes into one commit with its uses.
- Before handing a change back, run `cargo fmt`, `cargo clippy --all-targets`
  and `cargo test` in `rust/`.
- A claim about speed rests on `cargo bench --bench compare`, which runs two
  builds alternately, with both sides built the same way. A difference of a
  few percent that changes sign between files or rounds is drift: report it
  as no measurable change.

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
- A Rust panic that answers a broken contract (a consumer that takes no
  token, a call after a final error) is an obligation on the caller in Lean,
  not a panic.
- The Lean standard library is the only dependency unless the maintainer
  approves another.
- The toolchain is the Lean release pinned in `lean/lean-toolchain`. Do not
  change it, not even to a newer release, unless the maintainer asks.
  `tools/lean-driver/lean-toolchain` is a copy of it, since elan looks for
  the toolchain file only in a package's directory and the directories above
  it; the two stay identical.
- There is one set of tests, the Rust one. The tests are not translated to
  Lean: a driver runs them against the Lean implementation. Do not write Lean
  copies of Rust tests.
- `lean/BSmtLibSpec` (outside its `Facts`) is the trusted specification: a
  formal version of the SMT-LIB standard, independent of this library's
  implementation. It changes only by the maintainer or at the maintainer's
  explicit request. When a proof needs a change of it, stop and propose the
  change with its reason. Never weaken a definition or a property of it to make
  a proof go through. It imports only itself and the Lean standard library.
- The specification's source of truth is the SMT-LIB standard. Its comments
  cite the standard by version, section and production, as the one exception
  to the rule against referring to documents outside the repository. Every
  definition in it that states a rule or a property carries a tag in its comment
  saying how it relates to the standard; `lean/BSmtLibSpec.lean` lists the tags.
- `lean/BSmtLibSpec/Facts` checks the specification: on the standard's
  examples, and that it is unambiguous. It is not trusted and not a part of the
  specification.
- A theorem that proves a property stated in the specification, of the
  specification itself or of an implementation, is stated in the facts module
  of its part (`lean/BSmtLib/Facts/*.lean` for the library,
  `lean/BSmtLibSpec/Facts/*.lean` for the specification), with its proof under
  the `Facts/Proofs` beside it, so that one file per part shows what holds. It
  is followed by `#guard_msgs in #print axioms` with its expected output, which
  names no axiom but `propext`, `Classical.choice` and `Quot.sound`, so that a
  `sorry` or an axiom of its own fails the build. Examples and lemmas need no
  such check.

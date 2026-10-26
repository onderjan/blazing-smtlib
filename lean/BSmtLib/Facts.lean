module

public import BSmtLib.Facts.Lexer
public import BSmtLib.Facts.Parser
public import BSmtLib.Facts.Reader
public import BSmtLib.Facts.PublicApi

@[expose] public section

/-!
# Facts about the library

What the library satisfies, one module for each part:

- with respect to the specification formalism (`BSmtLibSpec`):
  - the lexers (`Facts.Lexer`);
  - the parsers (`Facts.Parser`);
  - the readers (`Facts.Reader`);
- stated without the formalism: the public API (`Facts.PublicApi`).

Each part states its theorems, each followed by the axioms its proof uses, and checks the
adapters that its statements are made with. The proofs are below `Facts.Proofs`.
-/

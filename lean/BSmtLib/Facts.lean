module

public import BSmtLib.Facts.Lexer
public import BSmtLib.Facts.Parser
public import BSmtLib.Facts.Reader
public import BSmtLib.Facts.PublicApi

@[expose] public section

/-!
# Facts about the library

What the library satisfies with respect to the specification, one module for each part: the
lexers (`Facts.Lexer`), the parsers (`Facts.Parser`) and the readers (`Facts.Reader`); and what
its public API satisfies, stated without the specification (`Facts.PublicApi`). Each part states
its theorems, each followed by the axioms its proof uses, and checks the adapters that its
statements are made with. The proofs are below `Facts.Proofs`.
-/

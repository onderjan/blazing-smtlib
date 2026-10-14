import BSmtLib.Facts.Lexer
import BSmtLib.Facts.Parser
import BSmtLib.Facts.Reader
import BSmtLib.Facts.PublicApi

/-!
# Facts of the library

What the library satisfies with respect to the specification, one module for each part: the
lexers (`Facts.Lexer`), the parsers (`Facts.Parser`) and the readers (`Facts.Reader`); and what
its public API satisfies, stated without the specification (`Facts.PublicApi`). Each part states
its theorems, each followed by the axioms its proof uses, and checks the adapters that its
statements are made with. The proofs are below `Facts.Proofs`.
-/

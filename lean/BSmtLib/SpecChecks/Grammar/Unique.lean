import BSmtLib.SpecChecks.Grammar.Unique.Balanced
import BSmtLib.SpecChecks.Grammar.Unique.Parts
import BSmtLib.SpecChecks.Grammar.Unique.Terms
import BSmtLib.SpecChecks.Grammar.Unique.Commands
import BSmtLib.SpecChecks.Grammar.Unique.Script

/-!
# The grammar is unambiguous

Proofs that the syntactic rules leave at most one syntax tree for a sequence of tokens, and
that a script has at most one parse.

- `Balanced` shows that every rule accepts items in a row, an item being a single token or a
  balanced group in parentheses, and that a sequence of tokens splits in at most one way into
  items.
- `Parts` proves uniqueness for the categories below terms: identifiers, sorts,
  s-expressions, attributes, qualified identifiers, sorted variables and patterns.
- `Terms` proves it for terms, by induction on the number of tokens.
- `Commands` proves it for commands, whose names tell them apart.
- `Script` proves that every script has at most one parse: the characters of the first
  command, the version it is parsed in, and its tree are determined, and so is the end of the
  script.

The theorems themselves, `Grammar.termsUnique`, `Grammar.commandsUnique` and
`Grammar.scriptsUnique`, are not here: they are stated in `BSmtLib.SpecChecks` with the axioms
their proofs use, beside the other properties proved of the specification, so that one file
shows what holds.

Not trusted: everything here is proved.
-/

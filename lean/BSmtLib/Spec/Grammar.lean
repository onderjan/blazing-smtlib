import BSmtLib.Spec.Grammar.Tree
import BSmtLib.Spec.Grammar.Syntax
import BSmtLib.Spec.Grammar.File
import BSmtLib.Spec.Grammar.Properties

/-!
# Grammar

The syntax of SMT-LIB scripts as the standard defines it, in three parts:

- `Tree`: the syntax trees, one type per syntactic category, which record everything a script
  writes but the whitespace between its tokens.
- `Syntax`: how each tree is written as tokens (`tokens`), and which trees each version has
  (`Valid`).
- `File`: how the characters of a file are read as commands, in the reading mode each command
  leaves.

It depends on no implementation.

Scripts only: theory declarations, logic declarations and command responses are
not covered.
-/

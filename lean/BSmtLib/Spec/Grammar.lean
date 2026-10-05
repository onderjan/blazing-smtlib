import BSmtLib.Spec.Grammar.Tree
import BSmtLib.Spec.Grammar.Rules
import BSmtLib.Spec.Grammar.Script
import BSmtLib.Spec.Grammar.Claims

/-!
# Grammar

The syntax of SMT-LIB scripts as the standard defines it: the syntax trees, the production
rules over the tokens, and how the characters of a script parse as commands. It depends on no
implementation.

Scope P1: scripts only. Theory declarations, logic declarations and command responses are
not covered.
-/

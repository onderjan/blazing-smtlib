import BSmtLib.Spec.Grammar.Script

/-!
# Properties of the grammar

Properties of the syntactic rules: each states that the rules are unambiguous. They are
properties of the specification alone, and `BSmtLib.SpecChecks` proves them.
Properties of what the parser hands to the handler are stated once the handler interface is
settled.
-/

namespace BSmtLib.Spec.Grammar

open BSmtLib.Spec.Lexicon

/--
Property: the rules leave at most one syntax tree for every sequence of tokens of a term.

This is a property of the specification alone. `BSmtLib.SpecChecks` proves it as
`Grammar.termsUnique`. If it did not hold, one term would stand for two different trees, and a
parser could not tell which one to hand over.
-/
def TermsUnique : Prop :=
  ∀ version tokens term term',
    Grammar.Term version tokens term → Grammar.Term version tokens term' → term = term'

/--
Property: the rules leave at most one syntax tree for every sequence of tokens of a command.

This is a property of the specification alone. `BSmtLib.SpecChecks` proves it as
`Grammar.commandsUnique`. If it did not hold, one command would stand for two different trees.
Two pairs of alternatives are kept apart only by a side condition: `check-sat-assuming` with
a list of terms (2.7) and with a list of propositional literals (2.5 and 2.6) by their
versions, and `set-info` and the declaration of a version by the keyword
`:smt-lib-version`.
-/
def CommandsUnique : Prop :=
  ∀ version tokens command command',
    Grammar.Command version tokens command → Grammar.Command version tokens command' →
      command = command'

/--
Property: every script has at most one parse.

This is a property of the specification alone. `BSmtLib.SpecChecks` proves it as
`Grammar.scriptsUnique`. If it did not hold, one script would stand for two different
sequences of commands. A script can switch the version in which its later commands are read,
so this does not follow from `CommandsUnique` alone: it also rests on a declaration of a
version being read the same way in every version.
-/
def ScriptsUnique : Prop :=
  ∀ version input commands commands',
    ScriptParse version input commands → ScriptParse version input commands' →
      commands = commands'

end BSmtLib.Spec.Grammar

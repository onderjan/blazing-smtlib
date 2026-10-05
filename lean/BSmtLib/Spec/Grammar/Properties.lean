import BSmtLib.Spec.Grammar.Script

/-!
# Properties of the grammar

Properties of the syntactic rules: each states that the rules are unambiguous. They are
properties of the specification alone, and `BSmtLib.SpecChecks` is to prove them.
Properties of what the parser hands to the handler are stated once the handler interface is
settled.
-/

namespace BSmtLib.Spec.Grammar

open BSmtLib.Spec.Lexicon

/--
Property: of the grammar, to be proved.

The rules leave at most one syntax tree for every sequence of tokens of a term.
-/
def TermsUnique : Prop :=
  ∀ version tokens term term',
    Grammar.Term version tokens term → Grammar.Term version tokens term' → term = term'

/--
Property: of the grammar, to be proved.

The rules leave at most one syntax tree for every sequence of tokens of a command.
-/
def CommandsUnique : Prop :=
  ∀ version tokens command command',
    Grammar.Command version tokens command → Grammar.Command version tokens command' →
      command = command'

/--
Property: of the grammar, to be proved.

Every script has at most one parse.
-/
def ScriptsUnique : Prop :=
  ∀ version input commands commands',
    ScriptParse version input commands → ScriptParse version input commands' →
      commands = commands'

end BSmtLib.Spec.Grammar

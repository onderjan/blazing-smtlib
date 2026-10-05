import ParserSpec.Script

/-!
# Claims

What is claimed about the syntactic rules. What the parser hands to the handler is claimed
once the handler interface is settled.
-/

namespace ParserSpec

open LexerSpec

/-- The rules leave at most one syntax tree for every sequence of tokens of a term. -/
def TermsUnique : Prop :=
  ∀ version tokens term term',
    Grammar.Term version tokens term → Grammar.Term version tokens term' → term = term'

/-- The rules leave at most one syntax tree for every sequence of tokens of a command. -/
def CommandsUnique : Prop :=
  ∀ version tokens command command',
    Grammar.Command version tokens command → Grammar.Command version tokens command' →
      command = command'

/-- Every script has at most one reading. -/
def ScriptsUnique : Prop :=
  ∀ version input commands commands',
    ScriptReads version input commands → ScriptReads version input commands' →
      commands = commands'

end ParserSpec

module

public import BSmtLibSpec.Grammar.File
public import BSmtLibSpec.Lexer

@[expose] public section

/-!
# Properties of the grammar

Properties of the specification alone: that each sequence of tokens is at most one tree, that
each file is at most one sequence of commands, and that a lexer fed a command holds none of its
tokens back. `BSmtLib.SpecChecks` proves them.

Together with `tokens`, which writes every tree as exactly one sequence of tokens, the first two
say that the valid trees of a version and the sequences of tokens they are written as
correspond one to one: a tree can be read back from its tokens, and nothing is lost in either
direction.
-/

namespace BSmtLibSpec.Grammar.Properties

open BSmtLibSpec.Lexicon

/--
Property: two terms of a version that are written with the same tokens are the same term.

So a sequence of tokens is a term of the version in at most one way (`Syntax.IsTerm`). If it did not
hold, one term would stand for two different trees, and a parser could not tell which one to
hand over.
-/
def TermsOneToOne : Prop :=
  ∀ version (term term' : Tree.Term), term.Valid version → term'.Valid version →
    term.tokens = term'.tokens → term = term'

/--
Property: two commands of a version that are written with the same tokens are the same command.

So a sequence of tokens is a command of the version in at most one way (`Syntax.IsCommand`). The
version matters: `(check-sat-assuming (p))` is written the same as a command of 2.7 with a list
of terms and as a command of 2.6 with a list of propositional literals, and only one of them is
a command of each version.
-/
def CommandsOneToOne : Prop :=
  ∀ version (command command' : Tree.Command), command.Valid version →
    command'.Valid version → command.tokens = command'.tokens → command = command'

/--
Property: every file has at most one reading.

This does not follow from `CommandsOneToOne` alone: a file can change the version in which the
rest of it is read, so it also rests on the version after each command being determined by the
command.
-/
def FilesUnique : Prop :=
  ∀ version input (commands commands' : List Tree.Command),
    File version input commands → File version input commands' → commands = commands'

/--
Property: a lexer fed the characters of a command, up to its `)`, has handed over all its
tokens and holds nothing back.

So reading can stop at the end of a command and start again, possibly in the version the command
switches to, without a token of the command waiting for what follows it. A command ends with its
`)`, which needs no delimiter.
-/
def CommandsHandedOverWhole : Prop :=
  ∀ version segment tokens command, Tokenization.Exactly version 0 segment tokens →
    Syntax.IsCommand version (tokens.map (SyntaxToken.ofToken version)) command →
      Lexer.HandoverMaximal version segment tokens

end BSmtLibSpec.Grammar.Properties

module

public import BSmtLibSpec.Grammar.File
public import BSmtLibSpec.Lexer

@[expose] public section

/-!
# Properties of the grammar

Properties of the specification alone, which `BSmtLibSpec.Facts.Grammar` proves:

- each sequence of tokens is at most one tree;
- each file is at most one sequence of commands;
- a lexer fed a command holds none of its tokens back.

Together with `tokens`, which writes every tree as exactly one sequence of tokens, the first five
say that, in each version, the valid trees and the sequences of tokens they are written as
correspond one to one: a tree can be read back from its tokens, and nothing is lost in either
direction.
-/

namespace BSmtLibSpec.Grammar.Properties

open BSmtLibSpec.Lexicon

/--
Property: two s-expressions valid in the same version and written with the same tokens are the
same s-expression.

So in each version, a sequence of tokens is an s-expression in at most one way
(`Syntax.IsSExpr`). If it did not hold, one s-expression would stand for two different trees,
and a parser could not tell which one to hand over.
-/
def SExprsOneToOne : Prop :=
  ∀ version (sExpr sExpr' : Tree.SExpr), sExpr.Valid version → sExpr'.Valid version →
    sExpr.tokens = sExpr'.tokens → sExpr = sExpr'

/--
Property: two attributes valid in the same version and written with the same tokens are the
same attribute.

So in each version, a sequence of tokens is an attribute in at most one way
(`Syntax.IsAttribute`). If it did not hold, one attribute would stand for two different trees,
and a parser could not tell which one to hand over.
-/
def AttributesOneToOne : Prop :=
  ∀ version («attribute» attribute' : Tree.Attribute), «attribute».Valid version →
    attribute'.Valid version → «attribute».tokens = attribute'.tokens → «attribute» = attribute'

/--
Property: two sorts valid in the same version and written with the same tokens are the same
sort.

So in each version, a sequence of tokens is a sort in at most one way (`Syntax.IsSort`). If it did
not hold, one sort would stand for two different trees, and a parser could not tell which one to
hand over.
-/
def SortsOneToOne : Prop :=
  ∀ version (sort sort' : Tree.Sort), sort.Valid version → sort'.Valid version →
    sort.tokens = sort'.tokens → sort = sort'

/--
Property: two terms valid in the same version and written with the same tokens are the same
term.

So in each version, a sequence of tokens is a term in at most one way (`Syntax.IsTerm`). If it
did not hold, one term would stand for two different trees, and a parser could not tell which
one to hand over.
-/
def TermsOneToOne : Prop :=
  ∀ version (term term' : Tree.Term), term.Valid version → term'.Valid version →
    term.tokens = term'.tokens → term = term'

/--
Property: two commands valid in the same version and written with the same tokens are the same
command.

So in each version, a sequence of tokens is a command in at most one way (`Syntax.IsCommand`).
The version matters: `(check-sat-assuming (p))` is written the same as a command with a
list of terms, valid in 2.7, and as one with a list of propositional literals, valid in 2.6, and
only one of them is valid in each version.
-/
def CommandsOneToOne : Prop :=
  ∀ version (command command' : Tree.Command), command.Valid version →
    command'.Valid version → command.tokens = command'.tokens → command = command'

/--
Property: every file has at most one reading.

This does not follow from `CommandsOneToOne` alone: a file can change the version in which the
rest of it is read, so it also rests on each command determining the version that the rest is
read in.
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

module

public import BSmtLib.Parser.Category.Term

public section

/-!
# The category parsers

One parser for each syntactic category that terms are built from, each a state machine stepped
by single tokens (see `Parser`). A parser that a construct enters after the construct has taken
the first tokens of it is started in the state after those tokens.
-/

namespace BSmtLib.Parser.Category

open BSmtLib.Traits BSmtLib.Parser.Category.Combinator BSmtLib.Parser.Category.SortedVar

/-- The parser of sorted variables enclosed in `(` and `)` (`SmtParenSortedVarsParser`). -/
abbrev ParenSortedVarsParser (H : Type) {m : Type → Type} [Monad m] [Handler H m] :=
  ParenMultipleParser H (SortedVarParser H)

end BSmtLib.Parser.Category

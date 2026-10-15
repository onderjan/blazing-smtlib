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

/-- The parser before the `(`, with the closed parser that parses after it. -/
/- LEAN: Rust's `SmtParenSortedVarsParser` is a type alias, made with `SmtOpenedParser::new`
through it; this is that function under the alias's name. -/
def ParenSortedVarsParser.new {H : Type} {m : Type → Type} [Monad m] [Handler H m]
    (closed : ClosedMultipleParser H (SortedVarParser H)) : ParenSortedVarsParser H :=
  OpenedParser.new closed

end BSmtLib.Parser.Category

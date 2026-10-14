module

public import BSmtLib.Parser.Category.Term

public section

/-!
# The category parsers

One parser for each syntactic category that terms are built from, each a state machine stepped
by single tokens (see `Parser`). A parser that a construct enters after the construct has taken
the first tokens of it is started in the state after those tokens.
-/

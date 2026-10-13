import BSmtLib.Parser.Syntax
import BSmtLib.Parser.Handler
import BSmtLib.Parser.Framework
import BSmtLib.Parser.Category
import BSmtLib.Parser.Term
import BSmtLib.Parser.Command
import BSmtLib.Parser.Parse
import BSmtLib.Parser.Script
import BSmtLib.Parser.Adapter

/-!
# The parser

One parser for each syntactic category, for commands and for scripts, each a state machine that
takes the tokens one by one and calls a handler as the handler contract states; and the parse
adapter, which runs a parser over the tokens a lexer hands over.
-/

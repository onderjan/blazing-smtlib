import BSmtLib.Facts.Parser.Adapters.Bridge
import BSmtLib.Facts.Parser.Adapters.Handler
import BSmtLib.Facts.Parser.Adapters.Run

/-!
# The adapters of the parser proofs

The definitions that the root theorems of `BSmtLib.Facts.Parser` are stated with, beside the
specification and the library, and nothing else: how the parser's values and tokens stand for the
spec's (`Adapters.Bridge`), the library handlers that stand for spec handlers
(`Adapters.Handler`), and how the parser is run as the spec runs a parser (`Adapters.Run`). The
root theorems of `BSmtLib.Facts.Reader` use some of them too.

A theorem stated with a wrong adapter is a theorem about the wrong thing, so these definitions are
trusted: they are to be read with the specification. `#adapters` in `BSmtLib.Facts.Parser` checks
that the root theorems need no other definition outside the specification, the library and Lean.
-/

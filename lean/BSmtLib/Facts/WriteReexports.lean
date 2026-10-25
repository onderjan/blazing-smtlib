module

public meta import BSmtLib.Facts.Reexports
-- Lean for the run too: a module imported with `meta` alone is not initialized when the
-- executable runs
import Lean
-- the modules the generated module is made from, so that they are built before it is written
import BSmtLib.ControlFlow
import BSmtLib.Lexicon.Bytes
import BSmtLib.Lexicon.Value
import BSmtLib.Lexicon.Value.Versioned
import BSmtLib.Span
import BSmtLib.Version
import BSmtLib.Grammar.Multiple
import BSmtLib.Grammar.Multiple.MatchCases
import BSmtLib.Grammar.Multiple.MatchCasesBuf
import BSmtLib.Grammar.Nodes
import BSmtLib.Handler
import BSmtLib.Handler.CommandHandler
import BSmtLib.Handler.PartialCommandHandler
import BSmtLib.Handler.SyntaxChecker
import BSmtLib.Token.Reserved
import BSmtLib.Token
import BSmtLib.Lexer.Cursor
import BSmtLib.Token.Lookahead
import BSmtLib.Token.Cursor
import BSmtLib.Token.ConsumeFrom
import BSmtLib.Token.TokenBuf
import BSmtLib.Token.TokensBuf
import BSmtLib.Token.TokensCursor
import BSmtLib.Token.AppendTokens
import BSmtLib.Writer
import BSmtLib.Lexer.Error
import BSmtLib.Lexer.Recovery
import BSmtLib.Reader.BufRead
import BSmtLib.Lexer
import BSmtLib.Parser
import BSmtLib.Parser.Category
import BSmtLib.Parser.Command
import BSmtLib.Parser.Script
import BSmtLib.Parser.Adapter
import BSmtLib.Parser.Internal.Fused
import BSmtLib.Reader

/-!
# Writing the re-exports

The executable `reexports`: `lake exe reexports`, run in the package's directory, writes the
generated module `BSmtLib.Reexports` (`BSmtLib/Reexports.lean`) from
`BSmtLib.Facts.Reexports.render` and the modules it imports, without the module itself, so that
a stale module does not stand in the way.
-/

open Lean BSmtLib.Facts.Reexports

/-- Writes the generated module. -/
public meta def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules (sources.toArray.map ({ module := · })) {}
  IO.FS.writeFile path (render (← Parser.builtinTokenTable.get) env)
  IO.println s!"wrote {path}"

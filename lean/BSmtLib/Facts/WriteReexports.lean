module

public meta import BSmtLib.Facts.Reexports
-- Lean for the run too: a module imported with `meta` alone is not initialized when the
-- executable runs
import Lean
-- the modules the generated module is made from, so that they are built before it is written
import BSmtLib.ControlFlow
import BSmtLib.Bytes
import BSmtLib.Plain
import BSmtLib.Span
import BSmtLib.Multiple
import BSmtLib.Multiple.MatchCases
import BSmtLib.Multiple.FunctionSignaturesView
import BSmtLib.Multiple.FunctionSignatures
import BSmtLib.Nodes
import BSmtLib.Traits
import BSmtLib.Traits.CommandHandler
import BSmtLib.Traits.SyntaxChecker
import BSmtLib.Token
import BSmtLib.Token.Reserved
import BSmtLib.Token.SyntaxToken
import BSmtLib.Token.Lookahead
import BSmtLib.Token.Produce
import BSmtLib.Token.ConsumeFrom
import BSmtLib.Lexer.Error
import BSmtLib.Lexer.Recovery
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

module

public import BSmtLib.Reexports
public import BSmtLib.ControlFlow
public import BSmtLib.Bytes
public import BSmtLib.Plain
public import BSmtLib.Span
public import BSmtLib.Multiple
public import BSmtLib.Multiple.MatchCases
public import BSmtLib.Nodes
public import BSmtLib.Traits
public import BSmtLib.Traits.CommandHandler
public import BSmtLib.Traits.SyntaxChecker
public import BSmtLib.Token
public import BSmtLib.Token.Reserved
public import BSmtLib.Token.SyntaxToken
public import BSmtLib.Token.Lookahead
public import BSmtLib.Token.Produce
public import BSmtLib.Token.ConsumeFrom
public import BSmtLib.Lexer.Error
public import BSmtLib.Lexer.Recovery
public import BSmtLib.Lexer
public import BSmtLib.Parser
public import BSmtLib.Parser.Category
public import BSmtLib.Parser.Command
public import BSmtLib.Parser.Script
public import BSmtLib.Parser.Adapter
public import BSmtLib.Parser.Internal.Fused
public import BSmtLib.Reader

public section

/-!
# The library

The root of the library, as `lib.rs` is the crate's: it imports every module of the library. The
items that `lib.rs` re-exports with `pub use` have their names at the root, `BSmtLib.Symbol` for
`BSmtLib.Plain.Symbol` as `blazing_smtlib::SmtSymbol` for `plain::SmtSymbol`. The items of the
modules `Token`, `Lexer`, `Parser` and `Reader`, public modules in Rust, keep their paths, and
the `pub use` lines of those modules give items their names there, `BSmtLib.Lexer.LexError` for
`BSmtLib.Lexer.Error.LexError` as `lexer::SmtLexError` for the `SmtLexError` of `lexer/error.rs`.
-/

/- LEAN: the second names are given by `export` in the generated module `BSmtLib.Reexports`,
for all `pub use` lines at once: `token.rs` and `parser.rs` re-export from submodules that
import `Token` and `Parser` in Lean, so these cannot hold the lines. -/

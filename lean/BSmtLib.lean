import BSmtLib.Reexports
import BSmtLib.ControlFlow
import BSmtLib.Bytes
import BSmtLib.Plain
import BSmtLib.Span
import BSmtLib.Nodes
import BSmtLib.Traits
import BSmtLib.Token
import BSmtLib.Token.Reserved
import BSmtLib.Token.SyntaxToken
import BSmtLib.Token.Produce
import BSmtLib.Token.ConsumeFrom
import BSmtLib.Lexer.CharClass
import BSmtLib.Lexer.Error
import BSmtLib.Lexer.Helpers
import BSmtLib.Lexer.Recovery
import BSmtLib.Lexer
import BSmtLib.Parser
import BSmtLib.Parser.Category
import BSmtLib.Parser.Command
import BSmtLib.Parser.Script
import BSmtLib.Parser.Adapter
import BSmtLib.Reader

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
import `Token` and `Parser` in Lean, so these cannot hold the lines. `lib.rs` re-exports all of
`nodes`; the parser's symbol, `Nodes.Symbol`, has no re-export, as its name at the root would be
that of `Plain.Symbol`. Rust's `SmtSymbol` is the symbol of `plain.rs`, which records whether it
was quoted; the Lean parser pairs the plain view with that flag in `Nodes.Symbol`. `multiple.rs`
has no counterpart. -/

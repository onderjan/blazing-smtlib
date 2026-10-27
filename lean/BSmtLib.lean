module

public import BSmtLib.Reexports
public import BSmtLib.ControlFlow
public import BSmtLib.Lexicon.Bytes
public import BSmtLib.Lexicon.Value
public import BSmtLib.Lexicon.Value.Versioned
public import BSmtLib.Lexicon.Reserved
public import BSmtLib.Span
public import BSmtLib.Version
public import BSmtLib.Grammar.Multiple
public import BSmtLib.Grammar.Multiple.MatchCases
public import BSmtLib.Grammar.Multiple.MatchCasesBuf
public import BSmtLib.Grammar.Nodes
public import BSmtLib.Handler
public import BSmtLib.Handler.CommandHandler
public import BSmtLib.Handler.PartialCommandHandler
public import BSmtLib.Handler.SyntaxChecker
public import BSmtLib.Token
public import BSmtLib.Lexer.Cursor
public import BSmtLib.Token.Lookahead
public import BSmtLib.Token.Cursor
public import BSmtLib.Token.ConsumeFrom
public import BSmtLib.Token.TokenBuf
public import BSmtLib.Token.TokensBuf
public import BSmtLib.Token.TokensCursor
public import BSmtLib.Token.AppendTokens
public import BSmtLib.Writer
public import BSmtLib.Lexer.Error
public import BSmtLib.Lexer.Recovery
public import BSmtLib.Reader.BufRead
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
items that `lib.rs` re-exports with `pub use` have their names at the root,
`BSmtLib.CommandHandler` for `BSmtLib.Handler.CommandHandler` as
`blazing_smtlib::SmtCommandHandler` for `handler::SmtCommandHandler`. The items of the modules
`Lexicon`, `Grammar`, `Span`, `Token`, `Lexer` and `Parser`, public modules in Rust, keep their
paths, and the `pub use` lines of those modules give items their names there,
`BSmtLib.Lexer.LexerError` for `BSmtLib.Lexer.Error.LexerError` as `lexer::SmtLexerError` for the
`SmtLexerError` of `lexer/error.rs`.
-/

/- LEAN: the second names are given by `export` in the generated module `BSmtLib.Reexports`,
for all `pub use` lines at once: `token.rs`, `lexer.rs` and `parser.rs` re-export from
submodules that import `Token`, `Lexer` and `Parser` in Lean, so these cannot hold the lines. -/

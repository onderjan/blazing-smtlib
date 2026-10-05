import BSmtLib.Plain
import BSmtLib.Token
import BSmtLib.Token.Reserved

/- LEAN: in Rust, `SmtSyntaxToken` is in `token` with the token it classifies. It needs
`Reserved`, whose module imports `BSmtLib.Token`, so it has a module of its own here; the root
module `BSmtLib` imports it. The Rust variants `Whitespace` and `Comment` come with the
whitespace and comment tokens. -/

namespace BSmtLib

inductive SyntaxToken where
  | parenOpen
  | parenClose
  | numeral (value : NumeralView)
  | decimal (value : DecimalView)
  | hexadecimal (value : HexDigitsView)
  | binary (value : BinDigitsView)
  | string (value : StringContentView)
  | keyword (value : KeywordView)
  | symbol (value : SymbolView)
  | reserved (value : Reserved)
  | endOfFile
  deriving BEq, Repr

namespace SyntaxToken

/- LEAN: the token is read through the cursor it came from, see `Token`. -/
/-- Construct the token kind from the token and version. -/
@[inline]
def fromToken (cursor : BatchCursor) (token : Token) (version : Version) : SyntaxToken :=
  let content := cursor.content token
  match cursor.category token with
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral => .numeral (NumeralView.newUnchecked content)
  | .decimal => .decimal (DecimalView.newUnchecked content)
  | .hexadecimal => .hexadecimal (HexDigitsView.newUnchecked content)
  | .binary => .binary (BinDigitsView.newUnchecked content)
  | .unquotedSymbol =>
    -- only the words reserved in the version are reserved words
    match Reserved.fromBytes? content version with
    | some word => .reserved word
    | none => .symbol (SymbolView.newUnchecked content)
  | .quotedSymbol => .symbol (SymbolView.newUnchecked content)
  | .string => .string (StringContentView.newUnchecked content)
  | .keyword => .keyword (KeywordView.newUnchecked content)
  | .endOfFile => .endOfFile

end SyntaxToken

namespace BatchCursor

/- LEAN: Rust's `token.syntax(version)`; `syntax` is a keyword in Lean, hence the quotes, which
a call such as `cursor.syntax token version` does not need. -/
@[inline]
def «syntax» (self : BatchCursor) (token : Token) (version : Version) : SyntaxToken :=
  SyntaxToken.fromToken self token version

end BatchCursor

end BSmtLib

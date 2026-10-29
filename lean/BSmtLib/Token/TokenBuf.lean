module

public import BSmtLib.Token

public section

/- LEAN: in Rust, `SmtTokenBuf` is in `token` with the token it is viewed as; here it has
a module of its own next to `Token`'s, which the root module `BSmtLib` imports. -/

open BSmtLib.Lexicon.Value

namespace BSmtLib.Token.TokenBuf

/--
Owned syntax token.

Unlike `TokenCategory`, a syntax token depends on the version: an unquoted symbol that
is a reserved word in the version is `TokenBuf.reserved`, and every other symbol is
a `TokenBuf.symbol`.
-/
inductive _root_.BSmtLib.Token.TokenBuf where
  /-- Opening parenthesis (`(`). -/
  | parenOpen
  /-- Closing parenthesis (`)`). -/
  | parenClose
  /-- Numeral, e.g. `0` or `42`. -/
  | numeral (value : NumeralBuf)
  /-- Decimal, e.g. `0.5` or `3.14`. -/
  | decimal (value : DecimalBuf)
  /-- Hexadecimal, e.g. `#xA04`. -/
  | hexadecimal (value : HexDigitsBuf)
  /-- Binary, e.g. `#b0101`. -/
  | binary (value : BinDigitsBuf)
  /-- String literal, e.g. `"hello"` or `""`. -/
  | string (value : StringContentBuf)
  /-- Keyword, e.g. `:named`. -/
  | keyword (value : KeywordBuf)
  /--
  Symbol (quoted or unquoted), e.g. `x`, `+` or `|a b|`.

  A quoted symbol is a symbol even if its content is a reserved word, such as `|let|`, and
  so is a word reserved only in later versions, such as `lambda` before version 2.7.
  -/
  | symbol (value : SymbolBuf)
  /-- Reserved word, e.g. `let`, `_`, `check-sat`, or `lambda` from version 2.7. -/
  | reserved (value : Lexicon.Reserved)
  /-- Whitespace, e.g. the space in `(assert p)`. -/
  | whitespace (value : WhitespaceBuf)
  /-- Comment, e.g. `; note`. -/
  | comment (value : CommentBuf)
  /--
  End of file (EOF).

  Marks the end of the input.
  -/
  | endOfFile
  deriving Repr

/-- Views as `Token`. -/
def view : TokenBuf → Token
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral value => .numeral value.view
  | .decimal value => .decimal value.view
  | .hexadecimal value => .hexadecimal value.view
  | .binary value => .binary value.view
  | .string value => .string value.view
  | .keyword value => .keyword value.view
  | .symbol value => .symbol value.view
  | .reserved word => .reserved word
  | .whitespace value => .whitespace value.view
  | .comment value => .comment value.view
  | .endOfFile => .endOfFile

end BSmtLib.Token.TokenBuf

namespace BSmtLib.Token

/-- Converts into `TokenBuf`. -/
def intoOwned : Token → TokenBuf
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral value => .numeral value.intoOwned
  | .decimal value => .decimal value.intoOwned
  | .hexadecimal value => .hexadecimal value.intoOwned
  | .binary value => .binary value.intoOwned
  | .string value => .string value.intoOwned
  | .keyword value => .keyword value.intoOwned
  | .symbol value => .symbol value.intoOwned
  | .reserved word => .reserved word
  | .whitespace value => .whitespace value.intoOwned
  | .comment value => .comment value.intoOwned
  | .endOfFile => .endOfFile

end BSmtLib.Token

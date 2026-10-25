module

public import BSmtLib.Token

public section

/- LEAN: in Rust, `SmtTokenBuf` is in `token` with the token it is viewed as; here it has
a module of its own next to `Token`'s, which the root module `BSmtLib` imports. -/

open BSmtLib.Lexicon.Value

namespace BSmtLib.Token.TokenBuf

/-- An owned token, from which `Token` is viewed. -/
inductive _root_.BSmtLib.Token.TokenBuf where
  | parenOpen
  | parenClose
  | numeral (value : NumeralBuf)
  | decimal (value : DecimalBuf)
  | hexadecimal (value : HexDigitsBuf)
  | binary (value : BinDigitsBuf)
  | string (value : StringContentBuf)
  | keyword (value : KeywordBuf)
  | symbol (value : SymbolBuf)
  | reserved (value : Reserved)
  | whitespace (value : WhitespaceBuf)
  | comment (value : CommentBuf)
  | endOfFile
  deriving Repr

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

module

public import BSmtLib.Plain
public import BSmtLib.Token
public import BSmtLib.Token.Reserved

public section

/- LEAN: in Rust, `SmtSyntaxToken` is in `token` with the token it classifies. It needs
`Reserved`, whose module imports `BSmtLib.Token`, so it has a module of its own here; the root
module `BSmtLib` imports it. -/

open BSmtLib.Plain

namespace BSmtLib.Token.SyntaxToken

/- LEAN: Rust's `SmtSyntaxToken::Symbol` carries the symbol's view only. Here a symbol also
says whether it was written quoted (`|abc|`), which the handler contract hands on with the
symbol. -/
inductive _root_.BSmtLib.Token.SyntaxToken where
  | parenOpen
  | parenClose
  | numeral (value : NumeralView)
  | decimal (value : DecimalView)
  | hexadecimal (value : HexDigitsView)
  | binary (value : BinDigitsView)
  | string (value : StringContentView)
  | keyword (value : KeywordView)
  | symbol (value : SymbolView) (quoted : Bool)
  | reserved (value : Reserved)
  | whitespace (value : WhitespaceView)
  | comment (value : CommentView)
  | endOfFile
  deriving BEq, Repr

/- LEAN: Rust's `from_token(token, version)` reads the token's category and content, which a
Lean token keeps in its batch; this takes them read already, so that a cursor and a lookahead
window view their tokens alike. -/
/-- Construct the token kind from the category and the content of a token, and the version. -/
@[inline]
def fromParts (category : TokenCategory) (content : ByteSlice) (version : Version) :
    SyntaxToken :=
  match category with
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
    | none => .symbol (SymbolView.newUnchecked content) false
  | .quotedSymbol => .symbol (SymbolView.newUnchecked content) true
  | .string => .string (StringContentView.newUnchecked content)
  | .keyword => .keyword (KeywordView.newUnchecked content)
  | .whitespace => .whitespace (WhitespaceView.newUnchecked content)
  | .comment => .comment (CommentView.newUnchecked content)
  | .endOfFile => .endOfFile

/- LEAN: the token is read through a cursor over its batch, see `Token`. -/
/-- Construct the token kind from the token and version. -/
@[inline]
def fromToken {batch : BatchTag} (cursor : BatchCursor batch) (token : Token batch)
    (version : Version) : SyntaxToken :=
  fromParts (cursor.category token) (cursor.content token) version

namespace BSmtLib.Token.BatchCursor

/- LEAN: Rust's `cursor.syntax(&token)`; `syntax` is a keyword in Lean, hence the quotes, which
a call such as `cursor.syntax token` does not need. -/
/-- Views the token as a library token under the version in force. -/
@[inline]
def _root_.BSmtLib.Token.BatchCursor.«syntax» {batch : BatchTag} (self : BatchCursor batch)
    (token : Token batch) : SyntaxToken :=
  SyntaxToken.fromToken self token self.version

end BSmtLib.Token.BatchCursor

/-- Views the token as a library token under the version of the window. -/
@[inline]
def _root_.BSmtLib.Token.BatchCursor.TokenWindow.«syntax» {batch : BatchTag}
    (self : BatchCursor.TokenWindow batch)
    (token : Token batch) : SyntaxToken :=
  SyntaxToken.fromParts (self.category token) (self.content token) self.version

end BSmtLib.Token.SyntaxToken

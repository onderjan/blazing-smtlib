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

inductive _root_.BSmtLib.Token.SyntaxToken where
  | parenOpen
  | parenClose
  | numeral (value : Numeral)
  | decimal (value : Decimal)
  | hexadecimal (value : HexDigits)
  | binary (value : BinDigits)
  | string (value : StringContent)
  | keyword (value : Keyword)
  | symbol (value : Symbol)
  | reserved (value : Reserved)
  | whitespace (value : Whitespace)
  | comment (value : Comment)
  | endOfFile
  deriving Repr

/- LEAN: Rust's `from_token(token, version)` reads the token's category and content, which a
Lean token keeps in its batch; this takes them read already, so that a cursor and a lookahead
window view their tokens alike. -/
/-- Construct the token kind from the category and the content of a token, and the version. -/
@[inline]
def Internal.fromParts (category : TokenCategory) (content : ByteSlice)
    (version : Version) : SyntaxToken :=
  match category with
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral => .numeral (Numeral.Internal.newUnchecked content)
  | .decimal => .decimal (Decimal.Internal.newUnchecked content)
  | .hexadecimal => .hexadecimal (HexDigits.Internal.newUnchecked content)
  | .binary => .binary (BinDigits.Internal.newUnchecked content)
  | .unquotedSymbol =>
    -- only the words reserved in the version are reserved words
    match Reserved.fromBytes? content version with
    | some word => .reserved word
    | none => .symbol (Symbol.Internal.newUnchecked false content)
  | .quotedSymbol => .symbol (Symbol.Internal.newUnchecked true content)
  | .string => .string (StringContent.Internal.newUnchecked content)
  | .keyword => .keyword (Keyword.Internal.newUnchecked content)
  | .whitespace => .whitespace (Whitespace.Internal.newUnchecked content)
  | .comment => .comment (Comment.Internal.newUnchecked content)
  | .endOfFile => .endOfFile

/- LEAN: the token is read through a cursor over its batch, see `Token`. -/
/-- Construct the token kind from the token and version. -/
@[inline]
def fromToken {batch : BatchTag} (cursor : BatchCursor batch) (token : Token batch)
    (version : Version) : SyntaxToken :=
  Internal.fromParts (cursor.category token) (cursor.content token) version

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
/- LEAN: Rust's `SmtLookahead::syntax` for `SmtTokenWindow`; `syntax` is a keyword in Lean, as
for the cursor's. -/
@[inline]
def _root_.BSmtLib.Token.BatchCursor.TokenWindow.«syntax» {batch : BatchTag}
    (self : BatchCursor.TokenWindow batch)
    (token : Token batch) : SyntaxToken :=
  SyntaxToken.Internal.fromParts (self.category token) (self.content token) self.version

end BSmtLib.Token.SyntaxToken

namespace BSmtLib.Token

/- LEAN: declared with `SyntaxToken`, as the cause names `Reserved`, whose module imports
`BSmtLib.Token`. -/
/-- Determines why writing a token has failed. -/
inductive WriteErrorCause where
  /-- Writing to the writer failed. -/
  | io (error : IO.Error)
  /-- The reserved word is not reserved in the version, so no text in it is the token. -/
  | notInVersion (reserved : Reserved)

/- LEAN: Rust's derived `Debug`. Lean's `IO.Error` has no `Repr`, so an I/O error is shown by its
message. -/
@[no_expose] instance : Repr WriteErrorCause where
  reprPrec cause prec :=
    let app (name : String) (argument : Std.Format) : Std.Format :=
      Repr.addAppParen (.group (.nest 2 (.text ("BSmtLib.Token.WriteErrorCause." ++ name) ++
        .line ++ argument))) prec
    match cause with
    | .io error => app "io" (reprArg (toString error))
    | .notInVersion reserved => app "notInVersion" (reprArg reserved)

/- LEAN: the constructor is private, as Rust's field is. The field is readable as `error.cause`,
replacing the getters `cause` and `into_cause`. -/
/-- An error that ended writing a token. -/
structure WriteError where
  private mk ::
  /-- Determines why writing has failed. -/
  cause : WriteErrorCause
  deriving Repr

namespace SyntaxToken

/-- The bytes of the slice appended. -/
private def appendSlice (out : ByteArray) (bytes : ByteSlice) : ByteArray :=
  out ++ bytes.toByteArray

/- LEAN: the text that `writeSmt` writes, appended to `out`, or the reserved word that is not in
the version; `writeSmt` writes it in one piece. -/
/-- The token as SMT-LIB text in the version, appended to `out`. -/
def Internal.appendSmt (self : SyntaxToken) (out : ByteArray) (version : Version) :
    Except Reserved ByteArray :=
  match self with
  | .parenOpen => .ok (out.push (byte! '('))
  | .parenClose => .ok (out.push (byte! ')'))
  | .numeral digits => .ok (appendSlice out digits.asSlice)
  | .decimal text => .ok (appendSlice out text.asSlice)
  | .hexadecimal digits =>
    .ok (appendSlice ((out.push (byte! '#')).push (byte! 'x')) digits.asSlice)
  | .binary digits => .ok (appendSlice ((out.push (byte! '#')).push (byte! 'b')) digits.asSlice)
  | .string content =>
    let body := content.asSlice.toByteArray.foldl (init := out.push (byte! '"')) fun out c =>
      if version == .v2_0 then
        -- SMT-LIB 2.0: a double quote and a backslash are escaped by a backslash
        -- for sanity, always escape backslashes, even if not strictly needed
        -- e.g. in \q, the backslash does not technically need to be escaped
        if c == byte! '"' || c == byte! '\\' then (out.push (byte! '\\')).push c else out.push c
      else
        -- SMT-LIB 2.5+: a double quote is escaped by another double quote
        if c == byte! '"' then (out.push c).push c else out.push c
    .ok (body.push (byte! '"'))
  | .keyword name => .ok (appendSlice (out.push (byte! ':')) name.asSlice)
  | .symbol name =>
    -- a simple symbol that is a reserved word in the version
    -- would be read as the reserved word, quote it to keep the symbol
    if name.isQuoted || (Reserved.fromBytes? name.asSlice version).isSome then
      .ok ((appendSlice (out.push (byte! '|')) name.asSlice).push (byte! '|'))
    else
      .ok (appendSlice out name.asSlice)
  | .reserved word =>
    -- the reserved word is not in the version
    -- there is no way to write it
    if word.isInVersion version then .ok (out ++ word.asStr.toUTF8) else .error word
  | .whitespace bytes => .ok (appendSlice out bytes.asSlice)
  | .comment text => .ok (appendSlice (out.push (byte! ';')) text.asSlice)
  | .endOfFile => .ok out

/- LEAN: Rust's `writer` is any `Write`; here an `IO.FS.Stream`, as the reader reads one
(`Reader.BufReader.new`). The token is written in one call of the stream's `write`, where Rust
writes it in pieces. -/
/--
Writes the token as SMT-LIB text in the given version.

No delimiter is written, only the SMT-LIB token as
it should appear in a byte stream.
2.0 string literals have backslashes always written escaped
for sanity even if a single backslash would have been acceptable.

If a simple symbol collides with a reserved word in the given
version, it is written as a quoted symbol, so version upgrades
are possible without problems.

Returns an error if the reserved word is not present
in the given version or if the underlying writer returns one.
-/
def writeSmt {n : Type → Type} [Monad n] [MonadLiftT IO n] (self : SyntaxToken)
    (writer : IO.FS.Stream) (version : Version) : n (Except WriteError Unit) := do
  match Internal.appendSmt self ByteArray.empty version with
  | .error word => return .error ⟨.notInVersion word⟩
  | .ok bytes =>
    let written : IO (Except IO.Error Unit) := (writer.write bytes).toBaseIO
    match ← written with
    | .error err => return .error ⟨.io err⟩
    | .ok () => return .ok ()

end SyntaxToken

end BSmtLib.Token

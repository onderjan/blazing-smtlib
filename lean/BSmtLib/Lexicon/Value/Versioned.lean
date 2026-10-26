module

public import BSmtLib.Lexicon.Value
public import BSmtLib.Token.Reserved

public section

/- LEAN: in Rust, these functions are in `lexicon::value` with the symbol. They need `Version` and
`Reserved`, whose modules import `BSmtLib.Lexicon.Value`, so they have a module of their own
here; the root module `BSmtLib` imports it. -/

namespace BSmtLib.Lexicon.Value

open BSmtLib.Token (Reserved)
open BSmtLib (Version)

/-- Whether the bytes are allowed in a simple symbol and are not a reserved word of the given
version. -/
def SymbolBuf.isSimpleIn (value : ByteSlice) (version : Version) : Bool :=
  isUnquotedAllowed value && (Reserved.fromBytes? value version).isNone

namespace Symbol

/--
Creates a symbol that reads back as itself in the given version.

The symbol is simple if its bytes are allowed in a simple symbol and are not a reserved word of
the version, and quoted otherwise.
-/
def newIn (value : ByteSlice) (version : Version) : Except DisallowedBytesError Symbol :=
  if SymbolBuf.isSimpleIn value version then newUnquoted value else newQuoted value

/-- Whether the symbol reads back as itself in the given version: it is quoted, or it is simple
and the version does not reserve it. -/
def isSymbolIn (self : Symbol) (version : Version) : Bool :=
  self.isQuoted || (Reserved.fromBytes? self.asSlice version).isNone

/-- Quotes the symbol if it is simple and a reserved word of the given version; any other symbol
is returned as it is. -/
def intoVersioned (self : Symbol) (version : Version) : Symbol :=
  Internal.newUnchecked (self.isQuoted || (Reserved.fromBytes? self.asSlice version).isSome)
    self.asSlice

end Symbol

namespace SymbolBuf

/--
Creates a symbol that reads back as itself in the given version.

The symbol is simple if its bytes are allowed in a simple symbol and are not a reserved word of
the version, and quoted otherwise.
-/
def newIn (value : ByteArray) (version : Version) : Except DisallowedByteVecError SymbolBuf :=
  if isSimpleIn value.toByteSlice version then newUnquoted value else newQuoted value

/-- Whether the symbol reads back as itself in the given version: it is quoted, or it is simple
and the version does not reserve it. -/
def isSymbolIn (self : SymbolBuf) (version : Version) : Bool :=
  self.view.isSymbolIn version

/-- Quotes the symbol if it is simple and a reserved word of the given version; any other symbol
is returned as it is. -/
def intoVersioned (self : SymbolBuf) (version : Version) : SymbolBuf :=
  Internal.newUnchecked (self.isQuoted || (Reserved.fromBytes? self.asSlice version).isSome)
    self.intoBytesBuf

end SymbolBuf

end BSmtLib.Lexicon.Value

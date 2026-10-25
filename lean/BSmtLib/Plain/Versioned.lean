module

public import BSmtLib.Plain
public import BSmtLib.Token.Reserved

public section

/- LEAN: in Rust, these functions are in `plain` with the symbol. They need `Version` and
`Reserved`, whose modules import `BSmtLib.Plain`, so they have a module of their own here; the
root module `BSmtLib` imports it. -/

namespace BSmtLib.Plain

open BSmtLib.Token (Version Reserved)

/-- Whether the bytes are allowed in a simple symbol and are not a reserved word of the given
version. -/
def SymbolBuf.isUnquotedAllowedIn (value : ByteSlice) (version : Version) : Bool :=
  isUnquotedAllowed value && (Reserved.fromBytes? value version).isNone

namespace Symbol

/--
Creates a symbol that reads back as itself in the given version.

The symbol is simple if its bytes are allowed in a simple symbol and are not a reserved word of
the version, and quoted otherwise.
-/
def new (value : ByteSlice) (version : Version) : Except DisallowedBytesError Symbol :=
  if SymbolBuf.isUnquotedAllowedIn value version then newUnquoted value else newQuoted value

/-- Whether the symbol reads back as itself in the given version: it is quoted, or it is simple
and not a reserved word of the version. -/
def isAllowedIn (self : Symbol) (version : Version) : Bool :=
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
def new (value : ByteArray) (version : Version) : Except DisallowedByteVecError SymbolBuf :=
  if isUnquotedAllowedIn value.toByteSlice version then newUnquoted value else newQuoted value

/-- Whether the symbol reads back as itself in the given version: it is quoted, or it is simple
and not a reserved word of the version. -/
def isAllowedIn (self : SymbolBuf) (version : Version) : Bool :=
  self.view.isAllowedIn version

/-- Quotes the symbol if it is simple and a reserved word of the given version; any other symbol
is returned as it is. -/
def intoVersioned (self : SymbolBuf) (version : Version) : SymbolBuf :=
  Internal.newUnchecked (self.isQuoted || (Reserved.fromBytes? self.asSlice version).isSome)
    self.intoBytesBuf

end SymbolBuf

end BSmtLib.Plain

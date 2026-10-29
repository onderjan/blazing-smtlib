module

public import BSmtLib.Token

public section

/- LEAN: in Rust, `SmtTokensBuf` is in `token` with the tokens it holds; here it has a module of
its own next to `Token`'s, which the root module `BSmtLib` imports. -/

open BSmtLib.Lexicon.Value

namespace BSmtLib.Token.TokensBuf

/- LEAN: Rust's private `TokenKind`, which the buffer keeps for each token. -/
/-- What a token of `TokensBuf` is, its bytes aside. -/
inductive Internal.Kind where
  | parenOpen
  | parenClose
  | numeral
  | decimal
  | hexadecimal
  | binary
  | string
  | keyword
  | unquotedSymbol
  | quotedSymbol
  | reserved (word : Lexicon.Reserved)
  | whitespace
  | comment
  | endOfFile

/- LEAN: Rust's private `TokenHandle`. -/
/-- A token of `TokensBuf`: its kind and where its bytes are in the text. -/
structure Internal.Handle where
  kind : Internal.Kind
  start : Nat
  «end» : Nat

/- LEAN: Rust's private `TokenHandle::create_by_push`, which returns the text with the bytes
after it. -/
/-- The text with the bytes of the token after it, and the token's handle. -/
@[inline]
def Internal.Handle.createByPush (text : ByteArray) (token : Token) :
    ByteArray × Internal.Handle :=
  let push (kind : Internal.Kind) (bytes : ByteSlice) : ByteArray × Internal.Handle :=
    -- `copySlice` with `exact := false` grows the capacity by doubling, as `Vec` does
    let text' := bytes.byteArray.copySlice bytes.start text text.size bytes.size false
    (text', { kind, start := text.size, «end» := text'.size })
  let empty (kind : Internal.Kind) : ByteArray × Internal.Handle :=
    (text, { kind, start := text.size, «end» := text.size })
  match token with
  | .parenOpen => empty .parenOpen
  | .parenClose => empty .parenClose
  | .numeral value => push .numeral value.asSlice
  | .decimal value => push .decimal value.asSlice
  | .hexadecimal value => push .hexadecimal value.asSlice
  | .binary value => push .binary value.asSlice
  | .string value => push .string value.asSlice
  | .keyword value => push .keyword value.asSlice
  | .symbol value =>
    push (if value.isQuoted then .quotedSymbol else .unquotedSymbol) value.asSlice
  | .reserved word => empty (.reserved word)
  | .whitespace value => push .whitespace value.asSlice
  | .comment value => push .comment value.asSlice
  | .endOfFile => empty .endOfFile

/- LEAN: Rust's private `TokenHandle::view`. -/
/-- Views the token whose bytes are in the text. -/
@[inline]
def Internal.Handle.view (self : Internal.Handle) (text : ByteArray) : Token :=
  -- the bytes were pushed from a view of the same kind, so they are allowed
  let bytes := text.toByteSlice self.start self.end
  match self.kind with
  | .parenOpen => .parenOpen
  | .parenClose => .parenClose
  | .numeral => .numeral (Numeral.Internal.newUnchecked bytes)
  | .decimal => .decimal (Decimal.Internal.newUnchecked bytes)
  | .hexadecimal => .hexadecimal (HexDigits.Internal.newUnchecked bytes)
  | .binary => .binary (BinDigits.Internal.newUnchecked bytes)
  | .string => .string (StringContent.Internal.newUnchecked bytes)
  | .keyword => .keyword (Keyword.Internal.newUnchecked bytes)
  | .unquotedSymbol => .symbol (Symbol.Internal.newUnchecked false bytes)
  | .quotedSymbol => .symbol (Symbol.Internal.newUnchecked true bytes)
  | .reserved word => .reserved word
  | .whitespace => .whitespace (Whitespace.Internal.newUnchecked bytes)
  | .comment => .comment (Comment.Internal.newUnchecked bytes)
  | .endOfFile => .endOfFile

/-- Dynamic array of owned tokens. -/
structure _root_.BSmtLib.Token.TokensBuf where
  private mk ::
  private text : ByteArray
  private handles : Array Internal.Handle

/-- Creates an empty array. -/
def new : TokensBuf := ⟨.empty, #[]⟩

/-- Copies the token after the others. -/
def push (self : TokensBuf) (token : Token) : TokensBuf :=
  let (text, handle) := Internal.Handle.createByPush self.text token
  ⟨text, self.handles.push handle⟩

/-- Removes all tokens. -/
def clear (_ : TokensBuf) : TokensBuf := new

/-- Returns the number of tokens. -/
def len (self : TokensBuf) : Nat := self.handles.size

/-- Returns `true` if there are no tokens. -/
def isEmpty (self : TokensBuf) : Bool := self.handles.isEmpty

/-- Returns the token at the position, or `none` if it is out of bounds. -/
def get? (self : TokensBuf) (index : Nat) : Option Token :=
  self.handles[index]?.map (·.view self.text)

@[no_expose] instance : Inhabited TokensBuf := ⟨new⟩

/- LEAN: Rust's `iter`, as for the containers of `BSmtLib.Grammar.Multiple`. -/
@[no_expose] instance {m : Type → Type} [Monad m] : ForIn m TokensBuf Token where
  forIn self init f := ForIn.forIn (self.handles.map (·.view self.text)) init f

/- LEAN: Rust's `Debug`, which lists the tokens. -/
@[no_expose] instance : Repr TokensBuf :=
  ⟨fun self p => reprPrec (self.handles.map (·.view self.text)) p⟩

end BSmtLib.Token.TokensBuf

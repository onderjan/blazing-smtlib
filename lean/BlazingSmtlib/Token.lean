import Std.Data.ByteSlice
import BlazingSmtlib.ControlFlow
import BlazingSmtlib.Span

/- LEAN: the namespaces follow the Rust modules: `BlazingSmtlib.Token` is `crate::token`.
Variant and function names follow Lean conventions (`TokenType.parenOpen` for
`TokenType::ParenOpen`, `lastConsumed` for `last_consumed`). An `inductive` without
fields is a Rust enum. -/
namespace BlazingSmtlib.Token

open BlazingSmtlib

inductive TokenType where
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
  | endOfFile
  deriving BEq, Repr, Inhabited

/-- Version of the SMT-LIB standard. -/
inductive SmtVersion where
  | v2_0
  | v2_5
  | v2_6
  | v2_7
  deriving BEq, Repr

namespace SmtVersion

/- LEAN: `Inhabited` gives the default value, the Rust `#[default]`. -/
instance : Inhabited SmtVersion := ⟨.v2_7⟩

/- LEAN: Lean cannot derive `PartialOrd`/`Ord` for comparison with `≤` from the order of the
variants, so the order is spelled out as a rank, and `≤` and `<` compare the ranks. -/
/-- The position of the version in the order of releases. -/
private def rank : SmtVersion → Nat
  | .v2_0 => 0
  | .v2_5 => 1
  | .v2_6 => 2
  | .v2_7 => 3

instance : LE SmtVersion := ⟨fun a b => a.rank ≤ b.rank⟩

instance : LT SmtVersion := ⟨fun a b => a.rank < b.rank⟩

/- LEAN: in Lean, `a ≤ b` is a proposition, not a boolean. To use it in an `if`, Lean
needs a `Decidable` instance that computes its truth; these reuse the one of `Nat`. -/
instance (a b : SmtVersion) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.rank ≤ b.rank))

instance (a b : SmtVersion) : Decidable (a < b) := inferInstanceAs (Decidable (a.rank < b.rank))

def fromDecimal? (decimal : ByteSlice) : Option SmtVersion :=
  if decimal == "2.0".toUTF8.toByteSlice then some .v2_0
  else if decimal == "2.5".toUTF8.toByteSlice then some .v2_5
  else if decimal == "2.6".toUTF8.toByteSlice then some .v2_6
  else if decimal == "2.7".toUTF8.toByteSlice then some .v2_7
  else none

end SmtVersion

/- LEAN: the Rust token refers to an entry `Option<(InnerType, &[u8])>` and a span stored in
the lexer's batch arrays, a layout chosen so the lexer writes as little as possible. In
Lean, a token is a plain value: its type, its content as a view of the bytes, and its span.
The end of file has its own type and empty content, so `InnerType` is not needed. -/
structure Token where
  /-- The type of the token. -/
  ty : TokenType
  /-- The bytes of the token; empty for the end of file. -/
  content : ByteSlice
  /-- The span of the token. -/
  span : SmtSpan
  deriving Inhabited

/--
A cursor into a batch of tokens, from which elements are consumed sequentially.

A parser reads a batch through a cursor: it can look at the
tokens ahead, consume them one at a time or several at once, look back at
what it consumed last, and tell how many tokens it has taken. However,
it is not guaranteed how many elements the batch will actually have,
so the lookahead is only useful for fast paths that fall back to
slow paths with the same behaviour if the lookahead is not available.
-/
/- LEAN: Rust narrows the borrowed slices on a relex request; here the cursor owns the
array of the batch and narrows it by moving `stop`, which needs no copy. -/
structure TokenCursor where
  private mk ::
  /-- The SMT-LIB version that applies to the tokens. -/
  version : SmtVersion
  private tokens : Array Token
  /-- The end of the tokens the cursor yields; tokens after it are discarded. -/
  private stop : Nat
  private nextIndex : Nat
  private relexFlag : Bool
  deriving Inhabited

namespace TokenCursor

/-- Returns a cursor at the start of the batch. -/
@[inline]
def new (version : SmtVersion) (tokens : Array Token) : TokenCursor :=
  { version, tokens, stop := tokens.size, nextIndex := 0, relexFlag := false }

/- LEAN: not in Rust. The lexer takes the array back after the handler is done with the
cursor; if nothing else refers to it, its storage is reused for the next batch, as the
Rust lexer reuses its fixed arrays. -/
/-- The tokens of the batch, for reuse of their storage once the cursor is spent. -/
@[inline]
def intoTokens (self : TokenCursor) : Array Token :=
  self.tokens

/-- The token at `index` of the batch, if any. -/
@[inline]
private def at? (self : TokenCursor) (index : Nat) : Option Token :=
  if index < self.stop then self.tokens[index]? else none

/--
Returns a cursor over a single token.

This can be used for parsing one token using a cursor-parsing function.
-/
@[inline]
def single (version : SmtVersion) (token : Token) : TokenCursor :=
  new version #[token]

/-- Returns the next token (if any) without consuming it. -/
@[inline]
def peek (self : TokenCursor) : Option Token :=
  self.at? self.nextIndex

/--
Returns the token `ahead` positions after the next one without consuming anything.

`get 0` is the next token, also available through `peek`.
-/
@[inline]
def get (self : TokenCursor) (ahead : Nat) : Option Token :=
  self.at? (self.nextIndex + ahead)

/- LEAN: methods taking `&mut self` in Rust return the updated cursor in Lean; this one
returns the token too. Within a handler, the cursor is state of the monad, and
`modifyGetThe TokenCursor TokenCursor.next` consumes a token in place. -/
/-- Consumes the next token (if any), returning it with the updated cursor. -/
@[inline]
def next (self : TokenCursor) : Option Token × TokenCursor :=
  match self.at? self.nextIndex with
  | some token => (some token, { self with nextIndex := self.nextIndex + 1 })
  | none => (none, self)

/--
Consumes the next `count` tokens.

Behaves as if `next` was called `count` times with the results discarded,
stopping at the end of the cursor.
-/
@[inline]
def advance (self : TokenCursor) (count : Nat) : TokenCursor :=
  { self with nextIndex := min (self.nextIndex + count) self.stop }

/-- Consumes all tokens remaining in the cursor. -/
@[inline]
def consumeAll (self : TokenCursor) : TokenCursor :=
  { self with nextIndex := self.stop }

/--
Returns the most recently consumed token, if any was consumed through
this cursor.
-/
@[inline]
def lastConsumed (self : TokenCursor) : Option Token :=
  if self.nextIndex == 0 then none else self.at? (self.nextIndex - 1)

/-- How many tokens have been consumed. -/
@[inline]
def consumed (self : TokenCursor) : Nat :=
  self.nextIndex

/-- Whether every token has been consumed. -/
@[inline]
def isEmpty (self : TokenCursor) : Bool :=
  self.nextIndex ≥ self.stop

/--
Requests that the input is lexed again from the end of the last
consumed token.

The tokens not consumed through this cursor are discarded and will be
produced again by the lexer, so the cursor yields no more tokens:
it is empty from now on, and the consumed count stays where it is.
-/
@[inline]
def relex (self : TokenCursor) : TokenCursor :=
  { self with stop := self.nextIndex, relexFlag := true }

/--
Sets the SMT-LIB version that should apply from now on.

This will adjust the non-consumed tokens so they correspond
to the set version. There is no guarantee on their shape
or whether any remain at all; the caller must not use any
information gathered on them beforehand.
-/
def setVersion (self : TokenCursor) (version : SmtVersion) : TokenCursor :=
  let isCurrent2_0 := self.version == .v2_0
  let isNew2_0 := version == .v2_0
  -- we need to relex if the lexical rules change
  let self := if isCurrent2_0 != isNew2_0 then self.relex else self
  { self with version }

/-- Whether `relex` has been called on this cursor. -/
@[inline]
def relexRequested (self : TokenCursor) : Bool :=
  self.relexFlag

end TokenCursor

/- LEAN: Rust's `handle_tokens(&mut self, cursor: &mut TokenCursor) -> Result<ControlFlow<R>, E>`
mutates the handler and the cursor in place and can do any side effect, such as I/O.
Lean functions are pure: to change a value they must return the new one, and side effects
are only possible inside a monad. A monad here does both. `StateT` threads the cursor and
the handler through the code as mutable state (`get`, `set`, `modify`), `ExceptT` gives the
early return of `Err` (`throw`), and the base monad `m`, chosen by the handler, can be `IO`
for a handler with side effects or `Id` for a pure one. A handler can then be written in
`do` notation with `let mut`, loops and early `return`, much as in Rust. The `ExceptT` is
outermost so that the handler and the cursor survive an error, as in Rust. -/
/--
The monad a token handler runs in: the handler `H` and the cursor are its
state, and it can fail with an error of type `E`.
-/
abbrev TokenHandlerM (H : Type) (m : Type → Type) (E : Type) :=
  ExceptT E (StateT TokenCursor (StateT H m))

/- LEAN: a class is Lean's trait. The Rust associated types `Result` and `Error` and the
monad are parameters marked `outParam`: the handler type determines them, as an `impl`
determines associated types. The Rust blanket `impl TokenHandler for &mut T` has no
counterpart, as Lean has no references. -/
/--
A sequential handler of tokens, running in the monad `m`, finishing with a
value of type `R` and failing with an error of type `E`.
-/
class TokenHandler (H : Type) (m : outParam (Type → Type)) (R E : outParam Type) where
  /--
  Handles the tokens handed over in the cursor, in order.

  If the handler returns `ControlFlow.continue`, it means all tokens
  were handled and more are wanted: the cursor must be empty, which it
  also is after a `TokenCursor.relex` request.

  If the handler returns `ControlFlow.break`, it means
  it finished the input it accepts (consuming exactly its tokens),
  is returning a result and waiting for processing of the next value.

  Throwing an error means the handler failed at the token after
  the consumed ones. The state of the handler and cursor is unspecified.
  -/
  handleTokens : TokenHandlerM H m E (ControlFlow R)

end BlazingSmtlib.Token

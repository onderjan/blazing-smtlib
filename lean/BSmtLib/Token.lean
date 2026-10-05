import Std.Data.ByteSlice
import BSmtLib.ControlFlow
import BSmtLib.Span

/- LEAN: the public items of the Rust crate are in the namespace `BSmtLib`, without the prefix
`Smt`: `SmtToken` is `BSmtLib.Token`. The internals of the lexer are in `BSmtLib.Lexer`.
Variant and function names follow Lean conventions (`TokenCategory.parenOpen` for
`SmtTokenCategory::ParenOpen`, `lastConsumed` for `last_consumed`). An `inductive` without
fields is a Rust enum. -/
namespace BSmtLib

inductive TokenCategory where
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
inductive Version where
  | v2_0
  | v2_5
  | v2_6
  | v2_7
  deriving BEq, Repr

namespace Version

/- LEAN: `Inhabited` gives the default value, the Rust `#[default]`. -/
instance : Inhabited Version := ⟨.v2_7⟩

/- LEAN: Lean cannot derive `PartialOrd`/`Ord` for comparison with `≤` from the order of the
variants, so the order is spelled out as a rank, and `≤` and `<` compare the ranks. -/
/-- The position of the version in the order of releases. -/
private def rank : Version → Nat
  | .v2_0 => 0
  | .v2_5 => 1
  | .v2_6 => 2
  | .v2_7 => 3

instance : LE Version := ⟨fun a b => a.rank ≤ b.rank⟩

instance : LT Version := ⟨fun a b => a.rank < b.rank⟩

/- LEAN: in Lean, `a ≤ b` is a proposition, not a boolean. To use it in an `if`, Lean
needs a `Decidable` instance that computes its truth; these reuse the one of `Nat`. -/
instance (a b : Version) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.rank ≤ b.rank))

instance (a b : Version) : Decidable (a < b) := inferInstanceAs (Decidable (a.rank < b.rank))

def fromDecimal? (decimal : ByteSlice) : Option Version :=
  if decimal == "2.0".toUTF8.toByteSlice then some .v2_0
  else if decimal == "2.5".toUTF8.toByteSlice then some .v2_5
  else if decimal == "2.6".toUTF8.toByteSlice then some .v2_6
  else if decimal == "2.7".toUTF8.toByteSlice then some .v2_7
  else none

end Version

namespace TokenCategory

/- LEAN: the batch keeps the types in a byte array, as numbers. -/
/-- The number of the type, in the order of declaration. -/
@[inline]
def toUInt8 : TokenCategory → UInt8
  | .parenOpen => 0
  | .parenClose => 1
  | .numeral => 2
  | .decimal => 3
  | .hexadecimal => 4
  | .binary => 5
  | .string => 6
  | .keyword => 7
  | .unquotedSymbol => 8
  | .quotedSymbol => 9
  | .endOfFile => 10

/-- The type of the number given by `toUInt8`. -/
@[inline]
def ofUInt8 : UInt8 → TokenCategory
  | 0 => .parenOpen
  | 1 => .parenClose
  | 2 => .numeral
  | 3 => .decimal
  | 4 => .hexadecimal
  | 5 => .binary
  | 6 => .string
  | 7 => .keyword
  | 8 => .unquotedSymbol
  | 9 => .quotedSymbol
  | _ => .endOfFile

-- the types are read back from the batch as they were written to it
#guard [TokenCategory.parenOpen, .parenClose, .numeral, .decimal, .hexadecimal, .binary, .string,
    .keyword, .unquotedSymbol, .quotedSymbol, .endOfFile].all fun ty => ofUInt8 ty.toUInt8 == ty

end TokenCategory

/- LEAN: the Rust token is a pair of references to its entry and its span in the lexer's
batch arrays, valid while the batch is. A Lean array holds every structure as a pointer to
a separate object, so a token held as a structure in the batch would be allocated when it
is lexed and freed when it is overwritten. The batch therefore keeps the tokens' fields in
arrays of their own (`TokenBatch`), which the lexer overwrites in place, and a token is its
index in the batch. A structure with a single number field is represented as the number
itself, so a token costs nothing. Its fields are read through the cursor it came from:
`cursor.category token`, `cursor.content token`, `cursor.span token`. -/
/-- A token of a batch, read through the cursor it came from. -/
structure Token where
  private mk ::
  private index : Nat
  deriving BEq, Inhabited

/- LEAN: what the Rust lexer keeps in its batch arrays. Each field is an array with one entry
per token; entries from `len` on are left over from earlier batches and are overwritten. The
contents of all tokens of a batch are in the one array `bytes`: either the input slice the
batch was lexed from, or the lexer's content buffer for a batch of one token. The fields are
public, as the lexer, which is another module, writes them. -/
/-- The tokens of a batch, field by field. -/
structure TokenBatch where
  /-- The number of tokens in the batch. -/
  len : Nat
  /-- The array of the tokens' contents. -/
  bytes : ByteArray
  /-- The types of the tokens, as `TokenCategory.toUInt8`. -/
  types : ByteArray
  contentStarts : Array Nat
  contentStops : Array Nat
  startOffsets : Array Nat
  startLines : Array Nat
  startColumns : Array Nat
  endOffsets : Array Nat
  endLines : Array Nat
  endColumns : Array Nat
  deriving Inhabited

namespace TokenBatch

/-- An empty batch with room for `capacity` tokens. -/
def empty (capacity : Nat) : TokenBatch :=
  { len := 0, bytes := ByteArray.empty, types := ByteArray.emptyWithCapacity capacity,
    contentStarts := Array.emptyWithCapacity capacity,
    contentStops := Array.emptyWithCapacity capacity,
    startOffsets := Array.emptyWithCapacity capacity,
    startLines := Array.emptyWithCapacity capacity,
    startColumns := Array.emptyWithCapacity capacity,
    endOffsets := Array.emptyWithCapacity capacity,
    endLines := Array.emptyWithCapacity capacity,
    endColumns := Array.emptyWithCapacity capacity }

/-- Writes the value at `index` of the array, which is at most its size. -/
@[inline]
private def write (array : Array Nat) (index value : Nat) : Array Nat :=
  if index < array.size then array.set! index value else array.push value

/--
Appends a token with the type, its content from `contentStart` to `contentStop` in `bytes`,
and the span given by the numbers of its two locations.
-/
@[inline]
def push (self : TokenBatch) (ty : TokenCategory) (contentStart contentStop : Nat)
    (startOffset startLine startColumn endOffset endLine endColumn : Nat) : TokenBatch :=
  let index := self.len
  { self with
    len := index + 1
    types := if index < self.types.size then self.types.set! index ty.toUInt8
      else self.types.push ty.toUInt8
    contentStarts := write self.contentStarts index contentStart
    contentStops := write self.contentStops index contentStop
    startOffsets := write self.startOffsets index startOffset
    startLines := write self.startLines index startLine
    startColumns := write self.startColumns index startColumn
    endOffsets := write self.endOffsets index endOffset
    endLines := write self.endLines index endLine
    endColumns := write self.endColumns index endColumn }

/--
Appends a token with the type, its content from `contentStart` to `contentStop` in `bytes`,
spanning the offsets from `start` to `end` on the line that starts at the offset `lineStart`.
-/
@[inline]
def pushOnLine (self : TokenBatch) (ty : TokenCategory) (contentStart contentStop : Nat)
    (line lineStart start «end» : Nat) : TokenBatch :=
  self.push ty contentStart contentStop start line (start - lineStart) «end» line («end» - lineStart)

/--
Appends a token with the type, its content from `contentStart` to `contentStop` in `bytes`,
spanning from `start` to `end`.
-/
@[inline]
def pushLocated (self : TokenBatch) (ty : TokenCategory) (contentStart contentStop : Nat)
    (start «end» : Location) : TokenBatch :=
  self.push ty contentStart contentStop start.offset start.line start.column
    «end».offset «end».line «end».column

/-- Empties the batch, keeping its storage. -/
@[inline]
def clear (self : TokenBatch) : TokenBatch :=
  { self with len := 0 }

end TokenBatch

/--
A cursor into a batch of tokens, from which elements are consumed sequentially.

A parser reads a batch through a cursor: it can look at the
tokens ahead, consume them one at a time or several at once, look back at
what it consumed last, and tell how many tokens it has taken. However,
it is not guaranteed how many elements the batch will actually have,
so the lookahead is only useful for fast paths that fall back to
slow paths with the same behaviour if the lookahead is not available.
-/
/- LEAN: Rust narrows the borrowed slices of the batch; here the cursor holds the whole batch
and the range of it that it yields, from `first` to `stop`. A relex request moves `stop`,
which needs no copy. -/
structure BatchCursor where
  private mk ::
  /-- The SMT-LIB version that applies to the tokens. -/
  version : Version
  private batch : TokenBatch
  /-- The first token the cursor yields. -/
  private first : Nat
  /-- The end of the tokens the cursor yields; tokens after it are discarded. -/
  private stop : Nat
  private nextIndex : Nat
  private relexFlag : Bool
  deriving Inhabited

namespace BatchCursor

/-- Returns a cursor at the start of the batch. -/
@[inline]
def new (version : Version) (batch : TokenBatch) : BatchCursor :=
  { version, batch, first := 0, stop := batch.len, nextIndex := 0, relexFlag := false }

/- LEAN: not in Rust. The lexer takes the batch back after the handler is done with the
cursor; if nothing else refers to it, its storage is overwritten by the next batch, as the
Rust lexer overwrites its fixed arrays. -/
/-- The batch of the cursor, for reuse of its storage once the cursor is spent. -/
@[inline]
def intoBatch (self : BatchCursor) : TokenBatch :=
  self.batch

/-- The token at `index` of the batch, if the cursor yields it. -/
@[inline]
private def at? (self : BatchCursor) (index : Nat) : Option Token :=
  if index < self.stop then some ⟨index⟩ else none

/--
Returns a cursor over a single token of this cursor's batch.

This can be used for parsing one token using a cursor-parsing function.
-/
/- LEAN: Rust's `single` takes the version and the token, which carries its own data. A Lean
token is read through its batch, so the new cursor is made from the cursor the token came
from, over the same batch. -/
@[inline]
def single (self : BatchCursor) (version : Version) (token : Token) : BatchCursor :=
  { version, batch := self.batch, first := token.index, stop := token.index + 1,
    nextIndex := token.index, relexFlag := false }

/-- Returns the next token (if any) without consuming it. -/
@[inline]
def peek (self : BatchCursor) : Option Token :=
  self.at? self.nextIndex

/--
Returns the token `ahead` positions after the next one without consuming anything.

`get 0` is the next token, also available through `peek`.
-/
@[inline]
def get (self : BatchCursor) (ahead : Nat) : Option Token :=
  self.at? (self.nextIndex + ahead)

/- LEAN: methods taking `&mut self` in Rust return the updated cursor in Lean; this one
returns the token too. Within a handler, the cursor is state of the monad, and
`modifyGetThe BatchCursor BatchCursor.next` consumes a token in place. -/
/-- Consumes the next token (if any), returning it with the updated cursor. -/
@[inline]
def next (self : BatchCursor) : Option Token × BatchCursor :=
  if self.nextIndex < self.stop then
    (some ⟨self.nextIndex⟩, { self with nextIndex := self.nextIndex + 1 })
  else
    (none, self)

/--
Consumes the next `count` tokens.

Behaves as if `next` was called `count` times with the results discarded,
stopping at the end of the cursor.
-/
@[inline]
def advance (self : BatchCursor) (count : Nat) : BatchCursor :=
  { self with nextIndex := min (self.nextIndex + count) self.stop }

/-- Consumes all tokens remaining in the cursor. -/
@[inline]
def consumeAll (self : BatchCursor) : BatchCursor :=
  { self with nextIndex := self.stop }

/--
Returns the most recently consumed token, if any was consumed through
this cursor.
-/
@[inline]
def lastConsumed (self : BatchCursor) : Option Token :=
  if self.nextIndex == self.first then none else self.at? (self.nextIndex - 1)

/-- How many tokens have been consumed. -/
@[inline]
def consumed (self : BatchCursor) : Nat :=
  self.nextIndex - self.first

/-- Whether every token has been consumed. -/
@[inline]
def isEmpty (self : BatchCursor) : Bool :=
  self.nextIndex ≥ self.stop

/--
Requests that the input is lexed again from the end of the last
consumed token.

The tokens not consumed through this cursor are discarded and will be
produced again by the lexer, so the cursor yields no more tokens:
it is empty from now on, and the consumed count stays where it is.
-/
@[inline]
def relex (self : BatchCursor) : BatchCursor :=
  { self with stop := self.nextIndex, relexFlag := true }

/--
Sets the SMT-LIB version that should apply from now on.

This will adjust the non-consumed tokens so they correspond
to the set version. There is no guarantee on their shape
or whether any remain at all; the caller must not use any
information gathered on them beforehand.
-/
def setVersion (self : BatchCursor) (version : Version) : BatchCursor :=
  let isCurrent2_0 := self.version == .v2_0
  let isNew2_0 := version == .v2_0
  -- we need to relex if the lexical rules change
  let self := if isCurrent2_0 != isNew2_0 then self.relex else self
  { self with version }

/-- Whether `relex` has been called on this cursor. -/
@[inline]
def relexRequested (self : BatchCursor) : Bool :=
  self.relexFlag

/- LEAN: the counterparts of the methods of the Rust token, which carries its data. A token
must only be given to the cursor it came from or to a copy of it. -/

/-- The category of the token. -/
@[inline]
def category (self : BatchCursor) (token : Token) : TokenCategory :=
  TokenCategory.ofUInt8 (self.batch.types.get! token.index)

/-- The bytes of the token; empty for the end of file. -/
@[inline]
def content (self : BatchCursor) (token : Token) : ByteSlice :=
  self.batch.bytes.toByteSlice (self.batch.contentStarts[token.index]!)
    (self.batch.contentStops[token.index]!)

/-- The span of the token. -/
@[inline]
def span (self : BatchCursor) (token : Token) : Span :=
  let batch := self.batch
  let index := token.index
  Span.ofNumbers batch.startOffsets[index]! batch.startLines[index]! batch.startColumns[index]!
    batch.endOffsets[index]! batch.endLines[index]! batch.endColumns[index]!

end BatchCursor

/- LEAN: Rust's `handle_tokens(&mut self, cursor: &mut BatchCursor) -> Result<ControlFlow<R>, E>`
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
abbrev ConsumeM (H : Type) (m : Type → Type) (E : Type) :=
  ExceptT E (StateT BatchCursor (StateT H m))

/- LEAN: a class is Lean's trait. The Rust associated types `Result` and `Error` and the
monad are parameters marked `outParam`: the handler type determines them, as an `impl`
determines associated types. The Rust blanket `impl Consume for &mut T` has no
counterpart, as Lean has no references. -/
/--
A sequential handler of tokens, running in the monad `m`, finishing with a
value of type `R` and failing with an error of type `E`.
-/
class Consume (H : Type) (m : outParam (Type → Type)) (R E : outParam Type) where
  /--
  Handles the tokens handed over in the cursor, in order.

  If the handler returns `ControlFlow.continue`, it means all tokens
  were handled and more are wanted: the cursor must be empty, which it
  also is after a `BatchCursor.relex` request.

  If the handler returns `ControlFlow.break`, it means
  it finished the input it accepts (consuming exactly its tokens),
  is returning a result and waiting for processing of the next value.

  Throwing an error means the handler failed at the token after
  the consumed ones. The state of the handler and cursor is unspecified.
  -/
  consume : ConsumeM H m E (ControlFlow R)

end BSmtLib

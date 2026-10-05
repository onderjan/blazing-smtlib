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
  | whitespace
  | comment
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
  | .whitespace => 10
  | .comment => 11
  | .endOfFile => 12

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
  | 10 => .whitespace
  | 11 => .comment
  | _ => .endOfFile

-- the types are read back from the batch as they were written to it
#guard [TokenCategory.parenOpen, .parenClose, .numeral, .decimal, .hexadecimal, .binary, .string,
    .keyword, .unquotedSymbol, .quotedSymbol, .whitespace, .comment, .endOfFile].all
  fun ty => ofUInt8 ty.toUInt8 == ty

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

namespace TokenBatch

/- LEAN: the counterparts of the methods of the Rust token, which carries its data, read from
the batch at the token's index. -/

@[inline]
private def categoryOf (self : TokenBatch) (token : Token) : TokenCategory :=
  TokenCategory.ofUInt8 (self.types.get! token.index)

@[inline]
private def contentOf (self : TokenBatch) (token : Token) : ByteSlice :=
  self.bytes.toByteSlice (self.contentStarts[token.index]!) (self.contentStops[token.index]!)

@[inline]
private def spanOf (self : TokenBatch) (token : Token) : Span :=
  let index := token.index
  Span.ofNumbers self.startOffsets[index]! self.startLines[index]! self.startColumns[index]!
    self.endOffsets[index]! self.endLines[index]! self.endColumns[index]!

end TokenBatch

/--
A cursor into a batch of tokens, from which elements are consumed sequentially.

A parser reads a batch through a cursor: it consumes the tokens one at
a time, can look at the next one, and can attempt to take several at once.
However, it is not guaranteed how many tokens the batch will actually have,
so an attempt is only useful for fast paths that fall back to slow paths
with the same behaviour if the tokens are not available.
-/
/- LEAN: Rust narrows the borrowed slices of the batch; here the cursor holds the whole batch
and the range of it that it yields, from `first` to `stop`. A relex request moves `stop`,
which needs no copy. `first` is the first token of the hand-over, Rust's `start`: the tokens
from it to `nextIndex` are the consumed ones. `bounded` keeps the indices in order, which the
proofs about consumption below rest on. -/
structure BatchCursor where
  private mk ::
  /-- The SMT-LIB version that applies to the tokens. -/
  version : Version
  private batch : TokenBatch
  private first : Nat
  private stop : Nat
  private nextIndex : Nat
  private relexFlag : Bool
  private bounded : first ≤ nextIndex ∧ nextIndex ≤ stop

namespace BatchCursor

/- LEAN: crate-private in Rust, like the other functions here that only the lexer uses. Lean
has no visibility between the crate and a file, so they are public. -/
/-- Returns a cursor at the start of the batch. -/
@[inline]
def new (version : Version) (batch : TokenBatch) : BatchCursor :=
  { version, batch, first := 0, stop := batch.len, nextIndex := 0, relexFlag := false,
    bounded := ⟨Nat.le_refl _, Nat.zero_le _⟩ }

/- LEAN: not in Rust. The lexer takes the batch back after the consumer is done with the
cursor; if nothing else refers to it, its storage is overwritten by the next batch, as the
Rust lexer overwrites its fixed arrays. -/
/-- The batch of the cursor, for reuse of its storage once the cursor is spent. -/
@[inline]
def intoBatch (self : BatchCursor) : TokenBatch :=
  self.batch

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
    nextIndex := token.index, relexFlag := false,
    bounded := ⟨Nat.le_refl _, Nat.le_succ _⟩ }

/-- Whether a token remains to be consumed. -/
def HasNext (self : BatchCursor) : Prop :=
  self.nextIndex < self.stop

instance (self : BatchCursor) : Decidable self.HasNext :=
  inferInstanceAs (Decidable (self.nextIndex < self.stop))

/--
Whether `self` comes from `origin` through the consumer's operations: it is the
same hand-over of the same batch, with at least the tokens consumed that `origin`
has consumed. The tokens not consumed yet may have been dropped, as a version
switch drops them.
-/
def Follows (self origin : BatchCursor) : Prop :=
  self.batch = origin.batch ∧ self.first = origin.first ∧ self.stop ≤ origin.stop
    ∧ origin.nextIndex ≤ self.nextIndex

/--
Whether `self` comes from `origin` through the consumer's operations, with at
least one more token consumed than `origin` has.
-/
def Consumed (self origin : BatchCursor) : Prop :=
  self.Follows origin ∧ origin.nextIndex < self.nextIndex

theorem Follows.refl (self : BatchCursor) : self.Follows self :=
  ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem Follows.trans {a b c : BatchCursor} (ab : a.Follows b) (bc : b.Follows c) :
    a.Follows c :=
  ⟨ab.1.trans bc.1, ab.2.1.trans bc.2.1, Nat.le_trans ab.2.2.1 bc.2.2.1,
    Nat.le_trans bc.2.2.2 ab.2.2.2⟩

theorem Consumed.follows {a b : BatchCursor} (ab : a.Consumed b) : a.Follows b :=
  ab.1

theorem Consumed.trans_follows {a b c : BatchCursor} (ab : a.Consumed b) (bc : b.Follows c) :
    a.Consumed c :=
  ⟨ab.1.trans bc, Nat.lt_of_le_of_lt bc.2.2.2 ab.2⟩

theorem Follows.trans_consumed {a b c : BatchCursor} (ab : a.Follows b) (bc : b.Consumed c) :
    a.Consumed c :=
  ⟨ab.trans bc.1, Nat.lt_of_lt_of_le bc.2 ab.2.2.2⟩

theorem Consumed.trans {a b c : BatchCursor} (ab : a.Consumed b) (bc : b.Consumed c) :
    a.Consumed c :=
  ab.trans_follows bc.1

/-- Returns the next token (if any) without consuming it. -/
@[inline]
def peek? (self : BatchCursor) : Option Token :=
  if self.nextIndex < self.stop then some ⟨self.nextIndex⟩ else none

/-- Returns the next token, which there is, without consuming it. -/
@[inline]
def peek (self : BatchCursor) (_ : self.HasNext) : Token :=
  ⟨self.nextIndex⟩

/- LEAN: methods taking `&mut self` in Rust return the updated cursor in Lean, here with the
proof that it consumed the token. -/
/-- Consumes the next token, which there is. -/
@[inline]
def next (self : BatchCursor) (h : self.HasNext) : Token × { c : BatchCursor // c.Consumed self } :=
  (⟨self.nextIndex⟩,
    ⟨{ self with nextIndex := self.nextIndex + 1, bounded := ⟨Nat.le_succ_of_le self.bounded.1, h⟩ },
      ⟨⟨rfl, rfl, Nat.le_refl _, Nat.le_succ _⟩, Nat.lt_succ_self _⟩⟩)

/-- Consumes the next token (if any). -/
@[inline]
def next? (self : BatchCursor) : Option (Token × { c : BatchCursor // c.Consumed self }) :=
  if h : self.HasNext then some (self.next h) else none

/--
The tokens ahead of a cursor, as the extractor of `BatchCursor.attempt` sees them: they can
only be taken in order.
-/
structure TokenWindow where
  private mk ::
  private batch : TokenBatch
  private stop : Nat
  private nextIndex : Nat
  private bounded : nextIndex ≤ stop

/--
Whether `self` comes from `origin` by taking at least one token from it.
-/
def TokenWindow.Consumed (self origin : TokenWindow) : Prop :=
  self.batch = origin.batch ∧ self.stop = origin.stop ∧ origin.nextIndex < self.nextIndex

theorem TokenWindow.Consumed.trans {a b c : TokenWindow} (ab : a.Consumed b)
    (bc : b.Consumed c) : a.Consumed c :=
  ⟨ab.1.trans bc.1, ab.2.1.trans bc.2.1, Nat.lt_trans bc.2.2 ab.2.2⟩

/-- Takes the next token of the window (if any). -/
@[inline]
def TokenWindow.next? (self : TokenWindow) :
    Option (Token × { w : TokenWindow // w.Consumed self }) :=
  if h : self.nextIndex < self.stop then
    some (⟨self.nextIndex⟩,
      ⟨{ self with nextIndex := self.nextIndex + 1, bounded := h },
        ⟨rfl, rfl, Nat.lt_succ_self _⟩⟩)
  else
    none

/-- The category of the token. -/
@[inline]
def TokenWindow.category (self : TokenWindow) (token : Token) : TokenCategory :=
  self.batch.categoryOf token

/-- The bytes of the token; empty for the end of file. -/
@[inline]
def TokenWindow.content (self : TokenWindow) (token : Token) : ByteSlice :=
  self.batch.contentOf token

/-- The span of the token. -/
@[inline]
def TokenWindow.span (self : TokenWindow) (token : Token) : Span :=
  self.batch.spanOf token

/--
Attempts to consume several tokens at once.

The extractor takes tokens from the window ahead of the cursor, in order.
If it returns `some`, exactly the tokens it took are consumed, which must be at least one.
If it returns `none`, nothing is consumed.

The window ends where the cursor does, which may be after any token.
An extractor that runs out of tokens must return `none`; the
caller must then reach the same result by consuming token by token.
-/
/- LEAN: the extractor returns the window it took the tokens from, with the proof that it
took at least one, where the Rust closure takes the window by `&mut`. -/
@[inline]
def attempt (self : BatchCursor)
    (extract : (window : TokenWindow) → Option (α × { w : TokenWindow // w.Consumed window })) :
    Option (α × { c : BatchCursor // c.Consumed self }) :=
  let window : TokenWindow :=
    { batch := self.batch, stop := self.stop, nextIndex := self.nextIndex,
      bounded := self.bounded.2 }
  match extract window with
  | none => none
  | some (result, ⟨taken, consumed⟩) =>
    -- the extractor succeeded, consume what it took
    let bounded : self.first ≤ taken.nextIndex ∧ taken.nextIndex ≤ self.stop :=
      ⟨Nat.le_trans self.bounded.1 (Nat.le_of_lt consumed.2.2),
        Nat.le_trans taken.bounded (Nat.le_of_eq consumed.2.1)⟩
    some (result, ⟨{ self with nextIndex := taken.nextIndex, bounded },
      ⟨⟨rfl, rfl, Nat.le_refl _, Nat.le_of_lt consumed.2.2⟩, consumed.2.2⟩⟩)

/-- Location of the end of the last consumed token in this hand-over (if any). -/
@[inline]
def consumedEnd (self : BatchCursor) : Option Location :=
  if self.first < self.nextIndex then some (self.batch.spanOf ⟨self.nextIndex - 1⟩).end
  else none

/- LEAN: for the lexer, which knows from the consumer's proof that a token was consumed. -/
/-- Location of the end of the last consumed token, given that one was consumed. -/
@[inline]
def consumedEndOf (self : BatchCursor) {origin : BatchCursor} (_ : self.Consumed origin) :
    Location :=
  (self.batch.spanOf ⟨self.nextIndex - 1⟩).end

/-- Consumes all tokens remaining in the cursor. -/
@[inline]
def consumeAll (self : BatchCursor) : BatchCursor :=
  { self with nextIndex := self.stop, bounded := ⟨Nat.le_trans self.bounded.1 self.bounded.2,
    Nat.le_refl _⟩ }

theorem consumeAll_follows (self : BatchCursor) : self.consumeAll.Follows self :=
  ⟨rfl, rfl, Nat.le_refl _, self.bounded.2⟩

theorem consumeAll_consumed {self : BatchCursor} (h : self.HasNext) :
    self.consumeAll.Consumed self :=
  ⟨self.consumeAll_follows, h⟩

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
private def relex (self : BatchCursor) : BatchCursor :=
  { self with
    stop := self.nextIndex
    relexFlag := true
    bounded := ⟨self.bounded.1, Nat.le_refl _⟩ }

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

theorem setVersion_follows (self : BatchCursor) (version : Version) :
    (self.setVersion version).Follows self := by
  unfold setVersion
  by_cases h : ((self.version == .v2_0) != (version == .v2_0)) = true
  · simp only [h, ite_true]
    exact ⟨rfl, rfl, self.bounded.2, Nat.le_refl _⟩
  · simp only [h]
    exact Follows.refl self

/-- Whether a relex has been requested through this cursor. -/
@[inline]
def relexRequested (self : BatchCursor) : Bool :=
  self.relexFlag

/--
The cursor over the tokens not consumed yet, as a new hand-over in which nothing is
consumed.
-/
/- LEAN: Rust's `reset_consumed`. -/
@[inline]
def resetConsumed (self : BatchCursor) : BatchCursor :=
  { self with first := self.nextIndex, bounded := ⟨Nat.le_refl _, self.bounded.2⟩ }

/-- The number of tokens not consumed yet. -/
def remaining (self : BatchCursor) : Nat :=
  self.stop - self.nextIndex

theorem Consumed.remaining_lt {self origin : BatchCursor} (h : self.Consumed origin) :
    self.remaining < origin.remaining := by
  have := self.bounded.2
  have := h.1.2.2.1
  have := h.2
  unfold remaining
  omega

theorem remaining_resetConsumed (self : BatchCursor) :
    self.resetConsumed.remaining = self.remaining :=
  rfl

theorem hasNext_resetConsumed {self : BatchCursor} :
    self.resetConsumed.HasNext ↔ self.HasNext :=
  Iff.rfl

/-- The category of the token. -/
@[inline]
def category (self : BatchCursor) (token : Token) : TokenCategory :=
  self.batch.categoryOf token

/-- The bytes of the token; empty for the end of file. -/
@[inline]
def content (self : BatchCursor) (token : Token) : ByteSlice :=
  self.batch.contentOf token

/-- The span of the token. -/
@[inline]
def span (self : BatchCursor) (token : Token) : Span :=
  self.batch.spanOf token

end BatchCursor

/- LEAN: a class is Lean's trait. The Rust associated types `Result` and `Error` and the
monad are parameters marked `outParam`: the consumer type determines them, as an `impl`
determines associated types. The Rust blanket `impl Consume for &mut T` has no
counterpart, as Lean has no references. -/
/--
A sequential consumer of tokens, running in the monad `m`, finishing with a
value of type `R` and failing with an error of type `E`.
-/
class Consume (H : Type) (m : outParam (Type → Type)) (R E : outParam Type) where
  /- LEAN: the Rust associated constant `CONSUMES_WHITESPACE_AND_COMMENTS`; a field without a
  default, so that every consumer states it. -/
  /--
  Whether the consumer consumes whitespace and comments.

  If false, the consumer operates over abstract tokens:
  it is not interested in whitespace and comments,
  and the caller must not hand them over for consumption.

  If true, the consumer operates over concrete tokens:
  it can reconstruct the byte stream precisely thanks
  to the whitespace and comments. The caller must hand
  over the whitespace and comment tokens present between
  true syntactic tokens.
  -/
  consumesWhitespaceAndComments : Bool
  /- LEAN: Rust's `consume(&mut self, cursor: &mut SmtBatchCursor)`. The consumer's state is
  the state of the monad, and the cursor is handed over with the proof that it has a token
  and given back with the proof that the consumer consumed at least one token of it: the
  two obligations that Rust states in words and checks with a panic. -/
  /--
  Consumes the tokens handed over in the cursor, in order.

  The caller ensures that the cursor contains at least one token.
  The consumer ensures that at least one token is consumed before
  return, no matter the result (even when returning an error).

  If the consumer returns `ControlFlow.continue`, the consumer is
  not finished yet and is ready to consume more tokens. Tokens that
  remain unconsumed in the cursor must be handed over again before
  any new ones.

  If the consumer returns `ControlFlow.break`, it has finished
  consuming the current value, is returning a result, and is ready
  to start consuming a new value.

  If the consumer returns an error, it has failed at the last
  consumed token. The state of the consumer is unspecified.
  -/
  consume : (cursor : BatchCursor) → cursor.HasNext →
    StateT H m (Except E (ControlFlow R) × { c : BatchCursor // c.Consumed cursor })

end BSmtLib

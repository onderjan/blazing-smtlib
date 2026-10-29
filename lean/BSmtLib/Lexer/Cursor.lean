module

public import BSmtLib.Token

public section

/- LEAN: Rust's module `lexer::cursor`, whose items `lexer.rs` re-exports: the token of the lexer,
the cursor over a batch of them and the window ahead of the cursor. The cursor implements
`Cursor` and the window `Lookahead`, whose instances are with the classes in
`BSmtLib.Token.Cursor` and `BSmtLib.Token.Lookahead`: the class `Cursor` names the lexer's cursor
in an internal hook, so this module comes before it. -/

namespace BSmtLib.Lexer.Cursor

open BSmtLib.Token

/- LEAN: the Rust token is a pair of references to its entry and its span in the lexer's
batch arrays, valid while the batch is. A Lean array holds every structure as a pointer to
a separate object, so a token held as a structure in the batch would be allocated when it
is lexed and freed when it is overwritten. The batch therefore keeps the tokens' fields in
arrays of their own (`Internal.TokenBatch`), which the lexer overwrites in place, and a token
is its index in the batch. A structure with a single number field is represented as the number
itself, so a token costs nothing; its batch tag is a type index and not stored. Its fields
are read through a cursor over its batch: `cursor.category token`, `cursor.content token`,
`cursor.span token`. -/
/--
Lexer token.

Lexer tokens are given out by `LexerCursor`. Each token includes its location span and can be
viewed as `Token` via `LexerCursor.syntax`.

A token is read through a cursor over its batch: the cursor it was taken from, or any cursor
that the consumer's operations make from that one in the same hand-over. A token cannot be
read through the cursor of another hand-over, which is over another batch.
-/
structure LexerToken (batch : BatchTag) where
  private mk ::
  private index : Nat
  /- LEAN: not in Rust. The token is within its batch, so that it is read without a bounds
  check; the proof is not stored, and the token stays a number. -/
  private valid : ∀ b, batch b → index < b.len

@[no_expose] instance {batch : BatchTag} : BEq (LexerToken batch) := ⟨fun a b => a.index == b.index⟩


end BSmtLib.Lexer.Cursor

namespace BSmtLib.Token.Internal.TokenBatch

/- LEAN: the counterparts of the methods of the Rust token, which carries its data, read from
the batch at the token's index, which is within the batch. -/

@[inline]
private def categoryOf (self : TokenBatch) (index : Nat) (h : index < self.len) : TokenCategory :=
  TokenCategory.Internal.ofUInt8 (self.types[index]'(Nat.lt_of_lt_of_le h self.ordered.1))

@[inline]
private def contentOf (self : TokenBatch) (index : Nat) (h : index < self.len) : ByteSlice :=
  self.bytes.toByteSlice (self.contentStarts[index]'(Nat.lt_of_lt_of_le h self.fit.1))
    (self.contentStops[index]'(Nat.lt_of_lt_of_le h self.fit.2.1))

@[inline]
private def spanOf (self : TokenBatch) (index : Nat) (h : index < self.len) : Span :=
  Span.Internal.ofNumbers (self.startOffsets[index]'(Nat.lt_of_lt_of_le h self.ordered.2.1))
    (self.startLines[index]'(Nat.lt_of_lt_of_le h self.fit.2.2.1))
    (self.startColumns[index]'(Nat.lt_of_lt_of_le h self.fit.2.2.2.1))
    (self.endOffsets[index]'(Nat.lt_of_lt_of_le h self.ordered.2.2.1))
    (self.endLines[index]'(Nat.lt_of_lt_of_le h self.fit.2.2.2.2.1))
    (self.endColumns[index]'(Nat.lt_of_lt_of_le h self.fit.2.2.2.2.2))

/-- The category of the token at the index, as the entries of the batch give it. -/
private theorem categoryOf_eq (self : TokenBatch) (index : Nat) (h : index < self.len) :
    self.categoryOf index h = TokenCategory.Internal.ofUInt8 (self.types.get! index) := by
  simp only [categoryOf, get!_eq_getElem _ (Nat.lt_of_lt_of_le h self.ordered.1)]

/-- The content of the token at the index, as the entries of the batch give it. -/
private theorem contentOf_eq (self : TokenBatch) (index : Nat) (h : index < self.len) :
    self.contentOf index h =
      self.bytes.toByteSlice (self.contentStarts[index]!) (self.contentStops[index]!) := by
  have := Nat.lt_of_lt_of_le h self.fit.1
  have := Nat.lt_of_lt_of_le h self.fit.2.1
  simp only [contentOf, getElem!_pos, *]

/-- The span of the token at the index, as the entries of the batch give it. -/
private theorem spanOf_eq (self : TokenBatch) (index : Nat) (h : index < self.len) :
    self.spanOf index h =
      Span.Internal.ofNumbers self.startOffsets[index]! self.startLines[index]!
          self.startColumns[index]!
        self.endOffsets[index]! self.endLines[index]! self.endColumns[index]! := by
  have := Nat.lt_of_lt_of_le h self.ordered.2.1
  have := Nat.lt_of_lt_of_le h self.fit.2.2.1
  have := Nat.lt_of_lt_of_le h self.fit.2.2.2.1
  have := Nat.lt_of_lt_of_le h self.ordered.2.2.1
  have := Nat.lt_of_lt_of_le h self.fit.2.2.2.2.1
  have := Nat.lt_of_lt_of_le h self.fit.2.2.2.2.2
  simp only [spanOf, getElem!_pos, *]


end BSmtLib.Token.Internal.TokenBatch

namespace BSmtLib.Lexer.Cursor

open BSmtLib.Token

/- LEAN: Rust narrows the borrowed slices of the batch; here the cursor holds the whole batch
and the range of it that it yields, from `first` to `stop`. A relex request moves `stop`,
which needs no copy. `first` is the first token of the hand-over, Rust's `start`: the tokens
from it to `nextIndex` are the consumed ones. `bounded` keeps the indices in order and within
the batch, which the reads and the proofs about consumption below rest on.

The batch is tagged by the type's parameter, which is not stored, and held in
the field `batch`, which the reads use; `tagged` ties the two. -/
/--
Cursor into a batch of lexer tokens.

A consumer reads a batch through a cursor: it consumes the tokens one at
a time, can look at the next one, and can attempt to take several at once.
However, it is not guaranteed how many tokens the batch will actually have,
so an attempt is only useful for fast paths that fall back to slow paths
with the same behaviour if the tokens are not available.

A cursor is over the batch of one hand-over, which its type names. The cursors
that the consumer's operations make from it are over the same batch and read
every token taken from any of them. The cursor of another hand-over is over
another batch.
-/
structure LexerCursor (tag : BatchTag) where
  private mk ::
  /--
  Returns the SMT-LIB version that applies to the tokens currently consumed.

  The version is guaranteed not to change during a call to the consumer except as a result of
  the consumer calling `setVersion` and the producer accepting.
  -/
  version : Version
  private batch : Internal.TokenBatch
  private tagged : tag = batch.tag
  private first : Nat
  private stop : Nat
  private nextIndex : Nat
  private relexFlag : Bool
  private discardFlag : Bool
  private bounded : first ≤ nextIndex ∧ nextIndex ≤ stop ∧ stop ≤ batch.len

/- LEAN: not in Rust, where the lexer reads the cursor's crate-private fields. The cursor's
fields are private to this module; the lexer reads the batch through this accessor. -/
/-- The batch of the cursor. -/
@[inline]
def LexerCursor.Internal.batch {batch : BatchTag} (cursor : LexerCursor batch) :
    Internal.TokenBatch :=
  cursor.batch

/-- The batch of the cursor has the cursor's tag. -/
theorem LexerCursor.Internal.tag_batch {batch : BatchTag} (cursor : LexerCursor batch) :
    (LexerCursor.Internal.batch cursor).tag = batch :=
  cursor.tagged.symm

namespace LexerCursor

variable {batch : BatchTag}

/-- The cursor's batch has the cursor's tag. -/
private theorem tagged_batch (self : LexerCursor batch) : batch self.batch :=
  (congrFun self.tagged self.batch).mpr rfl

/-- A batch with the cursor's tag is the cursor's batch. -/
private theorem eq_batch_of_tag (self : LexerCursor batch) {b : Internal.TokenBatch} (h : batch b) :
    b = self.batch :=
  (congrFun self.tagged b).mp h

/-- A token below the end of the cursor is within every batch with the cursor's tag. -/
private theorem valid_of_lt_stop (self : LexerCursor batch) {index : Nat}
    (h : index < self.stop) : ∀ b, batch b → index < b.len := fun _ hb => by
  rw [self.eq_batch_of_tag hb]
  exact Nat.lt_of_lt_of_le h self.bounded.2.2

/-- A token of the cursor's tag is within the cursor's batch. -/
private theorem lt_len (self : LexerCursor batch) (token : LexerToken batch) :
    token.index < self.batch.len :=
  token.valid _ self.tagged_batch

/- LEAN: crate-private in Rust, like the other functions here in `Internal`, which only the lexer
uses. -/
/-- Returns a cursor at the start of the batch. -/
@[inline]
def Internal.new (version : Version) (batch : Internal.TokenBatch) : LexerCursor batch.tag :=
  { version, batch, tagged := rfl, first := 0, stop := batch.len, nextIndex := 0,
    relexFlag := false, discardFlag := false,
    bounded := ⟨Nat.le_refl _, Nat.zero_le _, Nat.le_refl _⟩ }

/- LEAN: Rust's `single` takes the version and the token, which carries its own data. A Lean
token is read through its batch, so the new cursor is made from a cursor over the token's
batch. -/
/--
Returns a cursor over a single token of this cursor's batch.

This can be used for parsing one token using a cursor-parsing function.
-/
@[inline]
def Internal.single (self : LexerCursor batch) (version : Version) (token : LexerToken batch) :
    LexerCursor batch :=
  { version, batch := self.batch, tagged := self.tagged, first := token.index,
    stop := token.index + 1, nextIndex := token.index, relexFlag := false, discardFlag := false,
    bounded := ⟨Nat.le_refl _, Nat.le_succ _, self.lt_len token⟩ }

/- LEAN: not in Rust. That a token remains is the producer's law `Cursor.HasNext` for the
cursor, which the consumers take as a proof; Rust's `is_empty` is its negation. -/
/-- Whether a token remains to be consumed. -/
def HasNext (self : LexerCursor batch) : Prop :=
  self.nextIndex < self.stop

@[no_expose] instance (self : LexerCursor batch) : Decidable self.HasNext :=
  inferInstanceAs (Decidable (self.nextIndex < self.stop))

/-- A cursor at the start of a batch with a token has a token remaining. -/
theorem hasNext_new {b : Internal.TokenBatch} (version : Version) (h : 0 < b.len) :
    (Internal.new version b).HasNext :=
  h

/--
Whether `self` comes from `origin` through the consumer's operations: it is the
same hand-over of the same batch, with at least the tokens consumed that `origin`
has consumed. The tokens not consumed yet may have been dropped, as a version
switch drops them.
-/
def Internal.Follows (self origin : LexerCursor batch) : Prop :=
  self.first = origin.first ∧ self.stop ≤ origin.stop ∧ origin.nextIndex ≤ self.nextIndex

/- LEAN: not in Rust. That a cursor took a token is the producer's law `Cursor.Consumed` for
the cursor, by which the loops of the consumers end. -/
/--
Whether `self` comes from `origin` through the consumer's operations, with at
least one more token consumed than `origin` has.
-/
def Consumed (self origin : LexerCursor batch) : Prop :=
  (Internal.Follows self) origin ∧ origin.nextIndex < self.nextIndex

theorem Internal.Follows.refl (self : LexerCursor batch) : (Internal.Follows self) self :=
  ⟨rfl, Nat.le_refl _, Nat.le_refl _⟩

theorem Internal.Follows.trans {a b c : LexerCursor batch} (ab : (Internal.Follows a) b)
    (bc : (Internal.Follows b) c) :
    (Internal.Follows a) c :=
  ⟨ab.1.trans bc.1, Nat.le_trans ab.2.1 bc.2.1, Nat.le_trans bc.2.2 ab.2.2⟩

theorem Consumed.follows {a b : LexerCursor batch} (ab : a.Consumed b) : (Internal.Follows a) b :=
  ab.1

theorem Consumed.trans_follows {a b c : LexerCursor batch} (ab : a.Consumed b)
    (bc : (Internal.Follows b) c) : a.Consumed c :=
  ⟨ab.1.trans bc, Nat.lt_of_le_of_lt bc.2.2 ab.2⟩

theorem Internal.Follows.trans_consumed {a b c : LexerCursor batch} (ab : (Internal.Follows a) b)
    (bc : b.Consumed c) : a.Consumed c :=
  ⟨ab.trans bc.1, Nat.lt_of_lt_of_le bc.2 ab.2.2⟩

theorem Consumed.trans {a b c : LexerCursor batch} (ab : a.Consumed b) (bc : b.Consumed c) :
    a.Consumed c :=
  ab.trans_follows bc.1

/--
Returns the next token (if any) without consuming it.

Peeking must return `some` containing the next token that would be consumed if there is some
such token waiting.

The caller must not forget to consume the token later if it should be taken.
-/
@[inline]
def peek? (self : LexerCursor batch) : Option (LexerToken batch) :=
  if h : self.nextIndex < self.stop then some ⟨self.nextIndex, self.valid_of_lt_stop h⟩ else none

/-- Returns the next token, which there is, without consuming it. -/
@[inline]
def peek (self : LexerCursor batch) (h : self.HasNext) : LexerToken batch :=
  ⟨self.nextIndex, self.valid_of_lt_stop h⟩

/- LEAN: methods taking `&mut self` in Rust return the updated cursor in Lean, here with the
proof that it consumed the token. -/
/-- Consumes the next token, which there is. -/
@[inline]
def next (self : LexerCursor batch) (h : self.HasNext) :
    LexerToken batch × { c : LexerCursor batch // c.Consumed self } :=
  (⟨self.nextIndex, self.valid_of_lt_stop h⟩,
    ⟨{ self with
        nextIndex := self.nextIndex + 1
        bounded := ⟨Nat.le_succ_of_le self.bounded.1, h, self.bounded.2.2⟩ },
      ⟨⟨rfl, Nat.le_refl _, Nat.le_succ _⟩, Nat.lt_succ_self _⟩⟩)

/-- Consumes the next token (if any). -/
@[inline]
def next? (self : LexerCursor batch) :
    Option (LexerToken batch × { c : LexerCursor batch // c.Consumed self }) :=
  if h : self.HasNext then some (self.next h) else none

/-- A cursor with a token remaining gives it. -/
theorem isSome_next? {self : LexerCursor batch} (h : self.HasNext) : self.next?.isSome := by
  simp [next?, h]

end LexerCursor

section

variable {batch : BatchTag}

/--
Lookahead window for an attempt to extract tokens from a lexer cursor.

This window is given by `LexerCursor` to the extraction function passed
to `LexerCursor.attempt` so it can attempt extraction of multiple tokens.
-/
structure LexerWindow (tag : BatchTag) where
  private mk ::
  /-- The SMT-LIB version that applies to the tokens. -/
  version : Version
  private batch : Internal.TokenBatch
  private tagged : tag = batch.tag
  private stop : Nat
  private nextIndex : Nat
  private bounded : nextIndex ≤ stop ∧ stop ≤ batch.len

/-- A token of the window's tag is within the window's batch. -/
private theorem LexerWindow.lt_len (self : LexerWindow batch) (token : LexerToken batch) :
    token.index < self.batch.len :=
  token.valid _ ((congrFun self.tagged self.batch).mpr rfl)

/- LEAN: not in Rust. That a window took a token, as `Consumed` is for the cursor. -/
/--
Whether `self` comes from `origin` by taking at least one token from it.
-/
def LexerWindow.Consumed (self origin : LexerWindow batch) : Prop :=
  self.stop = origin.stop ∧ origin.nextIndex < self.nextIndex

theorem LexerWindow.Consumed.trans {a b c : LexerWindow batch} (ab : a.Consumed b)
    (bc : b.Consumed c) : a.Consumed c :=
  ⟨ab.1.trans bc.1, Nat.lt_trans bc.2 ab.2⟩

/- LEAN: Rust's `SmtLookahead::next` for `SmtLexerWindow`, with the proof that it took a token. -/
/-- Looks at the next token and advances the window. -/
@[inline]
def LexerWindow.next? (self : LexerWindow batch) :
    Option (LexerToken batch × { w : LexerWindow batch // w.Consumed self }) :=
  if h : self.nextIndex < self.stop then
    some (⟨self.nextIndex, fun _ hb => by
        rw [(congrFun self.tagged _).mp hb]; exact Nat.lt_of_lt_of_le h self.bounded.2⟩,
      ⟨{ self with nextIndex := self.nextIndex + 1, bounded := ⟨h, self.bounded.2⟩ },
        ⟨rfl, Nat.lt_succ_self _⟩⟩)
  else
    none

/- LEAN: Rust's `SmtLexerToken::category`, read through the window, as the token is an index into
its batch (see `LexerToken`). -/
/-- Returns the category of the token. -/
@[inline]
def LexerWindow.category (self : LexerWindow batch) (token : LexerToken batch) : TokenCategory :=
  self.batch.categoryOf token.index (self.lt_len token)

/- LEAN: Rust's `SmtLexerToken::content`, read through the window, as the token is an index into
its batch (see `LexerToken`). -/
/--
Returns the content of the token, as the lexicon type of its category holds it.

The content is for use during the hand-over; to keep it, copy it.

For example, the content is the bytes of `a b` for `|a b|` and of `named` for `:named`, and
empty for the end of the input.
-/
@[inline]
def LexerWindow.content (self : LexerWindow batch) (token : LexerToken batch) : ByteSlice :=
  self.batch.contentOf token.index (self.lt_len token)

/- LEAN: Rust's `SmtLexerToken::span`, read through the window, as the token is an index into its
batch (see `LexerToken`). -/
/-- Returns the span of the token. -/
@[inline]
def LexerWindow.span (self : LexerWindow batch) (token : LexerToken batch) : Span :=
  self.batch.spanOf token.index (self.lt_len token)

end

namespace LexerCursor

variable {batch : BatchTag}

/- LEAN: the extractor returns the window it took the tokens from, with the proof that it
took at least one, where the Rust closure takes the window by `&mut`. -/
/--
Attempts to consume several tokens at once (lookahead).

The extractor takes tokens from the window ahead of the cursor, in order.
If it returns `some`, exactly the tokens it took are consumed, which must be at least one.
If it returns `none`, nothing is consumed.
An extractor that runs out of tokens must return `none`.
The window may end after any token.

This function can be provided for ultra-fast processing,
and the caller must ensure that a successful attempt results in
the same observable behaviour as when it failed one.
Use standard `next?` processing unless
absolutely necessary and supported by measurements.
-/
@[inline]
def attempt (self : LexerCursor batch)
    (extract : (window : LexerWindow batch) →
      Option (α × { w : LexerWindow batch // w.Consumed window })) :
    Option (α × { c : LexerCursor batch // c.Consumed self }) :=
  let window : LexerWindow batch :=
    { version := self.version, batch := self.batch, tagged := self.tagged, stop := self.stop,
      nextIndex := self.nextIndex,
      bounded := self.bounded.2 }
  match extract window with
  | none => none
  | some (result, ⟨taken, consumed⟩) =>
    -- the extractor succeeded, consume what it took
    let bounded : self.first ≤ taken.nextIndex ∧ taken.nextIndex ≤ self.stop ∧
        self.stop ≤ self.batch.len :=
      ⟨Nat.le_trans self.bounded.1 (Nat.le_of_lt consumed.2),
        Nat.le_trans taken.bounded.1 (Nat.le_of_eq consumed.1), self.bounded.2.2⟩
    some (result, ⟨{ self with nextIndex := taken.nextIndex, bounded },
      ⟨⟨rfl, Nat.le_refl _, Nat.le_of_lt consumed.2⟩, consumed.2⟩⟩)

/-- Location of the end of the last consumed token in this hand-over (if any). -/
@[inline]
def Internal.consumedEnd (self : LexerCursor batch) : Option Span.Location :=
  if h : self.first < self.nextIndex then
    some (self.batch.spanOf (self.nextIndex - 1) (by have := self.bounded; omega)).end
  else none

/- LEAN: for the lexer, which knows from the consumer's proof that a token was consumed. -/
/-- Location of the end of the last consumed token, given that one was consumed. -/
@[inline]
def Internal.consumedEndOf (self : LexerCursor batch) {origin : LexerCursor batch}
    (h : self.Consumed origin) : Span.Location :=
  (self.batch.spanOf (self.nextIndex - 1) (by have := self.bounded; have := h.2; omega)).end

/- LEAN: Rust's `consumed_span`, for a consumer's caller that knows from the consumer's proof
that a token was consumed. -/
/-- Span of the last consumed token in this handover, given that one was consumed. -/
@[inline]
def Internal.consumedSpanOf (self : LexerCursor batch) {origin : LexerCursor batch}
    (h : self.Consumed origin) : Span :=
  self.batch.spanOf (self.nextIndex - 1) (by have := self.bounded; have := h.2; omega)

/--
Whether the cursor yields no token beyond its batch, and every token of its batch ends after
the offset.
-/
def Internal.EndsAfter (self : LexerCursor batch) (offset : Nat) : Prop :=
  self.stop ≤ self.batch.len ∧ self.batch.EndsAfter offset

theorem endsAfter_new {batch : Internal.TokenBatch} {offset : Nat} (h : batch.EndsAfter offset)
    (version : Version) : Internal.EndsAfter (Internal.new version batch) offset :=
  ⟨Nat.le_refl _, h⟩

/-- Two cursors with the same tag are over the same batch. -/
private theorem batch_eq_of_tag (self other : LexerCursor batch) : self.batch = other.batch :=
  Internal.TokenBatch.tag_injective (self.tagged.symm.trans other.tagged)

theorem Internal.Follows.endsAfter {self origin : LexerCursor batch} (h : (Internal.Follows self)
    origin)
    {offset : Nat} (ho : (Internal.EndsAfter origin) offset) :
    (Internal.EndsAfter self) offset := by
  rw [EndsAfter, batch_eq_of_tag self origin]
  exact ⟨Nat.le_trans h.2.1 ho.1, ho.2⟩

/-- The last token consumed ends after the offset that every token of the batch ends after. -/
theorem Consumed.lt_consumedEndOf {self origin : LexerCursor batch} (h : self.Consumed origin)
    {offset : Nat} (ho : (Internal.EndsAfter origin) offset) : offset
        < ((Internal.consumedEndOf self) h).offset := by
  have hs := h.follows.endsAfter ho
  have hlt : self.nextIndex - 1 < self.batch.len := by
    have := h.2
    have := self.bounded.2
    have := hs.1
    omega
  have h2 := Internal.TokenBatch.endsAfter_iff.mp hs.2 _ hlt
  rw [getElem!_pos self.batch.endOffsets _ (Nat.lt_of_lt_of_le hlt self.batch.ordered.2.2.1)] at h2
  simpa only [Internal.consumedEndOf, Internal.TokenBatch.spanOf, Span.end_ofNumbers,
    Span.Location.Internal.offset_new] using h2

/-- Consumes all tokens the producer has left to hand over. -/
@[inline]
def consumeAll (self : LexerCursor batch) : LexerCursor batch :=
  { self with nextIndex := self.stop, bounded := ⟨Nat.le_trans self.bounded.1 self.bounded.2.1,
    Nat.le_refl _, self.bounded.2.2⟩ }

theorem consumeAll_follows (self : LexerCursor batch) : (Internal.Follows self.consumeAll) self :=
  ⟨rfl, Nat.le_refl _, self.bounded.2.1⟩

theorem consumeAll_consumed {self : LexerCursor batch} (h : self.HasNext) :
    self.consumeAll.Consumed self :=
  ⟨self.consumeAll_follows, h⟩

/--
Returns `true` if the producer has no tokens left to consume.

This must be true exactly if `peek?` or `next?` would produce `none`.
-/
@[inline]
def isEmpty (self : LexerCursor batch) : Bool :=
  self.nextIndex ≥ self.stop

theorem isEmpty_iff (self : LexerCursor batch) : self.isEmpty = true ↔ ¬ self.HasNext := by
  simp [isEmpty, HasNext]

theorem not_hasNext_consumeAll (self : LexerCursor batch) : ¬ self.consumeAll.HasNext := by
  simp [consumeAll, HasNext]

/--
Requests that the input is lexed again from the end of the last
consumed token.

The tokens not consumed through this cursor are discarded and will be
produced again by the lexer, so the cursor yields no more tokens:
it is empty from now on, and the consumed count stays where it is.
-/
@[inline]
private def relex (self : LexerCursor batch) : LexerCursor batch :=
  { self with
    stop := self.nextIndex
    relexFlag := true
    bounded := ⟨self.bounded.1, Nat.le_refl _, Nat.le_trans self.bounded.2.1 self.bounded.2.2⟩ }

/--
Sets the version that applies from now on.

If the producer returns `.ok`, it has switched to the new version, and will return it in
subsequent calls of `version`. The version change applies between the last consumed and first
unconsumed token, and the producer can adjust the non-consumed tokens so they correspond to
the set version. There is no guarantee on their shape or whether any remain at all; the caller
must not use any information gathered on them beforehand.

If the producer returns `.error`, it has refused the version set request. It guarantees that
no changes were made, as if the method was never called.
-/
def setVersion (self : LexerCursor batch) (version : Version) :
    Except VersionRefused (LexerCursor batch) :=
  -- the lexer supports all versions,
  -- but needs to relex when switching between 2.0 and 2.5+
  let isCurrent2_0 := self.version == .v2_0
  let isNew2_0 := version == .v2_0
  -- we need to relex if the lexical rules change
  let self := if isCurrent2_0 != isNew2_0 then self.relex else self
  .ok { self with version }

theorem setVersion_follows {self : LexerCursor batch} {version : Version}
    {next : LexerCursor batch} (h : self.setVersion version = .ok next) :
    (Internal.Follows next) self := by
  unfold setVersion at h
  injection h with h
  subst h
  by_cases hv : ((self.version == .v2_0) != (version == .v2_0)) = true
  · simp only [hv, ite_true]
    exact ⟨rfl, self.bounded.2.1, Nat.le_refl _⟩
  · simp only [hv]
    exact Internal.Follows.refl self

/-- Whether a relex has been requested through this cursor. -/
@[inline]
def Internal.relexRequested (self : LexerCursor batch) : Bool :=
  self.relexFlag

/--
Forces the producer to discard all tokens before an EOF token.

It follows that the first produced token, if any, must be EOF.
-/
@[inline]
def discardRest (self : LexerCursor batch) : LexerCursor batch :=
  { self with
    stop := self.nextIndex
    discardFlag := true
    bounded := ⟨self.bounded.1, Nat.le_refl _, Nat.le_trans self.bounded.2.1 self.bounded.2.2⟩ }

theorem discardRest_follows (self : LexerCursor batch) : (Internal.Follows self.discardRest) self :=
  ⟨rfl, self.bounded.2.1, Nat.le_refl _⟩

/-- Whether discarding the rest has been requested through this cursor. -/
@[inline]
def Internal.discardRequested (self : LexerCursor batch) : Bool :=
  self.discardFlag

/- LEAN: Rust's `reset_consumed`. -/
/--
The cursor over the tokens not consumed yet, as a new hand-over in which nothing is
consumed.
-/
@[inline]
def Internal.resetConsumed (self : LexerCursor batch) : LexerCursor batch :=
  { self with first := self.nextIndex, bounded := ⟨Nat.le_refl _, self.bounded.2⟩ }

/-- Folds over the categories of the first `count` tokens of the batch, which has them. -/
private def foldCategories (b : Internal.TokenBatch) (count : Nat) (h : count ≤ b.len) (init : β)
    (f : β → TokenCategory → β) : β :=
  count.fold (init := init) fun index hindex acc =>
    f acc (b.categoryOf index (Nat.lt_of_lt_of_le hindex h))

private theorem foldCategories_eq (b : Internal.TokenBatch) (count : Nat) (h : count ≤ b.len)
    (init : β)
    (f : β → TokenCategory → β) :
    foldCategories b count h init f =
      (List.range count).foldl
        (fun acc index => f acc (TokenCategory.Internal.ofUInt8 (b.types.get! index))) init := by
  induction count with
  | zero => simp [foldCategories]
  | succ n ih =>
    unfold foldCategories at ih ⊢
    rw [Nat.fold_succ, List.range_succ, List.foldl_append, ← ih (by omega),
      Internal.TokenBatch.categoryOf_eq]
    rfl

/- LEAN: for the lexer, Rust's `consumed_entries`. -/
/-- Folds over the categories of the tokens of the batch consumed so far, from its first one. -/
def Internal.foldConsumedCategories (self : LexerCursor batch) (init : β) (f : β → TokenCategory →
    β) :
    β :=
  foldCategories self.batch self.nextIndex (by have := self.bounded; omega) init f

/-- The fold over the consumed categories, as the entries of the batch give them. -/
private theorem foldConsumedCategories_eq (self : LexerCursor batch) (init : β)
    (f : β → TokenCategory → β) :
    (Internal.foldConsumedCategories self) init f =
      (List.range self.nextIndex).foldl
        (fun acc index => f acc
            (TokenCategory.Internal.ofUInt8 (self.batch.types.get! index))) init :=
  foldCategories_eq ..

/-- The number of tokens not consumed yet. -/
def Internal.remaining (self : LexerCursor batch) : Nat :=
  self.stop - self.nextIndex

theorem Consumed.remaining_lt {self origin : LexerCursor batch} (h : self.Consumed origin) :
    (Internal.remaining self) < (Internal.remaining origin) := by
  have := self.bounded.2
  have := h.1.2.1
  have := h.2
  unfold Internal.remaining
  omega

theorem remaining_resetConsumed (self : LexerCursor batch) :
    (Internal.remaining (Internal.resetConsumed self)) = (Internal.remaining self) :=
  (rfl)

theorem endsAfter_resetConsumed {self : LexerCursor batch} {offset : Nat}
    (h : (Internal.EndsAfter self) offset) :
        (Internal.EndsAfter (Internal.resetConsumed self)) offset :=
  h

theorem hasNext_resetConsumed {self : LexerCursor batch} :
    (Internal.resetConsumed self).HasNext ↔ self.HasNext :=
  Iff.rfl

/- LEAN: Rust's `SmtLexerToken::category`, read through the cursor, as the token is an index into
its batch (see `LexerToken`). -/
/-- Returns the category of the token. -/
@[inline]
def category (self : LexerCursor batch) (token : LexerToken batch) : TokenCategory :=
  self.batch.categoryOf token.index (self.lt_len token)

/- LEAN: Rust's `SmtLexerToken::content`, read through the cursor, as the token is an index into
its batch (see `LexerToken`). -/
/--
Returns the content of the token, as the lexicon type of its category holds it.

The content is for use during the hand-over; to keep it, copy it.

For example, the content is the bytes of `a b` for `|a b|` and of `named` for `:named`, and
empty for the end of the input.
-/
@[inline]
def content (self : LexerCursor batch) (token : LexerToken batch) : ByteSlice :=
  self.batch.contentOf token.index (self.lt_len token)

/- LEAN: Rust's `SmtLexerToken::span`, read through the cursor, as the token is an index into its
batch (see `LexerToken`). -/
/-- Returns the span of the token. -/
@[inline]
def span (self : LexerCursor batch) (token : LexerToken batch) : Span :=
  self.batch.spanOf token.index (self.lt_len token)

/- LEAN: not in Rust: for the proofs, which read the cursor only through this module. -/
/-- Two cursors of a batch alike but for where their handover started: everything a consumer or
the lexer reads of a cursor is the same of both. -/
def Internal.Alike (x y : LexerCursor batch) : Prop :=
  x.version = y.version ∧ x.stop = y.stop ∧ x.nextIndex = y.nextIndex ∧
    x.relexFlag = y.relexFlag ∧ x.discardFlag = y.discardFlag

namespace Internal.Alike

theorem refl (x : LexerCursor batch) : Alike x x := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem symm {x y : LexerCursor batch} (h : Alike x y) : Alike y x :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩

theorem trans {x y z : LexerCursor batch} (h : Alike x y) (h' : Alike y z) : Alike x z :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.1.trans h'.2.2.2.1,
    h.2.2.2.2.trans h'.2.2.2.2⟩

theorem resetConsumed (x : LexerCursor batch) : Alike (Internal.resetConsumed x) x := refl x

theorem version {x y : LexerCursor batch} (h : Alike x y) : x.version = y.version := h.1

theorem hasNext_iff {x y : LexerCursor batch} (h : Alike x y) : x.HasNext ↔ y.HasNext := by
  unfold HasNext; rw [h.2.1, h.2.2.1]

theorem next {x y : LexerCursor batch} (h : Alike x y) (hx : x.HasNext) (hy : y.HasNext) :
    (x.next hx).1 = (y.next hy).1 ∧ Alike (x.next hx).2.val (y.next hy).2.val := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, h1, h2, by simp [LexerCursor.next, h3], h4, h5⟩
  simp only [LexerCursor.next, h3]

theorem setVersion {x y : LexerCursor batch} (h : Alike x y) (v : Version)
    {x' y' : LexerCursor batch} (hx : x.setVersion v = .ok x') (hy : y.setVersion v = .ok y') :
    Alike x' y' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold LexerCursor.setVersion at hx hy
  injection hx with hx
  injection hy with hy
  subst hx hy
  rw [h1]
  split <;> simp_all [Alike, LexerCursor.relex]

theorem discardRest {x y : LexerCursor batch} (h : Alike x y) :
    Alike x.discardRest y.discardRest :=
  ⟨h.1, h.2.2.1, h.2.2.1, h.2.2.2.1, rfl⟩

theorem category {x y : LexerCursor batch} (_ : Alike x y) (t : LexerToken batch) :
    x.category t = y.category t := by
  simp only [LexerCursor.category, batch_eq_of_tag x y]

theorem content {x y : LexerCursor batch} (_ : Alike x y) (t : LexerToken batch) :
    x.content t = y.content t := by
  simp only [LexerCursor.content, batch_eq_of_tag x y]

theorem consumedEndOf {x y o o' : LexerCursor batch} (h : Alike x y) (hx : x.Consumed o)
    (hy : y.Consumed o') : (Internal.consumedEndOf x) hx = (Internal.consumedEndOf y) hy := by
  simp only [Internal.consumedEndOf, batch_eq_of_tag x y, h.2.2.1]

theorem consumedSpanOf {x y o o' : LexerCursor batch} (h : Alike x y) (hx : x.Consumed o)
    (hy : y.Consumed o') : (Internal.consumedSpanOf x) hx = (Internal.consumedSpanOf y) hy := by
  simp only [Internal.consumedSpanOf, batch_eq_of_tag x y, h.2.2.1]

theorem span_peek {x y : LexerCursor batch} (h : Alike x y) (hx : x.HasNext)
    (hy : y.HasNext) : x.span (x.peek hx) = y.span (y.peek hy) := by
  simp only [LexerCursor.span, LexerCursor.peek, batch_eq_of_tag x y, h.2.2.1]

theorem relexRequested {x y : LexerCursor batch} (h : Alike x y) :
    (Internal.relexRequested x) = (Internal.relexRequested y) := h.2.2.2.1

theorem discardRequested {x y : LexerCursor batch} (h : Alike x y) :
    (Internal.discardRequested x) = (Internal.discardRequested y) := h.2.2.2.2

theorem resetConsumed_eq {x y : LexerCursor batch} (h : Alike x y) :
    (Internal.resetConsumed x) = (Internal.resetConsumed y) := by
  have hb := batch_eq_of_tag x y
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  cases x; cases y
  simp only at h1 h2 h3 h4 h5 hb
  subst h1 h2 h3 h4 h5 hb
  rfl

theorem foldConsumedCategories {x y : LexerCursor batch} (h : Alike x y) {β : Type} (init : β)
    (f : β → TokenCategory → β) :
    (Internal.foldConsumedCategories x) init f = (Internal.foldConsumedCategories y) init f := by
  simp only [Internal.foldConsumedCategories, batch_eq_of_tag x y, h.2.2.1]

theorem batch_eq {x y : LexerCursor batch} (_ : Alike x y) :
    LexerCursor.Internal.batch x = LexerCursor.Internal.batch y :=
  batch_eq_of_tag x y

/-- A cursor with a request made has no token left, if it had none left when the request was made:
the requests drop the tokens left. -/
theorem flags_hasNext {x : LexerCursor batch} (h : (Internal.relexRequested x) = false)
    (h' : (Internal.discardRequested x) = false) (v : Version) {x' : LexerCursor batch}
    (hx : x.setVersion v = .ok x') (hn : x'.HasNext) :
    (Internal.relexRequested x') = false ∧ (Internal.discardRequested x') = false := by
  unfold LexerCursor.setVersion at hx
  injection hx with hx
  subst hx
  split at hn
  · simp [HasNext, LexerCursor.relex] at hn
  · rename_i hc
    simp only [hc]
    exact ⟨h, h'⟩

end Internal.Alike

theorem discardRest_hasNext (x : LexerCursor batch) : ¬ x.discardRest.HasNext := by
  simp [HasNext, discardRest]

theorem relexRequested_next {x : LexerCursor batch} (hx : x.HasNext) :
    (Internal.relexRequested (x.next hx).2.val) = (Internal.relexRequested x) ∧
      (Internal.discardRequested (x.next hx).2.val) = (Internal.discardRequested x) :=
  ⟨rfl, rfl⟩

end LexerCursor

/- LEAN: not in Rust. The parts of a token's content, read without the content's slice, which is
made by a call that the compiler does not inline: for a reader of the bytes that needs no slice.
They are declared here, where the cursor's fields are visible. -/
namespace Internal

variable {batch : BatchTag}

/-- The bytes that the token's content is a slice of. -/
@[inline]
def contentBytes (cursor : LexerCursor batch) (_ : LexerToken batch) : ByteArray :=
  cursor.batch.bytes

/-- Where the token's content starts in `contentBytes`. -/
@[inline]
def contentStart (cursor : LexerCursor batch) (token : LexerToken batch) : Nat :=
  cursor.batch.contentStarts[token.index]'(Nat.lt_of_lt_of_le (cursor.lt_len token)
    cursor.batch.fit.1)

/-- Where the token's content stops in `contentBytes`. -/
@[inline]
def contentStop (cursor : LexerCursor batch) (token : LexerToken batch) : Nat :=
  cursor.batch.contentStops[token.index]'(Nat.lt_of_lt_of_le (cursor.lt_len token)
    cursor.batch.fit.2.1)

/-- The content is the slice of its bytes between its start and its stop. -/
theorem content_eq_parts (cursor : LexerCursor batch) (token : LexerToken batch) :
    cursor.content token =
      (contentBytes cursor token).toByteSlice (contentStart cursor token)
        (contentStop cursor token) :=
  (rfl)

end Internal

/- LEAN: Rust's `SmtToken::from_lexer_token(token, version)` reads the token's category and
content, which a Lean token keeps in its batch, so this reads them through a cursor over the
batch. It is declared here, as the cursor's module imports `BSmtLib.Token`. -/
/-- Views a lexer token, read through the cursor, as a syntax token in the version. -/
@[inline]
def _root_.BSmtLib.Token.fromLexerToken {batch : BatchTag} (cursor : LexerCursor batch)
    (token : LexerToken batch) (version : Version) : Token :=
  Token.Internal.fromParts (cursor.category token) (cursor.content token) version

namespace LexerCursor

/- LEAN: Rust's `cursor.syntax(&token)`; `syntax` is a keyword in Lean, hence the quotes, which
a call such as `cursor.syntax token` does not need. -/
/-- Views a token of this cursor as a syntax token in the version in force. -/
@[inline]
def «syntax» {batch : BatchTag} (self : LexerCursor batch) (token : LexerToken batch) : Token :=
  Token.fromLexerToken self token self.version

end LexerCursor

/- LEAN: Rust's `SmtLookahead::syntax` for `SmtLexerWindow`; `syntax` is a keyword in Lean, as
for the cursor's. -/
/-- Views the user token as a syntax token. -/
@[inline]
def LexerWindow.«syntax» {batch : BatchTag} (self : LexerWindow batch) (token : LexerToken batch) :
    Token :=
  Token.Internal.fromParts (self.category token) (self.content token) self.version

end BSmtLib.Lexer.Cursor

import BSmtLib.Lexer
import BSmtLib.Proofs.Lexer.Slice

/-!
The lexer with the content buffer: a lexer of the chain that leads from the specification to the
library's lexer, after the lexer with the batch kept in the lexer's state `X1BatchInCore`.

It is the lexer with the batch kept in the lexer's state with one change: the contents. The
content of the token in progress is kept in a buffer with a length (`ContentBuffer`), whose
storage is reused from token to token, where `X1BatchInCore` keeps a byte array of its own and
starts a new one with every token; and the content of a token lexed from the slice is the slice's
array and the positions in it (`Content.borrowed`, the arguments of `pushFast` and
`pushBorrowed`), where `X1BatchInCore` takes a view of the slice.

Everything else is the lexer with the batch kept in the lexer's state's: the batch, the indices
into the slice, the fast paths, the steps per state, the loop over a slice, the end of the input
and the recovery. The library's lexer `BSmtLib.Lexer` is this lexer with `USize` positions in the
whole array of the slice.
-/

namespace BSmtLib.Proofs.Lexer.X2Contents

open BSmtLib.Lexer (BATCH_CAPACITY Stop Interrupted Failure LexerState RecoveryState ContentBuffer
  Content DigitRun HEXADECIMAL_RUN BINARY_RUN Start startOf fastFlags isDelimiter endsRun
  FAST_ON FAST_PIPE FAST_EMIT FAST_RUN_MASK RUN_NON_LF_WHITESPACE RUN_SIMPLE_SYMBOL
  RUN_COMMENT_PLAIN RUN_DIGIT RUN_STRING_PLAIN RUN_QUOTED_PLAIN not_endsRun_of_fastFlags
  eq_of_startOf_eq_lineFeed)
open Slice

/- LEAN: the fields of the Rust `Lexer` except the handler, which the lexer's monad keeps
separately (see `LexM`). The lexer states are documented at `LexerState` in Rust. The
batch lives here instead of in a local of `lex_slice_inner`, so that its storage is reused
from one slice to the next; it is empty whenever lexing returns. -/
structure LexerCore where
  /-- The SMT-LIB version the lexer currently operates under. -/
  version : Version
  /-- The initial SMT-LIB version the lexer will reset to. -/
  initialVersion : Version
  /-- Current lexer state. -/
  state : LexerState
  /-- Whether the lexer should discard bytes until EOF is reached. -/
  discard : Bool
  /- LEAN: Rust chooses by its type parameter `R`; the constructors set this to match the
  `recovery` of the lexer. -/
  /-- Whether the lexer recovers from errors. -/
  recovers : Bool
  /--
  The number of parentheses left open by the tokens the consumer has consumed.

  Only tracked by a recovering lexer to aid recovery.
  -/
  consumedDepth : Nat
  /--
  The number of parentheses lexed.

  Only tracked by a recovering lexer to aid recovery.
  Used to speed up depth tracking in the common case
  of consumer consuming the whole batch.
  -/
  lexedDepth : Nat
  /-- The current state of lexer recovery (if any). -/
  recoveryState : Option RecoveryState
  /-- Location of the start of the currently-processed token. -/
  tokenStart : Location
  /-- The currently-built string content of the currently-processed token. -/
  tokenContent : ContentBuffer
  /--
  Offset of the start of the byte being processed during lexing.

  It only advances after byte consumption.
  -/
  offset : Nat
  /- LEAN: not in Rust, where indices are relative to the rest of the slice, whose first
  byte is at `offset`. Here indices are in the slice, and `base` is the index of the byte at
  `offset`; it is zero when no slice is being lexed. -/
  /-- The index in the slice of the byte at `offset`. -/
  base : Nat
  /--
  Number of the latest line (zero-based).

  It only advances after consumption of LF.
  -/
  line : Nat
  /--
  Offset of the start of the current line (after line break, zero-based)

  It only advances after consumption of LF.
  -/
  lineStart : Nat
  /-- Token batch, may be only partially filled. -/
  batch : TokenBatch
  /- LEAN: not in Rust: two facts about the fields above, which show that every token handed
  over has a byte and is after the tokens before it (see `TokenBatch.ordered`). -/
  /-- The token in progress, if any, starts before `offset`. -/
  tokenStarted : state = .normal ∨ tokenStart.offset < offset
  /-- The tokens of the batch end at or before `offset`. -/
  batchEnded : batch.lastEnd ≤ offset

/-- The lexer with its consumer. -/
structure Lexer (H : Type) (recovery : Recovery := .failFast) where
  /-- Consumer of produced tokens. -/
  handler : H
  core : LexerCore

/- LEAN: not in Rust. What a step of the lexer keeps true of its state, from which the loop over
a slice is shown to end: the offset only grows from `low`, its value when the step started; and
the offset and the tokens of the batch are at or after the floor (see `Interrupted`), and a
token in progress ends after it: it starts at or after the floor and has a byte, or the offset,
at or before its end, is after the floor. -/
/--
The lexer state is within the bounds: its offset is at or after `low`; and if there is a
floor, the offset is at or after it, the lexer is between tokens or the token start is at or
after the floor or the offset after it, and every token of the batch starts at or after it.
-/
def LexerCore.Bound (floor : Option Nat) (low : Nat) (c : LexerCore) : Prop :=
  low ≤ c.offset ∧
    ∀ p, floor = some p → p ≤ c.offset ∧
      (c.state = .normal ∨ p ≤ c.tokenStart.offset ∨ p < c.offset) ∧ c.batch.StartsFrom p

abbrev InnerM (H : Type) (m : Type → Type) := StateT LexerCore (StateT H m)

/- LEAN: a step runs on the lexer state together with the proof that it is within the bounds,
which costs nothing when the lexer runs. -/
abbrev StepM (H : Type) (m : Type → Type) (floor : Option Nat) (low : Nat) :=
  StateT {c : LexerCore // c.Bound floor low} (StateT H m)

abbrev LexM (H : Type) (m : Type → Type) (R E : Type) (floor : Option Nat) (low : Nat) :=
  ExceptT (Interrupted R E floor) (StepM H m floor low)

/-- The stream offset of the index `position` of the slice. -/
@[inline]
def LexerCore.offsetAt (self : LexerCore) (position : Nat) : Nat :=
  self.offset + (position - self.base)

/-- Location of the index `position` of the slice.

Every line feed before `position` must be marked before calling this. -/
@[inline]
def LexerCore.locationAt (self : LexerCore) (position : Nat) : Location :=
  let offset := self.offsetAt position
  { offset, line := self.line, column := offset - self.lineStart }

/-- The current location: that of the next byte to be lexed. -/
@[inline]
def LexerCore.currentLocation (self : LexerCore) : Location :=
  self.locationAt self.base

/-- The lexer state with the offset moved on to that of `position`, the next byte to be lexed. -/
@[inline]
def LexerCore.advance (self : LexerCore) (position : Nat) : LexerCore :=
  { self with
    offset := self.offsetAt position
    base := position
    tokenStarted := self.tokenStarted.imp_right fun h => Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
    batchEnded := Nat.le_trans self.batchEnded (Nat.le_add_right _ _) }

theorem LexerCore.Bound.advance {self : LexerCore} {floor : Option Nat} {low : Nat}
    (h : self.Bound floor low) (position : Nat) : (self.advance position).Bound floor low :=
  ⟨Nat.le_trans h.1 (Nat.le_add_right _ _), fun p hp =>
    ⟨Nat.le_trans (h.2 p hp).1 (Nat.le_add_right _ _),
      (h.2 p hp).2.1.imp_right
        (Or.imp_right fun h => Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)),
      (h.2 p hp).2.2⟩⟩

/--
Moves the lexer back to `location`, which the tokens handed over
so far end at, discarding whatever was lexed beyond it; `position` is its index in the
slice.
-/
def LexerCore.resumeAt (self : LexerCore) (location : Location) (position : Nat) : LexerCore :=
  -- the region after the location was lexed once already,
  -- restore all bookkeeping
  -- a stop inside an arm leaves it mid-token
  { self with
    offset := location.offset
    base := position
    line := location.line
    lineStart := location.offset - location.column
    state := .normal
    tokenContent := self.tokenContent.clear
    /- LEAN: not in Rust: the token start and the batch are not used before they are set
    again, as the lexer is between tokens and the batch was handed over; they are set here so
    that nothing in the state is before the location. -/
    tokenStart := location
    batch := self.batch.clear location.offset
    tokenStarted := .inl rfl
    batchEnded := Nat.le_of_eq (TokenBatch.lastEnd_clear _ _) }

theorem LexerCore.bound_resumeAt (self : LexerCore) (location : Location) (position : Nat) :
    (self.resumeAt location position).Bound (some location.offset) 0 :=
  ⟨Nat.zero_le _, fun p hp => by
    cases hp
    exact ⟨Nat.le_refl _, .inl rfl, TokenBatch.startsFrom_clear _ _ _⟩⟩

theorem LexerCore.Bound.weaken {self : LexerCore} {floor : Option Nat} {low : Nat}
    (h : self.Bound floor low) : self.Bound floor 0 :=
  ⟨Nat.zero_le _, h.2⟩

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat}

/- LEAN: `getThe` and `modifyThe` name the state they access, as there are two. Reading the
state with `← getCore` gives a reference to it; the code below lets such references die before
the state is modified, so that it is modified in place and not copied. -/
@[inline]
def getCore : LexM H m R E floor low LexerCore :=
  return (← getThe {c : LexerCore // c.Bound floor low}).val

/-- Changes the lexer state by `f`, which keeps it within the bounds. -/
@[inline]
def modifyCore (f : LexerCore → LexerCore)
    (h : ∀ c, c.Bound floor low → (f c).Bound floor low := by intro c hc; exact hc) :
    LexM H m R E floor low Unit :=
  modifyThe {c : LexerCore // c.Bound floor low} fun c => ⟨f c.val, h c.val c.property⟩

/-- Changes the lexer state by `f`, which is given the proof that the state is within the
bounds. -/
@[inline]
def modifyBound
    (f : (c : LexerCore) → c.Bound floor low → {c' : LexerCore // c'.Bound floor low}) :
    LexM H m R E floor low Unit :=
  modifyThe {c : LexerCore // c.Bound floor low} fun c => f c.val c.property

/-- Moves the lexer to the normal state. -/
@[inline]
def setNormal : LexM H m R E floor low Unit :=
  modifyCore (fun c => { c with state := .normal, tokenStarted := .inl rfl })
    fun _ hc => ⟨hc.1, fun p hp => ⟨(hc.2 p hp).1, .inl rfl, (hc.2 p hp).2.2⟩⟩

/- LEAN: not in Rust. Where the token in progress started before the step, at `start`, and is
lexed on in another state. The token start is written again with its value, so that the fact
`LexerCore.tokenStarted` follows from what the step knows. -/
/-- What a step that started with a token in progress knows of it: it starts at `start`,
before the step's offset, which is after the floor. -/
abbrev Started (floor : Option Nat) (low : Nat) (start : Location) : Prop :=
  start.offset < low ∧ ∀ p, floor = some p → p < low

/-- Moves the token in progress, which starts at `start`, to the state. -/
@[inline]
def setTokenState (state : LexerState) (start : Location) (h : Started floor low start) :
    LexM H m R E floor low Unit :=
  modifyBound fun c hc =>
    ⟨{ c with state, tokenStart := start, tokenStarted := .inr (Nat.lt_of_lt_of_le h.1 hc.1) },
      ⟨hc.1, fun p hp =>
        ⟨(hc.2 p hp).1, .inr (.inr (Nat.lt_of_lt_of_le (h.2 p hp) hc.1)), (hc.2 p hp).2.2⟩⟩⟩

/- LEAN: Rust's `C::CONSUMES_WHITESPACE_AND_COMMENTS`, read from the consumer's instance. -/
@[inline]
def consumesWhitespaceAndComments : LexM H m R E floor low Bool :=
  pure (Consume.consumesWhitespaceAndComments (H := H))

/- LEAN: the content buffer is taken out of the state before it is changed:
changing `c.tokenContent` while `c` still refers to it would find it shared and copy it,
together with its array. -/
/-- Changes the content buffer in place. -/
@[inline]
def modifyContent (f : ContentBuffer → ContentBuffer) : LexM H m R E floor low Unit :=
  modifyCore fun c =>
    let content := c.tokenContent
    let c := { c with tokenContent := ContentBuffer.empty }
    { c with tokenContent := f content }

/-- Appends the bytes of the slice from index `start` to index `stop` to the content. -/
@[inline]
def extendContent (input : ByteSlice) (start stop : Nat) : LexM H m R E floor low Unit :=
  modifyContent (·.extendFrom input.byteArray (input.start + start) (input.start + stop))

@[inline]
def pushContent (c : UInt8) : LexM H m R E floor low Unit :=
  modifyContent (·.push c)

/- LEAN: what the loop of `lexNormal` keeps true of the offset `offset` of the index `base`,
from which it computes the offsets of the indices after it. -/
/-- The offset is at or after the step's offset and the floor. -/
abbrev Frame (floor : Option Nat) (low : Nat) (offset : Nat) : Prop :=
  low ≤ offset ∧ ∀ p, floor = some p → p ≤ offset

/- LEAN: Rust computes the location from the lexer's offset; here it is computed from `offset`
and `base`, the loop's copies of them, so that the proofs know its offset. The token start is
set to it and the state to normal, where the lexer already is. -/
/--
Starts a token at `position`, whose offset is `offset` plus the bytes from `base` to it, and
returns its location.
-/
@[inline]
def startToken (offset : Nat) (base position : Nat) (hframe : Frame floor low offset) :
    LexM H m R E floor low
      {start : Location // start.offset = offset + (position - base)} := do
  -- update the token start to the computed location
  let c ← getCore
  let startOffset := offset + (position - base)
  let start : Location :=
    { offset := startOffset, line := c.line, column := startOffset - c.lineStart }
  modifyCore (fun c => { c with tokenStart := start, state := .normal, tokenStarted := .inl rfl })
    fun _ hc => ⟨hc.1, fun p hp =>
      ⟨(hc.2 p hp).1, .inr (.inl (Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _))),
        (hc.2 p hp).2.2⟩⟩
  -- clear the token string
  modifyContent (·.clear)
  return ⟨start, rfl⟩

@[inline]
def markLineFeedAt (position : Nat) : LexM H m R E floor low Unit :=
  -- when lexing a run, this is used to mark a line feed
  -- the locations must only refer to positions after it afterwards
  modifyCore fun c => { c with line := c.line + 1, lineStart := c.offsetAt position + 1 }

/-- Fails with an error spanning up to `position` with effective failure at `failure`. -/
def failWith (kind : LexicalErrorKind) (position failure : Nat) :
    LexM H m R E floor low α := do
  let c ← getCore
  let span := Span.newUnchecked c.tokenStart (c.locationAt position)
  -- no tokens have been consumed, as this is an error
  -- that occurred during lexing
  throw {
    result := .error (.lexical { kind, span })
    location := c.locationAt failure
    stopAfter := fun _ _ _ h => nomatch h }

/--
Fails with an error spanning the token up to `position`.

Used for errors detected mid-run, e.g. forbidden byte in a string
or a backslash in a quoted symbol.
-/
/- LEAN: Rust panics if `position` is zero, which no caller passes: an error detected at a
byte spans that byte. -/
def failAt (kind : LexicalErrorKind) (position : Nat) : LexM H m R E floor low α :=
  -- the byte before the position raised the error
  failWith kind position (position - 1)

/-- Fails with an error spanning the token so far and, if it ended at a byte, that byte. -/
def fail (kind : LexicalErrorKind) (tokenEnd : TokenEnd) : LexM H m R E floor low α :=
  -- if the token ended at a byte, that byte raised the error,
  -- otherwise the end of the input did
  failWith kind (tokenEnd.position + if tokenEnd.atByte then 1 else 0) tokenEnd.position

/--
Checks that `next`, the byte at `position` right after a token,
delimits it.

Called before the token is handed over, so that a token without its
delimiter never reaches the handler; the error spans the token and
the offending byte.
-/
@[inline]
def expectDelimiter (next : UInt8) (position : Nat) : LexM H m R E floor low Unit := do
  unless isDelimiter next do
    failAt .missingDelimiter (position + 1)

/- LEAN: runs the consumer on the cursor. The consumer runs in `StateT H m`, which the `←` lifts
into the lexer's monad, where the consumer is the inner state. -/
def callConsumer {batch : BatchTag} (cursor : BatchCursor batch) (h : cursor.HasNext) :
    LexM H m R E floor low
      (Except E (ControlFlow R) × { c : BatchCursor batch // c.Consumed cursor }) := do
  let action : StateT H m
      (Except E (ControlFlow R) × { c : BatchCursor batch // c.Consumed cursor }) :=
    Consume.consume (H := H) cursor h
  action

/- LEAN: Rust's `flush_cursor` loops while the cursor is not empty; here the loop is the
recursion, which ends as every call of the consumer consumes a token, by the proof the
consumer returns. The interruption is returned rather than thrown, so that the caller can
take the batch back first. A stop is after the floor, as every token of the batch ends after
it (`BatchCursor.Consumed.lt_consumedEndOf`). -/
/--
Hands the cursor over to the consumer until nothing remains in it or the consumer stops.

Returns the stop, if the consumer stopped, and the cursor as the consumer left it.
-/
def flushCursor {batch : BatchTag} (cursor : BatchCursor batch)
    (hfloor : ∀ p, floor = some p → cursor.EndsAfter p) :
    LexM H m R E floor low (Option (Interrupted R E floor) × BatchCursor batch) := do
  -- flush the cursor until nothing remains
  if h : cursor.HasNext then
    let (result, ⟨next, consumed⟩) ← callConsumer cursor h
    -- the stop takes effect after the consumed tokens
    let location := next.consumedEndOf consumed
    have after : ∀ p, floor = some p → p < location.offset := fun p hp =>
      consumed.lt_consumedEndOf (hfloor p hp)
    -- process the result
    match result with
    | .ok .continue =>
      if next.relexRequested then
        -- we need to stop and relex here
        return (some { result := .ok .relex, location, stopAfter := fun p hp _ _ => after p hp },
          next)
      else
        -- zero the number of consumed tokens in the cursor
        -- continue flushing until nothing remains
        have : next.resetConsumed.remaining < cursor.remaining := by
          rw [BatchCursor.remaining_resetConsumed]
          exact consumed.remaining_lt
        flushCursor next.resetConsumed fun p hp =>
          BatchCursor.endsAfter_resetConsumed (consumed.follows.endsAfter (hfloor p hp))
    | .ok (.break result) =>
      return (some {
        result := .ok (.finished result)
        location
        stopAfter := fun p hp _ _ => after p hp }, next)
    | .error err =>
      return (some {
        result := .error (.consumer err)
        location
        stopAfter := fun _ _ _ h => nomatch h }, next)
  else
    -- everything was consumed without break or error
    return (none, cursor)
termination_by cursor.remaining

/-- Puts a spent batch back into the lexer state, empty. -/
@[inline]
def storeSpent (spent : TokenBatch) : LexM H m R E floor low Unit :=
  modifyBound fun c hc =>
    ⟨{ c with
        batch := spent.clear c.offset
        batchEnded := Nat.le_of_eq (TokenBatch.lastEnd_clear _ _) },
      ⟨hc.1, fun p hp => ⟨(hc.2 p hp).1, (hc.2 p hp).2.1, TokenBatch.startsFrom_clear _ _ _⟩⟩⟩

/- LEAN: Rust's `flush_cursor` takes a cursor over the lexer's arrays; here the batch itself
is handed to the consumer in the cursor, and taken back afterwards, whatever the consumer
decides, so that its storage is overwritten by the next batch. The batch's array of contents
is then set to `bytesAfter`, so that the batch does not keep a reference to the lexer's
content buffer, which would make the buffer's next change copy it. If the consumer stops,
the batch goes back into the lexer state, empty, before the stop is thrown; otherwise the
caller takes it. -/
/-- Hands the batch over to the consumer and takes it back, spent. -/
def handOver (batch : TokenBatch) (bytesAfter : ByteArray)
    (hfloor : ∀ p, floor = some p → batch.EndsAfter p) : LexM H m R E floor low TokenBatch := do
  let (stop, cursor) ← flushCursor (BatchCursor.new (← getCore).version batch) fun p hp =>
    BatchCursor.endsAfter_new (hfloor p hp) _
  if (← getCore).recovers then
    match stop with
    | some _ =>
      -- the consumer has not taken the whole batch
      -- count the actually consumed parentheses only
      -- and reset the lexed depth to them
      modifyCore fun c =>
        let consumedDepth := cursor.foldConsumedCategories c.consumedDepth fun depth category =>
          match category with
          | .parenOpen => depth + 1
          -- saturate to avoid going below zero depth
          | .parenClose => depth - 1
          | _ => depth
        { c with consumedDepth, lexedDepth := consumedDepth }
    | none =>
      -- everything was consumed: the consumer has taken every token lexed so far,
      -- so the consumed parentheses are the same that were lexed
      modifyCore fun c => { c with consumedDepth := c.lexedDepth }
  -- set our version to the cursor-requested version, and take the batch back
  modifyCore fun c => { c with version := cursor.version }
  let spent : TokenBatch := { Lexer.Internal.intoBatch cursor with bytes := bytesAfter }
  if let some interrupted := stop then
    storeSpent spent
    throw interrupted
  return spent

/-- Takes the batch out of the lexer state, leaving an empty one without storage. -/
@[inline]
def takeBatch :
    LexM H m R E floor low {batch : TokenBatch // ∀ p, floor = some p → batch.StartsFrom p} :=
  modifyGetThe {c : LexerCore // c.Bound floor low} fun c =>
    (⟨c.val.batch, fun p hp => (c.property.2 p hp).2.2⟩,
      ⟨{ c.val with
          batch := default
          batchEnded := TokenBatch.lastEnd_default ▸ Nat.zero_le _ },
        ⟨c.property.1, fun p hp =>
          ⟨(c.property.2 p hp).1, (c.property.2 p hp).2.1, TokenBatch.startsFrom_default p⟩⟩⟩)

def flushBatch : LexM H m R E floor low Unit := do
  -- the batch is spent once handed over, no matter what the handler decides
  if (← getCore).batch.len == 0 then
    return
  let ⟨batch, hbatch⟩ ← takeBatch
  let bytes := batch.bytes
  storeSpent (← handOver batch bytes fun p hp => (hbatch p hp).endsAfter)

/--
Hands over a single token whose content is in the lexer's content buffer,
spanning from `start` to `end`.
-/
/- LEAN: Rust hands such a token over in a cursor of its own; here it goes in the batch,
which is empty after the flush, with the content buffer as its array of contents for the
one token. -/
def handOverStored (ty : TokenCategory) (_hty : ty ≠ .endOfFile) (start «end» : Location)
    (hend : start.offset < «end».offset) (hfloor : ∀ p, floor = some p → p < «end».offset) :
    LexM H m R E floor low Unit := do
  -- flush the batch, then hand over this token
  flushBatch
  let ⟨batch, _⟩ ← takeBatch
  let bytes := batch.bytes
  let c ← getCore
  let batch := ({ batch.clear start.offset with bytes := c.tokenContent.bytes } : TokenBatch)
    |>.pushLocated ty 0 c.tokenContent.len start «end»
      (Nat.le_of_eq (TokenBatch.lastEnd_clear _ _)) (.inl hend)
  storeSpent (← handOver batch bytes fun p hp =>
    TokenBatch.endsAfter_pushLocated (fun _ h => absurd h (Nat.not_lt_zero _)) (hfloor p hp))

/-- Hands over the end-of-file token, at the location. -/
def handOverEof (location : Location) : LexM H m R E none low Unit := do
  -- flush the batch, then hand over this token
  flushBatch
  let ⟨batch, _⟩ ← takeBatch
  let bytes := batch.bytes
  let c ← getCore
  let batch := ({ batch.clear location.offset with bytes := c.tokenContent.bytes } : TokenBatch)
    |>.pushLocated .endOfFile 0 c.tokenContent.len location location
      (Nat.le_of_eq (TokenBatch.lastEnd_clear _ _)) (.inr ⟨rfl, rfl⟩)
  storeSpent (← handOver batch bytes fun _ h => nomatch h)

/-- The location of the index `position`, given that `base` is the index of the step's
offset. -/
@[inline]
def locationFrom (base position : Nat) :
    LexM H m R E floor low {location : Location // low ≤ location.offset} := do
  let c ← getCore
  let offset := low + (position - base)
  return ⟨{ offset, line := c.line, column := offset - c.lineStart }, Nat.le_add_right _ _⟩

/- LEAN: Rust sinks a token with its content either borrowed from the slice or stored in the
content buffer. A token lexed by `lexNormal` is borrowed and put into the batch that the loop
holds (see `pushBorrowed`); the token in progress of a step that started with it is stored,
and sunk here. `start` is where it starts, and `base` the index of the step's offset. -/
/-- Sinks the token in progress, which ends at `tokenEnd`; its content is in the content
buffer. -/
@[inline]
def sinkStored (ty : TokenCategory) (hty : ty ≠ .endOfFile) (tokenEnd : TokenEnd)
    (start : Location) (base : Nat) (h : Started floor low start) :
    LexM H m R E floor low Unit := do
  -- this is in our own buffer, so we cannot put it into the batch
  -- as we need the buffer usable for the next token
  let ⟨«end», hend⟩ ← locationFrom base tokenEnd.position
  handOverStored ty hty start «end» (Nat.lt_of_lt_of_le h.1 hend) fun p hp =>
    Nat.lt_of_lt_of_le (h.2 p hp) hend

/--
Sinks a decimal token.

The token's own shape is checked first, then that `next`, the byte
at the end (if there is one), delimits it.
-/
@[inline]
def finishDecimal (tokenEnd : TokenEnd) (next : Option UInt8) (start : Location)
    (base : Nat) (h : Started floor low start) : LexM H m R E floor low Unit := do
  -- decimals of the form 7. without any digit in fractional part are disallowed
  let last := Content.stored.last? (← getCore).tokenContent
  if last.isNone || last == some (byte! '.') then
    fail .fractionDigitExpected tokenEnd
  if let some next := next then
    expectDelimiter next tokenEnd.position
  sinkStored .decimal nofun tokenEnd start base h

@[inline]
def finishNumeral (tokenEnd : TokenEnd) (start : Location) (base : Nat)
    (h : Started floor low start) : LexM H m R E floor low Unit :=
  sinkStored .numeral nofun tokenEnd start base h

/-- The type of the token of the digit run: hexadecimal or binary. -/
theorem DigitRun.tokenType_ne {run : DigitRun}
    (h : run = HEXADECIMAL_RUN ∨ run = BINARY_RUN) : run.tokenType ≠ .endOfFile := by
  rcases h with h | h <;> (subst h; nofun)

/--
Sinks a hexadecimal/binary token.

The token's own shape is checked first, then that `next`, the byte
at the end (if there is one), delimits it.
-/
@[inline]
def finishDigitRun (run : DigitRun) (hrun : run = HEXADECIMAL_RUN ∨ run = BINARY_RUN)
    (tokenEnd : TokenEnd) (next : Option UInt8) (start : Location) (base : Nat)
    (h : Started floor low start) : LexM H m R E floor low Unit := do
  -- digit runs must not be empty
  if Content.stored.size (← getCore).tokenContent == 0 then
    fail run.emptyError tokenEnd
  if let some next := next then
    expectDelimiter next tokenEnd.position
  sinkStored run.tokenType (DigitRun.tokenType_ne hrun) tokenEnd start base h

@[inline]
def finishSimpleSymbol (tokenEnd : TokenEnd) (start : Location) (base : Nat)
    (h : Started floor low start) : LexM H m R E floor low Unit :=
  sinkStored .unquotedSymbol nofun tokenEnd start base h

/--
Sinks a keyword.

The token's own shape is checked first, then that `next`, the byte
at the end (if there is one), delimits it.
-/
@[inline]
def finishKeyword (tokenEnd : TokenEnd) (next : Option UInt8) (start : Location)
    (base : Nat) (h : Started floor low start) : LexM H m R E floor low Unit := do
  -- ensure the keyword is not empty
  if Content.stored.size (← getCore).tokenContent == 0 then
    fail .forbiddenKeywordName tokenEnd
  if let some next := next then
    expectDelimiter next tokenEnd.position
  sinkStored .keyword nofun tokenEnd start base h

@[inline]
def finishStringLiteral (tokenEnd : TokenEnd) (start : Location) (base : Nat)
    (h : Started floor low start) : LexM H m R E floor low Unit :=
  sinkStored .string nofun tokenEnd start base h

@[inline]
def finishWhitespace (tokenEnd : TokenEnd) (start : Location) (base : Nat)
    (h : Started floor low start) : LexM H m R E floor low Unit :=
  sinkStored .whitespace nofun tokenEnd start base h

/- LEAN: Rust keeps the batch length, the line and the line start in locals of `lex_normal`.
Here the local is the batch itself, which the loop passes along; the line and the line start
stay in the lexer state, which the fast path only reads. While the loop holds the batch, the
lexer state has an empty batch. Unlike Rust, the loop holds the batch on its slow path too,
and puts it back into the lexer state only where it ends: where it returns or throws an
error (`leave`, `leavePending`). Its offset and index, `offset` and `base`, go back into
the lexer state with it, moved on to where the loop ends; this is where the lexer is anyway,
as the loop over the slice moves them there after the step. The batch is a local of its own,
not a field of a structure of locals, so that it is not shared when it is changed. What the
loop knows of the batch it holds at `index` (`Held`) shows that the tokens it appends are in
order. -/

/-- The batch that the loop of `lexNormal` holds at `index`: its tokens end at or before
`index`, and start at or after the floor. -/
abbrev Held (floor : Option Nat) (offset : Nat) (base index : Nat) (batch : TokenBatch) :
    Prop :=
  batch.lastEnd ≤ offset + (index - base) ∧ ∀ p, floor = some p → batch.StartsFrom p

theorem Held.mono {floor : Option Nat} {offset : Nat} {base index next : Nat}
    {batch : TokenBatch} (h : Held floor offset base index batch)
    (_hindex : base ≤ index) (hnext : index ≤ next) : Held floor offset base next batch :=
  ⟨by have := h.1; omega, h.2⟩

/-- Puts the batch held by the loop back into the lexer state, with the lexer at `position`,
between tokens. -/
@[inline]
def leave (offset : Nat) (base position : Nat) (batch : TokenBatch)
    (hframe : Frame floor low offset) (hbatch : Held floor offset base position batch) :
    LexM H m R E floor low Unit :=
  modifyBound fun c _ =>
    ⟨{ c with
        batch, offset := offset + (position - base), base := position, state := .normal,
        tokenStarted := .inl rfl, batchEnded := hbatch.1 },
      ⟨Nat.le_trans hframe.1 (Nat.le_add_right _ _), fun p hp =>
        ⟨Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _), .inl rfl, hbatch.2 p hp⟩⟩⟩

/-- Puts the batch held by the loop back into the lexer state, with the token from `start`
left unfinished in `state` at `position`. -/
@[inline]
def leavePending (state : LexerState) (start : Location) (offset : Nat)
    (base position : Nat) (batch : TokenBatch) (hframe : Frame floor low offset)
    (hbatch : Held floor offset base position batch)
    (hstart : start.offset < offset + (position - base))
    (hfloor : ∀ p, floor = some p → p ≤ start.offset) : LexM H m R E floor low Unit :=
  modifyBound fun c _ =>
    ⟨{ c with
        batch, offset := offset + (position - base), base := position, state,
        tokenStart := start, tokenStarted := .inr hstart, batchEnded := hbatch.1 },
      ⟨Nat.le_trans hframe.1 (Nat.le_add_right _ _), fun p hp =>
        ⟨Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _), .inr (.inl (hfloor p hp)),
          hbatch.2 p hp⟩⟩⟩

/-- Hands the full batch held by the loop over, and gives it back empty, with the origin. -/
@[inline]
def flushHeld (batch : TokenBatch) (origin : Nat)
    (hbatch : ∀ p, floor = some p → batch.StartsFrom p) :
    LexM H m R E floor low
      {batch : TokenBatch //
        batch.lastEnd = origin ∧ ∀ p, floor = some p → batch.StartsFrom p} := do
  -- batch capacity reached, we need to flush the batch
  let bytes := batch.bytes
  let spent ← handOver batch bytes fun p hp => (hbatch p hp).endsAfter
  return ⟨spent.clear origin, TokenBatch.lastEnd_clear _ _,
    fun _ _ => TokenBatch.startsFrom_clear _ _ _⟩

/--
Puts a fast-path token into the batch if `emit` is set, flushing the batch
when it is full.

The content is from `contentStart` to `contentStop` in the slice, and the span is on the
current line, over `start` to `end` in the slice. `offset` is the stream offset of the
index `base`.
-/
/- LEAN: Rust writes the entry even when it is not emitted, as the next token overwrites it;
here a token that is not emitted is not written. -/
@[inline]
def pushFast (input : ByteSlice) (batch : TokenBatch) (offset : Nat) (base : Nat)
    (ty : TokenCategory) (contentStart contentStop start «end» : Nat) (emit : Bool)
    (hty : ty ≠ .endOfFile) (hstart : base ≤ start)
    (hend : start < «end») (hframe : Frame floor low offset)
    (hbatch : Held floor offset base start batch) :
    LexM H m R E floor low {batch : TokenBatch // Held floor offset base «end» batch} := do
  if !emit then
    return ⟨batch, hbatch.mono hstart (Nat.le_of_lt hend)⟩
  let c ← getCore
  let line := c.line
  let lineStart := c.lineStart
  have hlt : offset + (start - base) < offset + («end» - base) := by omega
  let batch := batch.pushOnLine ty (input.start + contentStart) (input.start + contentStop)
    line lineStart (offset + (start - base)) (offset + («end» - base)) hbatch.1
    (.inl hlt)
  have hfrom : ∀ p, floor = some p → batch.StartsFrom p := fun p hp =>
    TokenBatch.startsFrom_pushOnLine (hbatch.2 p hp)
      (Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _)) hty
  if batch.len == BATCH_CAPACITY then
    let ⟨batch, hlast, hfrom⟩ ← flushHeld batch (offset + («end» - base)) hfrom
    return ⟨batch, Nat.le_of_eq hlast, hfrom⟩
  else
    return ⟨batch, Nat.le_of_eq (TokenBatch.lastEnd_pushOnLine ..), hfrom⟩

/--
Puts a token lexed on the slow path into the batch, flushing the batch when it is full.

The content is from `contentStart` to `contentStop` in the slice, and the span from `start`
to `tokenEnd` in the slice. `offset` is the stream offset of the index `base`.
-/
/- LEAN: Rust's `sink_slice` with borrowed content, which puts the token into the lexer's
batch; here into the batch the loop holds. -/
@[inline]
def pushBorrowed (input : ByteSlice) (batch : TokenBatch) (offset : Nat) (base : Nat)
    (ty : TokenCategory) (contentStart contentStop : Nat) (start : Location) (tokenEnd : Nat)
    (hty : ty ≠ .endOfFile) (hafter : batch.lastEnd ≤ start.offset)
    (hend : start.offset < offset + (tokenEnd - base))
    (hfloor : ∀ p, floor = some p → p ≤ start.offset ∧ batch.StartsFrom p) :
    LexM H m R E floor low {batch : TokenBatch // Held floor offset base tokenEnd batch} := do
  let c ← getCore
  let endOffset := offset + (tokenEnd - base)
  let «end» : Location := { offset := endOffset, line := c.line, column := endOffset - c.lineStart }
  let batch := batch.pushLocated ty (input.start + contentStart) (input.start + contentStop) start
    «end» hafter (.inl hend)
  have hfrom : ∀ p, floor = some p → batch.StartsFrom p := fun p hp =>
    TokenBatch.startsFrom_pushLocated (hfloor p hp).2 (hfloor p hp).1 hty
  if batch.len == BATCH_CAPACITY then
    let ⟨batch, hlast, hfrom⟩ ← flushHeld batch endOffset hfrom
    return ⟨batch, Nat.le_of_eq hlast, hfrom⟩
  else
    return ⟨batch, Nat.le_of_eq (TokenBatch.lastEnd_pushLocated ..), hfrom⟩

/--
Moves a fast-path symbol run that cannot be finished
in this slice to the stored path.

The token itself starts at `index`, its content either at `index`
(simple symbol) or `after` (quoted symbol, excludes pipe), and
the token continues at least to `runEndAt`, where it has been
left unfinished.
-/
def storeUnfinishedSymbolRun (input : ByteSlice) (entry : UInt8) (offset : Nat)
    (base index after runEndAt : Nat) (batch : TokenBatch) (hframe : Frame floor low offset)
    (hindex : base ≤ index) (hrun : index < runEndAt)
    (hbatch : Held floor offset base index batch) : LexM H m R E floor low Unit := do
  let ⟨start, hstart⟩ ← startToken offset base index hframe
  have hpending : start.offset < offset + (runEndAt - base) := by rw [hstart]; omega
  have hfloor : ∀ p, floor = some p → p ≤ start.offset := fun p hp => by
    rw [hstart]; exact Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _)
  have hbatch := hbatch.mono hindex (Nat.le_of_lt hrun)
  if entry &&& FAST_PIPE != 0 then
    -- quoted symbol, skip the start pipe
    extendContent input after runEndAt
    leavePending .quotedSymbol start offset base runEndAt batch hframe hbatch hpending hfloor
  else
    -- simple symbol, do not skip anything
    extendContent input index runEndAt
    leavePending .simpleSymbol start offset base runEndAt batch hframe hbatch hpending hfloor

/- LEAN: the loops of the lexer are recursions on an index in the slice, which are shown to
end by the bytes left after it: every call goes on after a byte it has read. The facts that
show it are stated with `have` before the call; the tactic expands the local definitions that
they and the call are stated with, and does the arithmetic. -/
local macro "decreasing_position" : tactic =>
  `(tactic| ((try simp +zetaDelta only at *) <;> omega))

/- LEAN: not in Rust. What `startWhitespace` needs to return an index after the start of the
run: a byte there that the run takes. -/
/--
Whether the byte at `position` continues a whitespace run: a line feed, or whitespace other
than it.
-/
def ContinuesWhitespace (input : ByteSlice) (position : Nat) : Prop :=
  ∃ c, get? input position = some c ∧ (c = byte! '\n' ∨ endsRun c RUN_NON_LF_WHITESPACE = false)

/-- The run ends after its start: the search has passed the start, or the byte where it continues
belongs to the run. -/
theorem lt_whitespaceRunEnd {input : ByteSlice} {index start : Nat} {c : UInt8}
    (hindex : index ≤ start)
    (hrun : index < start ∨ ContinuesWhitespace input start)
    (h : get? input (runEnd input start RUN_NON_LF_WHITESPACE) = some c)
    (hc : ¬(c == byte! '\n') = true) :
    index < runEnd input start RUN_NON_LF_WHITESPACE := by
  have hle := le_runEnd input start RUN_NON_LF_WHITESPACE
  rcases hrun with hlt | ⟨first, hfirst, hlf | hcontinues⟩
  · omega
  · -- the search stops at the line feed, where the byte is not one
    have : runEnd input start RUN_NON_LF_WHITESPACE ≠ start := by
      intro heq
      rw [heq, hfirst] at h
      cases h
      exact hc (by rw [hlf]; rfl)
    omega
  · have := lt_runEnd RUN_NON_LF_WHITESPACE hfirst hcontinues
    omega

/-- A token that starts at `index` ends after its start at a later index. -/
theorem started_lt {offset : Nat} {base index position : Nat} {start : Location}
    (hstart : start.offset = offset + (index - base)) (hindex : base ≤ index)
    (hlt : index < position) : start.offset < offset + (position - base) := by
  rw [hstart]
  omega

/-- A token that starts at an index of the loop starts at or after the floor. -/
theorem started_floor {floor : Option Nat} {low offset : Nat} {base index : Nat}
    {start : Location} (hstart : start.offset = offset + (index - base))
    (hframe : Frame floor low offset) : ∀ p, floor = some p → p ≤ start.offset := fun p hp => by
  rw [hstart]
  exact Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _)

/-- What a token that starts at the index `index` of the loop gives to `pushBorrowed`. -/
theorem started_held {floor : Option Nat} {low offset : Nat} {base index : Nat}
    {start : Location} {batch : TokenBatch} (hstart : start.offset = offset + (index - base))
    (hframe : Frame floor low offset) (hbatch : Held floor offset base index batch) :
    batch.lastEnd ≤ start.offset ∧
      ∀ p, floor = some p → p ≤ start.offset ∧ batch.StartsFrom p :=
  ⟨by rw [hstart]; exact hbatch.1, fun p hp => ⟨started_floor hstart hframe p hp, hbatch.2 p hp⟩⟩

/- LEAN: the loop of `start_whitespace`, as a recursion on `«end»` that is shown to end.
`index` is where the run starts and `«end»` where the search for its end continues; the
search has passed `index` or the byte at `«end»` belongs to the run, so that the index
returned is after `index`, which `lexNormalFrom` is shown to end by. The token of the run starts
at `start`, and goes into the batch that `lexNormalFrom` holds, which comes back with the
index after the run; if the run reaches the end of the slice, the batch goes back into the
lexer state instead, and `none` is returned. -/
def startWhitespaceFrom (input : ByteSlice) (offset : Nat) (base index «end» : Nat)
    (start : Location) (batch : TokenBatch) (hframe : Frame floor low offset)
    (hstart : start.offset = offset + (index - base))
    (hend : base ≤ index ∧ index ≤ «end» ∧ «end» ≤ input.size)
    (hrun : index < «end» ∨ ContinuesWhitespace input «end»)
    (hbatch : Held floor offset base index batch) :
    LexM H m R E floor low (Option {next : Nat × TokenBatch //
      index < next.1 ∧ Held floor offset base next.1 next.2}) := do
  -- find the first byte that is not whitespace other than a line feed
  let «end» := runEnd input «end» RUN_NON_LF_WHITESPACE
  -- the search goes on from where it was
  have : _ ≤ «end» := le_runEnd input _ RUN_NON_LF_WHITESPACE
  match h : get? input «end» with
  | some c =>
    if hc : c == byte! '\n' then
      -- the line feed is a part of the run, mark it and continue
      markLineFeedAt «end»
      have := lt_size_of_get? h
      startWhitespaceFrom input offset base index («end» + 1) start batch hframe hstart
        ⟨hend.1, by omega, by omega⟩ (.inl (by omega)) hbatch
    else
      -- the run has ended inside the slice
      have hlt := lt_whitespaceRunEnd hend.2.1 hrun h hc
      let ⟨batch, hbatch⟩ ← pushBorrowed input batch offset base .whitespace index «end» start
        «end» nofun (started_held hstart hframe hbatch).1 (started_lt hstart hend.1 hlt)
        (started_held hstart hframe hbatch).2
      return some ⟨(«end», batch), hlt, hbatch⟩
  | none =>
    -- we ran out of bytes, update the content and state
    extendContent input index input.size
    have hstop : index < input.size := by
      rcases hrun with hlt | ⟨_, hfirst, _⟩
      · omega
      · have := lt_size_of_get? hfirst
        omega
    leavePending .whitespace start offset base input.size batch hframe
      (hbatch.mono hend.1 (Nat.le_of_lt hstop)) (started_lt hstart hend.1 hstop)
      (started_floor hstart hframe)
    return none
termination_by input.size - «end»
decreasing_by decreasing_position

/--
Lexes the whitespace run that starts at `index` of the slice,
to be handed over as a token.

Returns the index after the run and the batch with its token, if the run ends inside the
slice. Otherwise, the run is stored, the state becomes `whitespace`, the batch goes back into
the lexer state, and `none` is returned.
-/
def startWhitespace (input : ByteSlice) (offset : Nat) (base index : Nat)
    (batch : TokenBatch) (hrun : ContinuesWhitespace input index) (hframe : Frame floor low offset)
    (hindex : base ≤ index) (hbatch : Held floor offset base index batch) :
    LexM H m R E floor low (Option {next : Nat × TokenBatch //
      index < next.1 ∧ Held floor offset base next.1 next.2}) := do
  let ⟨start, hstart⟩ ← startToken offset base index hframe
  have hstop : index ≤ input.size := by
    have ⟨_, hfirst, _⟩ := hrun
    have := lt_size_of_get? hfirst
    omega
  startWhitespaceFrom input offset base index index start batch hframe hstart
    ⟨hindex, Nat.le_refl _, hstop⟩ (.inr hrun) hbatch

/-- What the loops of `lexNormal` return: an index at or after `index`, and after it if
`index` is below the size of the slice. -/
abbrev Past (input : ByteSlice) (index : Nat) :=
  {next : Nat // index ≤ next ∧ (index < input.size → index < next)}

/-- An index past `index` is past every index at or before `index`. -/
@[inline]
def Past.from {input : ByteSlice} {origin index : Nat} (h : origin ≤ index)
    (next : Past input index) : Past input origin :=
  ⟨next.1, Nat.le_trans h next.2.1, fun hlt =>
    if hi : index < input.size then Nat.lt_of_le_of_lt h (next.2.2 hi)
    else by have := next.2.1; omega⟩

/-- The type of a token on the fast path: a quoted symbol, whitespace or a simple symbol. -/
@[inline]
def fastCategory (isQuoted emitsWhitespace : Bool) : TokenCategory :=
  if isQuoted then .quotedSymbol else if emitsWhitespace then .whitespace else .unquotedSymbol

theorem fastCategory_ne (isQuoted emitsWhitespace : Bool) :
    fastCategory isQuoted emitsWhitespace ≠ .endOfFile := by
  unfold fastCategory
  split
  · nofun
  · split <;> nofun

/- LEAN: the Rust function loops over the slice with `while let`; here the loop is the
recursion on `index`. Every arm that continues the loop in Rust calls `lexNormalFrom` again
at the new index, which is after `index`. `offset` is the offset of the index `base`, from
which the loop computes the offsets of the indices after it; they stay the same while the
loop runs. `origin` is where the loop started, which the index returned is past; it stays
the same too, so that the recursive call is the last one and the loop takes no stack. The
recursion is encoded as a well-founded one, which for a function this long nests
deeper than the default limit allows. -/
set_option maxRecDepth 2048 in
def lexNormalFrom (input : ByteSlice) (offset : Nat) (base index : Nat)
    (batch : TokenBatch) (hframe : Frame floor low offset) (hindex : base ≤ index)
    (hbatch : Held floor offset base index batch) (origin : Nat)
    (horigin : origin ≤ index) : LexM H m R E floor low (Past input origin) := do
  match hget : get? input index with
  | none =>
    -- we have consumed every byte of the slice
    -- write the locals back before returning
    leave offset base index batch hframe hbatch
    return Past.from horigin
      ⟨index, Nat.le_refl _, fun h => absurd h (Nat.not_lt.mpr (size_le_of_get?_none hget))⟩
  | some c =>
  have := lt_size_of_get? hget
  -- A fast path handles the most common token types.
  -- It is determined by one table lookup. If the started token is not on
  -- the fast path, a slower path is taken, again looked up. Arms eagerly
  -- try to complete the token with the whole content borrowed from the slice,
  -- which resets the lexer back to the normal state, so the loop can continue.
  --
  -- Lexing only returns early if eager dispatch is not possible,
  -- typically due to running out of bytes in the slice.

  let after := index + 1
  have hafter : index < after := by decreasing_position
  -- Handle the parentheses first as they are numerous and
  -- need no special processing. The closing parenthesis is first
  -- as it forms more clusters.
  if c == byte! ')' then
    if (← getCore).recovers then
      -- saturate to avoid going below zero depth
      -- which would happen with too many closing parentheses
      modifyCore fun core => { core with lexedDepth := core.lexedDepth - 1 }
    let ⟨batch, hbatch⟩ ← pushFast input batch offset base .parenClose index after index after true
      nofun hindex hafter hframe hbatch
    return ← lexNormalFrom input offset base after batch hframe
      (by decreasing_position) hbatch origin
      (Nat.le_trans horigin (Nat.le_of_lt hafter))
  if c == byte! '(' then
    if (← getCore).recovers then
      modifyCore fun core => { core with lexedDepth := core.lexedDepth + 1 }
    let ⟨batch, hbatch⟩ ← pushFast input batch offset base .parenOpen index after index after true
      nofun hindex hafter hframe hbatch
    return ← lexNormalFrom input offset base after batch hframe
      (by decreasing_position) hbatch origin
      (Nat.le_trans horigin (Nat.le_of_lt hafter))
  -- Handle whitespace and symbols in a fast path.
  let fastEntry := fastFlags c
  if fastEntry &&& FAST_ON != 0 then
    -- Fast path, compute where the run ends and where the token ends.
    -- For quoted symbols, the token will end after the closing pipe.
    let runEndAt := runEnd input after (fastEntry &&& FAST_RUN_MASK)
    have : after ≤ runEndAt := le_runEnd input after _
    let isQuoted := fastEntry &&& FAST_PIPE != 0

    -- Check if we need to fall back to state-machine lexing
    -- if we have been asked to emit whitespace and are handling it.
    -- We need to fall back if we have overrun the slice or encountered
    -- a line-feed which needs to update the location line/column.
    let isWhitespace := fastEntry &&& RUN_NON_LF_WHITESPACE != 0
    let emitsWhitespace := (← consumesWhitespaceAndComments) && isWhitespace
    if hws : emitsWhitespace && (get? input runEndAt).all (· == byte! '\n') then
      -- the whitespace token does not end on this line inside the slice
      match ← startWhitespace input offset base index batch
          ⟨c, hget, .inr (not_endsRun_of_fastFlags (by
            simp only [emitsWhitespace, isWhitespace, fastEntry, Bool.and_eq_true] at hws
            exact hws.1.2))⟩ hframe hindex hbatch with
      | none =>
        -- we ran out of bytes inside the whitespace
        return Past.from horigin
          ⟨input.size, by decreasing_position, fun _ => by decreasing_position⟩
      | some ⟨(next, batch), hnext, hbatch⟩ =>
        return ← lexNormalFrom input offset base next batch hframe
          (by decreasing_position) hbatch origin
          (Nat.le_trans horigin (Nat.le_of_lt hnext))

    -- We might need to fall back to state-machine lexing if the token
    -- we have found is not properly finished.
    -- This can only happen if we are processing a quoted symbol
    -- and the expected pipe after the end of the run is not there,
    -- or if we are processing a simple symbol and we overrun the slice.
    -- Parentheses have trivially zero-length runs.
    -- If the consumer does not want whitespace to be emitted,
    -- it can be discarded split.
    /- LEAN: Rust tests whether the token is unfinished inside the test of the condition.
    Here the two tests are one, and the code after it is its `else`, so that the code is known
    there to have found the closing pipe of a quoted symbol at `runEndAt`: the token end after
    it is then after `index`. -/
    let isUnfinished := (runEndAt == input.size || isQuoted) &&
      if isQuoted then get? input runEndAt != some (byte! '|')
      else fastEntry &&& RUN_SIMPLE_SYMBOL != 0
    if hunfinished : isUnfinished then
      -- write the locals back
      storeUnfinishedSymbolRun input fastEntry offset base index after runEndAt batch hframe hindex
        (by decreasing_position) hbatch
      return Past.from horigin ⟨runEndAt, by decreasing_position, fun _ => by decreasing_position⟩
    else
    let tokenEnd := if isQuoted then runEndAt + 1 else runEndAt
    have htokenEnd : runEndAt ≤ tokenEnd := by
      simp only [tokenEnd]
      split <;> omega
    have hend : index < tokenEnd := by decreasing_position

    -- No need to fall back, construct the token: the pipes delimit a quoted
    -- symbol but are not part of its content, any other fast token is its
    -- whole text. The token is on a single line as all fast-lex runs exclude
    -- newlines. Whitespace is only emitted if the consumer wants it.
    let ty := fastCategory isQuoted emitsWhitespace
    let contentStart := if isQuoted then after else index
    let contentStop := if isQuoted then runEndAt else tokenEnd
    let emit := fastEntry &&& FAST_EMIT != 0
    -- A token must be delimited by the byte after it,
    -- fall back to the state machine if the delimiter is not found.
    if emit then
      match get? input tokenEnd with
      | some next =>
        -- the token ended inside the slice: the byte after it must delimit it
        if !isDelimiter next then
          leave offset base index batch hframe hbatch
          let _ ← startToken offset base index hframe
          failAt .missingDelimiter (tokenEnd + 1)
      | none =>
        -- the token ended exactly at the slice end
        -- this must be a quoted symbol as the unquoted symbol
        -- has its token end inside the confirmed run
        -- the quoted symbol must wait for the delimiter
        let ⟨start, hstart⟩ ← startToken offset base index hframe
        extendContent input contentStart contentStop
        leavePending .quotedSymbolClosed start offset base tokenEnd batch hframe
          (hbatch.mono hindex (Nat.le_of_lt hend)) (started_lt hstart hindex hend)
          (started_floor hstart hframe)
        return Past.from horigin ⟨tokenEnd, Nat.le_of_lt hend, fun _ => hend⟩
    -- whitespace needs no delimiter, it is emitted only if the consumer takes it
    let emit := emit || emitsWhitespace
    let ⟨batch, hbatch⟩ ← pushFast input batch offset base ty contentStart contentStop index
      tokenEnd emit (fastCategory_ne _ _) hindex hend hframe hbatch
    -- Fast path done, continue normally after the token end.
    return ← lexNormalFrom input offset base tokenEnd batch hframe
      (by decreasing_position) hbatch origin
      (Nat.le_trans horigin (Nat.le_of_lt hend))

  -- Fast path was not taken, use the slow path.
  match hstart : startOf c with
  | .lineFeed =>
    if ← consumesWhitespaceAndComments then
      -- the line feed starts a whitespace token
      match ← startWhitespace input offset base index batch
          ⟨c, hget, .inl (eq_of_startOf_eq_lineFeed hstart)⟩ hframe hindex hbatch with
      | none =>
        return Past.from horigin
          ⟨input.size, by decreasing_position, fun _ => by decreasing_position⟩
      | some ⟨(next, batch), hnext, hbatch⟩ =>
        lexNormalFrom input offset base next batch hframe
          (by decreasing_position) hbatch origin
          (Nat.le_trans horigin (Nat.le_of_lt hnext))
    else
      -- line feeds must be marked for line offsets
      -- mark it and update the index
      markLineFeedAt index
      lexNormalFrom input offset base after batch hframe
        (by decreasing_position) (hbatch.mono hindex (Nat.le_of_lt hafter)) origin
        (Nat.le_trans horigin (Nat.le_of_lt hafter))
  | .comment =>
    -- a comment has been started
    -- process the run eagerly
    let ⟨tokenStart, hts⟩ ← startToken offset base index hframe
    let «end» := runEnd input after RUN_COMMENT_PLAIN
    have : after ≤ «end» := le_runEnd input after _
    match hbyte : get? input «end» with
    | some c =>
      have := lt_size_of_get? hbyte
      have hnext : index < «end» + 1 := by decreasing_position
      if c == byte! '\n' then
        -- line feed, we need to mark it
        markLineFeedAt «end»
      -- otherwise a carriage return, which also ends the comment
      -- we have reached the end of the comment, which includes
      -- the byte that ended it but not its semicolon
      -- sink the content if it should be emitted
      let ⟨batch, hbatch⟩ ← if ← consumesWhitespaceAndComments then
          pushBorrowed input batch offset base .comment after («end» + 1) tokenStart («end» + 1)
            nofun (started_held hts hframe hbatch).1 (started_lt hts hindex hnext)
            (started_held hts hframe hbatch).2
        else
          pure ⟨batch, hbatch.mono hindex (Nat.le_of_lt hnext)⟩
      -- update the index and continue the loop
      lexNormalFrom input offset base («end» + 1) batch hframe
        (by decreasing_position) hbatch origin
        (Nat.le_trans horigin (Nat.le_of_lt hnext))
    | none =>
      -- we ran out of bytes while inside the comment
      -- extend the content if it should be emitted
      if ← consumesWhitespaceAndComments then
        extendContent input after «end»
      -- update the state and return
      have hlt : index < «end» := by decreasing_position
      leavePending .comment tokenStart offset base «end» batch hframe
        (hbatch.mono hindex (Nat.le_of_lt hlt)) (started_lt hts hindex hlt)
        (started_floor hts hframe)
      return Past.from horigin ⟨«end», Nat.le_of_lt hlt, fun _ => hlt⟩
  | .hash =>
    -- base selection
    let ⟨tokenStart, hts⟩ ← startToken offset base index hframe
    let selected := (get? input after).bind fun c =>
      if c == byte! 'x' then some HEXADECIMAL_RUN
      else if c == byte! 'b' then some BINARY_RUN
      else none
    let some ⟨run, hrun⟩ := selected.attach
      | do
        -- we either encountered a wrong base selection
        -- or ran out of bytes
        -- update the state and return
        -- if the base selection is wrong,
        -- the error will be produced in its function
        leavePending .baseSelection tokenStart offset base after batch hframe
          (hbatch.mono hindex (Nat.le_of_lt hafter)) (started_lt hts hindex hafter)
          (started_floor hts hframe)
        return Past.from horigin ⟨after, Nat.le_of_lt hafter, fun _ => hafter⟩
    have hkind : run = HEXADECIMAL_RUN ∨ run = BINARY_RUN := by
      have ⟨_, _, hselection⟩ := Option.bind_eq_some_iff.mp hrun
      split at hselection
      · exact .inl (Option.some.inj hselection).symm
      · split at hselection
        · exact .inr (Option.some.inj hselection).symm
        · cases hselection
    -- the base has been selected, get a run of its digits
    let start := after + 1
    let afterEnd := runEnd input start run.flag
    have : start ≤ afterEnd := le_runEnd input start _
    have hlt : index < afterEnd := by decreasing_position
    if afterEnd == input.size then
      -- we ran out of bytes
      -- update the content and the state and return
      extendContent input start afterEnd
      leavePending run.state tokenStart offset base afterEnd batch hframe
        (hbatch.mono hindex (Nat.le_of_lt hlt)) (started_lt hts hindex hlt)
        (started_floor hts hframe)
      return Past.from horigin ⟨afterEnd, Nat.le_of_lt hlt, fun _ => hlt⟩
    -- dispatch a token with borrowed content
    -- digit runs must not be empty
    if (borrow input start afterEnd).size (← getCore).tokenContent == 0 then
      leave offset base index batch hframe hbatch
      fail run.emptyError (.mkAtByte afterEnd)
    let next := get input afterEnd
    if !isDelimiter next then
      leave offset base index batch hframe hbatch
      failAt .missingDelimiter (afterEnd + 1)
    let ⟨batch, hbatch⟩ ← pushBorrowed input batch offset base run.tokenType start afterEnd
      tokenStart afterEnd (DigitRun.tokenType_ne hkind) (started_held hts hframe hbatch).1
      (started_lt hts hindex hlt) (started_held hts hframe hbatch).2
    -- update the index and continue the loop
    lexNormalFrom input offset base afterEnd batch hframe
      (by decreasing_position) hbatch origin
      (Nat.le_trans horigin (Nat.le_of_lt hlt))
  | .quote =>
    -- starts a string literal
    let ⟨tokenStart, hts⟩ ← startToken offset base index hframe
    if (← getCore).version == .v2_0 then
      -- SMT-LIB 2.0 has a different string-escape format
      -- than the subsequent versions, leave the fast path immediately
      leavePending .stringLiteral tokenStart offset base after batch hframe
        (hbatch.mono hindex (Nat.le_of_lt hafter)) (started_lt hts hindex hafter)
        (started_floor hts hframe)
      return Past.from horigin ⟨after, Nat.le_of_lt hafter, fun _ => hafter⟩
    -- determine the run of content bytes
    let afterContentEnd := runEnd input after RUN_STRING_PLAIN
    have : after ≤ afterContentEnd := le_runEnd input after _
    -- we can only eagerly borrow if the content is ended by a closing quote
    -- that is definitely not followed by another closing quote
    -- (we cannot borrow a string containing an escape)
    /- LEAN: Rust looks at a two-byte window; here the byte after the closing quote is only
    looked at once the quote is found. -/
    let closed := match get? input afterContentEnd with
      | some quote =>
        if quote == byte! '"' then
          let afterQuote := afterContentEnd + 1
          match get? input afterQuote with
          | some next => if next != byte! '"' then some (afterQuote, next) else none
          | none => none
        else
          none
      | none => none
    match hclosed : closed with
    | some (afterQuote, next) =>
      have : after < afterQuote := by
        simp only [closed] at hclosed
        split at hclosed
        · split at hclosed
          · split at hclosed
            · split at hclosed
              · cases hclosed
                omega
              · cases hclosed
            · cases hclosed
          · cases hclosed
        · cases hclosed
      have hlt : index < afterQuote := by decreasing_position
      -- definitely closed by a quote not followed by another quote
      -- borrow the string literal content and produce a token
      if !isDelimiter next then
        leave offset base index batch hframe hbatch
        failAt .missingDelimiter (afterQuote + 1)
      let ⟨batch, hbatch⟩ ← pushBorrowed input batch offset base .string after afterContentEnd
        tokenStart afterQuote nofun (started_held hts hframe hbatch).1 (started_lt hts hindex hlt)
        (started_held hts hframe hbatch).2
      -- the closing quote is not part of the content,
      -- but was also processed
      lexNormalFrom input offset base afterQuote batch hframe
        (by decreasing_position) hbatch origin
        (Nat.le_trans horigin (Nat.le_of_lt hlt))
    | none =>
      -- we cannot borrow the content
      -- update the content and state and return
      extendContent input after afterContentEnd
      have hlt : index < afterContentEnd := by decreasing_position
      leavePending .stringLiteral tokenStart offset base afterContentEnd batch hframe
        (hbatch.mono hindex (Nat.le_of_lt hlt)) (started_lt hts hindex hlt)
        (started_floor hts hframe)
      return Past.from horigin ⟨afterContentEnd, Nat.le_of_lt hlt, fun _ => hlt⟩
  | .colon =>
    -- starts a keyword
    let ⟨tokenStart, hts⟩ ← startToken offset base index hframe
    -- get a run of simple-symbol bytes
    let afterEnd := runEnd input after RUN_SIMPLE_SYMBOL
    have : after ≤ afterEnd := le_runEnd input after _
    have hlt : index < afterEnd := by decreasing_position
    if afterEnd == input.size then
      -- we ran out of bytes
      -- update the content and state and return
      extendContent input after afterEnd
      leavePending .keyword tokenStart offset base afterEnd batch hframe
        (hbatch.mono hindex (Nat.le_of_lt hlt)) (started_lt hts hindex hlt)
        (started_floor hts hframe)
      return Past.from horigin ⟨afterEnd, Nat.le_of_lt hlt, fun _ => hlt⟩
    -- dispatch a token with borrowed content
    -- ensure the keyword is not empty
    if (borrow input after afterEnd).size (← getCore).tokenContent == 0 then
      leave offset base index batch hframe hbatch
      fail .forbiddenKeywordName (.mkAtByte afterEnd)
    let next := get input afterEnd
    if !isDelimiter next then
      leave offset base index batch hframe hbatch
      failAt .missingDelimiter (afterEnd + 1)
    let ⟨batch, hbatch⟩ ← pushBorrowed input batch offset base .keyword after afterEnd tokenStart
      afterEnd nofun (started_held hts hframe hbatch).1 (started_lt hts hindex hlt)
      (started_held hts hframe hbatch).2
    -- update the index and continue the loop
    lexNormalFrom input offset base afterEnd batch hframe
      (by decreasing_position) hbatch origin
      (Nat.le_trans horigin (Nat.le_of_lt hlt))
  | .digit =>
    let ⟨tokenStart, hts⟩ ← startToken offset base index hframe
    -- determine the run of digits
    let afterEnd := runEnd input after RUN_DIGIT
    have : after ≤ afterEnd := le_runEnd input after _
    have hlt : index < afterEnd := by decreasing_position
    -- check that we are not in a leading zero condition,
    -- which is only possible if the first character was zero
    -- and there is a subsequent digit;
    -- it is possible we will not be able to decide it here
    -- if the slice ends with a single zero, so we need to handle that
    -- when lexing digit in the state `numeralOrDecimal`
    if c == byte! '0' && afterEnd > after then
      leave offset base index batch hframe hbatch
      failAt .numeralLeadingZero (after + 1)
    match hnext : get? input afterEnd with
    | some next =>
      if next == byte! '.' then
        -- a dot starts a fraction, try to do a subsequent run of fraction digits
        let afterFractionEnd := runEnd input (afterEnd + 1) RUN_DIGIT
        have : afterEnd + 1 ≤ afterFractionEnd := le_runEnd input _ _
        have hfraction : index < afterFractionEnd := by decreasing_position
        if afterFractionEnd == input.size then
          -- we ran out of bytes
          -- update the content and state and return
          extendContent input index afterFractionEnd
          leavePending .fraction tokenStart offset base afterFractionEnd batch hframe
            (hbatch.mono hindex (Nat.le_of_lt hfraction)) (started_lt hts hindex hfraction)
            (started_floor hts hframe)
          return Past.from horigin ⟨afterFractionEnd, Nat.le_of_lt hfraction, fun _ => hfraction⟩
        -- dispatch a decimal token with borrowed content
        -- decimals of the form 7. without any digit in fractional part are disallowed
        let last := (borrow input index afterFractionEnd).last? (← getCore).tokenContent
        if last.isNone || last == some (byte! '.') then
          leave offset base index batch hframe hbatch
          fail .fractionDigitExpected (.mkAtByte afterFractionEnd)
        let following := get input afterFractionEnd
        if !isDelimiter following then
          leave offset base index batch hframe hbatch
          failAt .missingDelimiter (afterFractionEnd + 1)
        let ⟨batch, hbatch⟩ ← pushBorrowed input batch offset base .decimal index afterFractionEnd
          tokenStart afterFractionEnd nofun (started_held hts hframe hbatch).1
          (started_lt hts hindex hfraction) (started_held hts hframe hbatch).2
        -- update the index and continue the loop
        lexNormalFrom input offset base afterFractionEnd batch hframe
          (by decreasing_position) hbatch origin
          (Nat.le_trans horigin (Nat.le_of_lt hfraction))
      else
        -- the numeral is not actually a decimal and ends
        -- dispatch a numeral token with borrowed content
        if !isDelimiter next then
          leave offset base index batch hframe hbatch
          failAt .missingDelimiter (afterEnd + 1)
        let ⟨batch, hbatch⟩ ← pushBorrowed input batch offset base .numeral index afterEnd
          tokenStart afterEnd nofun (started_held hts hframe hbatch).1 (started_lt hts hindex hlt)
          (started_held hts hframe hbatch).2
        -- update the index and continue the loop
        lexNormalFrom input offset base afterEnd batch hframe
          (by decreasing_position) hbatch origin
          (Nat.le_trans horigin (Nat.le_of_lt hlt))
    | none =>
      -- we ran out of bytes
      -- update the content and state and return
      extendContent input index afterEnd
      leavePending .numeralOrDecimal tokenStart offset base afterEnd batch hframe
        (hbatch.mono hindex (Nat.le_of_lt hlt)) (started_lt hts hindex hlt)
        (started_floor hts hframe)
      return Past.from horigin ⟨afterEnd, Nat.le_of_lt hlt, fun _ => hlt⟩
  | .other | .whitespace | .parenOpen | .parenClose | .symbol | .pipe =>
    -- can actually only be other (resulting in unexpected character),
    -- as the other arms have already been handled in the fast path.
    let _ ← startToken offset base index hframe
    leave offset base index batch hframe hbatch
    failAt .unexpectedCharacter after
termination_by input.size - index
decreasing_by all_goals decreasing_position

/- LEAN: Rust's `lex_normal` gets the rest of the slice, whose first byte is at the lexer's
offset. Here `start` is the index of the step, the lexer's `base`; the loop takes its offset
as that of `base` moved on to `start`, so that the proofs know that the indices it reads are
at or after the index of its offset. -/
/-- Lexes from `start`, which is below the size of the slice, in the normal state, returning
the index up to which the slice was consumed, which is after `start`. -/
def lexNormal (input : ByteSlice) (start : Nat) (hstart : start < input.size) :
    LexM H m R E floor low {next : Nat // start < next} := do
  -- use locals for variables commonly used on the fast path
  let ⟨(offset, base, batch), hframe, hbatch, hfloor⟩ ←
    modifyGetThe {c : LexerCore // c.Bound floor low} fun c =>
      ((⟨(c.val.offset, c.val.base, c.val.batch),
          ⟨c.property.1, fun p hp => (c.property.2 p hp).1⟩, c.val.batchEnded,
          fun p hp => (c.property.2 p hp).2.2⟩ :
          {x : Nat × Nat × TokenBatch // Frame floor low x.1 ∧ x.2.2.lastEnd ≤ x.1 ∧
            ∀ p, floor = some p → x.2.2.StartsFrom p}),
        ⟨{ c.val with
            batch := default
            batchEnded := TokenBatch.lastEnd_default ▸ Nat.zero_le _ },
          ⟨c.property.1, fun p hp =>
            ⟨(c.property.2 p hp).1, (c.property.2 p hp).2.1, TokenBatch.startsFrom_default p⟩⟩⟩)
  let offset := offset + (start - base)
  let ⟨next, hnext⟩ ← lexNormalFrom input offset start start batch
    ⟨Nat.le_trans hframe.1 (Nat.le_add_right _ _),
      fun p hp => Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _)⟩ (Nat.le_refl _)
    ⟨by simp only [Nat.sub_self, Nat.add_zero]
        exact Nat.le_trans hbatch (Nat.le_add_right _ _), hfloor⟩ start (Nat.le_refl _)
  return ⟨next, hnext.2 hstart⟩

/- LEAN: each of the following steps lexes the slice from `start`, where Rust's step gets the
rest of the slice; an index that is 0 in Rust is `start` here, and a step returns the
index up to which it has consumed the slice, where Rust returns the number of bytes, with
the proof that it is at or after `start`. Each of them lexes on the token in progress, which
starts at `tokenStart`, before the step's offset; `base` is the index of that offset. -/

def lexFractionFrom (input : ByteSlice) (start : Nat) (tokenStart : Location) (base : Nat)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // start ≤ next} := do
  -- find the first byte in the remainder that is not a digit
  let «end» := runEnd input start RUN_DIGIT
  -- extend the token from slice
  extendContent input start «end»
  if «end» < input.size then
    -- we have successfully consumed the fraction, finish the decimal
    finishDecimal (.mkAtByte «end») (some (get input «end»)) tokenStart base h
    setNormal
  else
    -- we ran out of bytes for now
    setTokenState .fraction tokenStart h
  return ⟨«end», le_runEnd input start _⟩

def lexNumeralOrDecimal (input : ByteSlice) (start : Nat) (tokenStart : Location)
    (base : Nat) (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // start ≤ next} := do
  -- find the first byte that is not a digit
  let index := runEnd input start RUN_DIGIT
  have : start ≤ index := le_runEnd input start _

  -- check that we are not in a leading zero condition
  -- this could not have been done when starting the numeral/decimal
  -- since just a single '0' is allowed

  -- as we emplace the first digit in the normal state,
  -- it suffices for the leading zero condition that
  -- 1. at least one additional digit has been consumed
  -- 2. the content lexed previously is exactly "0"
  let content := (← getCore).tokenContent
  let isZero := content.len == 1 && content.bytes.get! 0 == byte! '0'
  if index > start && isZero then
    failAt .numeralLeadingZero (start + 1)

  -- extend the token from slice
  extendContent input start index

  match get? input index with
  | some next =>
    if next == byte! '.' then
      -- decimal, the next character will start fraction
      -- add the dot and immediately start lexing the fraction after it
      pushContent (byte! '.')
      let ⟨«end», hend⟩ ← lexFractionFrom input (index + 1) tokenStart base h
      return ⟨«end», by omega⟩
    else
      -- we have successfully consumed the numeral, finish it
      expectDelimiter next index
      finishNumeral (.mkAtByte index) tokenStart base h
      -- move back to normal lexer state, not consuming the current byte
      setNormal
      return ⟨index, this⟩
  | none =>
    -- we have run out of bytes for now
    return ⟨index, this⟩

def lexBaseSelection (input : ByteSlice) (start : Nat) (tokenStart : Location)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // start ≤ next} := do
  let c := get input start
  if c == byte! 'x' then
    setTokenState .hexadecimal tokenStart h
  else if c == byte! 'b' then
    setTokenState .binary tokenStart h
  else
    failAt .baseSelectionExpected (start + 1)
  return ⟨start + 1, by omega⟩

/-- Lexes a digit run, either hexadecimal or binary. -/
def lexDigitRun (input : ByteSlice) (start : Nat) (run : DigitRun)
    (hrun : run = HEXADECIMAL_RUN ∨ run = BINARY_RUN) (tokenStart : Location) (base : Nat)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // start ≤ next} := do
  -- find the first byte that is not allowed in the run
  let index := runEnd input start run.flag
  -- extend the token from slice
  extendContent input start index
  if index < input.size then
    -- we have successfully consumed the digit run, finish it
    finishDigitRun run hrun (.mkAtByte index) (some (get input index)) tokenStart base h
    setNormal
  return ⟨index, le_runEnd input start _⟩

/- LEAN: the Rust loops keep the rest of the slice and the number of bytes consumed from it;
here the loops keep the index `consumed` in the slice, so an index in the rest in Rust
is `consumed` plus it here. The loops are shown to end as `lexNormalFrom` is. Where a loop
moves `consumed` on before its run, the index is kept with the proof that it is not
before the one the call started from, which the code after the move is shown to end by. -/

/--
Lexes the string literal in the legacy 2.0 mode.

The legacy 2.0 mode has two backslash escapes, \" and \\.
There are no other escapes.
-/
/- LEAN: `origin` is where the step started, as at `lexWhitespace`. -/
def lexStringLiteralLegacy (input : ByteSlice) (consumed origin : Nat)
    (horigin : origin ≤ consumed) (tokenStart : Location)
    (base : Nat) (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // origin ≤ next} := do
  let some ⟨first, hfirst⟩ := (get? input consumed).attach
    | return ⟨consumed, horigin⟩
  have := lt_size_of_get? hfirst
  let mut consumed : { position : Nat // consumed ≤ position } :=
    ⟨consumed, Nat.le_refl _⟩
  match (← getCore).state with
  | .stringLiteralDoubleQuote =>
    -- expect a delimiter and finish the previously ended token
    expectDelimiter first consumed
    finishStringLiteral (.mkAtByte consumed) tokenStart base h
    -- set lexer to normal state and return, not consuming the current byte
    setNormal
    return ⟨consumed.1, Nat.le_trans horigin consumed.2⟩
  | .stringLiteralBackslashEscape =>
    -- handle the backslash escape
    if first == byte! '"' || first == byte! '\\' then
      -- a backslash escape: only the escaped byte belongs to the content
      pushContent first
      consumed := ⟨consumed.1 + 1, by simp +zetaDelta only; omega⟩
    else
      -- not a backslash escape: the backslash belongs to the content,
      -- and the byte after it is lexed like any other
      pushContent (byte! '\\')
    -- continue parsing the string literal
    setTokenState .stringLiteral tokenStart h
  | _ => pure ()

  -- find the first byte that does not belong to string nor quoted
  -- this means backslash and pipe end the run as well, so we can act on them
  let index := runEndAll input consumed (RUN_STRING_PLAIN ||| RUN_QUOTED_PLAIN)
  have : consumed.1 ≤ index := le_runEndAll input _ _
  have := consumed.2

  let some ⟨c, hc⟩ := (get? input index).attach
    | do
      -- extend the content with the rest
      extendContent input consumed input.size
      -- we have nothing more to consume, return
      return ⟨input.size, by omega⟩

  let addRunEnding ←
    if c == byte! '\n' then do
      -- mark the line feed
      markLineFeedAt index
      -- it belongs to the string, add it and continue lexing
      pure true
    else if c == byte! '"' then do
      -- put the lexer in the double-quote state
      -- do not add the quote, it is not part of the content
      setTokenState .stringLiteralDoubleQuote tokenStart h
      pure false
    else if c == byte! '\\' then do
      -- put the lexer in the backslash-escape state
      -- do not add the backslash yet
      -- it may or may not be part of the content
      -- depending on if it truly is a backslash escape or not
      setTokenState .stringLiteralBackslashEscape tokenStart h
      pure false
    else if c == byte! '|' then do
      -- pipe belongs to the string, add it and continue lexing
      pure true
    else
      -- forbidden character
      failAt .forbiddenCharInString (index + 1)

  -- extend the content with bytes before the run-ending byte
  extendContent input consumed index
  if addRunEnding then
    -- add the byte to the content
    pushContent c
  -- consume the run-ending byte and everything before it
  have := lt_size_of_get? hc
  lexStringLiteralLegacy input (index + 1) origin (by simp +zetaDelta only at *; omega)
    tokenStart base h
termination_by input.size - consumed
decreasing_by decreasing_position

/-- Lexes the string literal. -/
def lexStringLiteralFrom (input : ByteSlice) (consumed origin : Nat)
    (horigin : origin ≤ consumed) (tokenStart : Location)
    (base : Nat) (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // origin ≤ next} := do
  let some ⟨first, hfirst⟩ := (get? input consumed).attach
    | return ⟨consumed, horigin⟩
  have := lt_size_of_get? hfirst
  let mut consumed : { position : Nat // consumed ≤ position } :=
    ⟨consumed, Nat.le_refl _⟩
  if (← getCore).state == .stringLiteralDoubleQuote then
    -- we need to react to the literal being closed by a previous double-quote
    -- look at the first byte
    if first != byte! '"' then
      -- the previous character was really a quote ending the string literal
      -- finish the previously ended token
      expectDelimiter first consumed
      finishStringLiteral (.mkAtByte consumed) tokenStart base h
      -- set lexer to normal state and return, not consuming the current byte
      setNormal
      return ⟨consumed.1, Nat.le_trans horigin consumed.2⟩
    else
      -- this has been a double-quote escape
      -- consume the first byte
      consumed := ⟨consumed.1 + 1, by simp +zetaDelta only; omega⟩
      -- push a double-quote byte (just one, we encountered two)
      pushContent (byte! '"')
      -- return to string-literal state and continue lexing
      setTokenState .stringLiteral tokenStart h

  -- find the first byte that is not a plain string byte
  let index := runEnd input consumed RUN_STRING_PLAIN
  have : consumed.1 ≤ index := le_runEnd input _ _
  have := consumed.2

  match hc : get? input index with
  | some c =>
    have := lt_size_of_get? hc
    if c == byte! '\n' then
      -- mark the line feed
      markLineFeedAt index
      -- extend with & consume the run including the line feed
      extendContent input consumed (index + 1)
      -- continue lexing
      lexStringLiteralFrom input (index + 1) origin (by simp +zetaDelta only at *; omega)
        tokenStart base h
    else if c == byte! '"' then
      -- we have a double quote in string literal
      -- only extend the content with bytes before it
      extendContent input consumed index
      -- the quote may be followed by another double quote for escaping
      -- otherwise, it will end the string literal
      -- put the lexer in a special state to handle the next character
      setTokenState .stringLiteralDoubleQuote tokenStart h
      -- consume the quote and everything before it, continue lexing
      lexStringLiteralFrom input (index + 1) origin (by simp +zetaDelta only at *; omega)
        tokenStart base h
    else
      -- forbidden, not printable or whitespace
      failAt .forbiddenCharInString (index + 1)
  | none =>
    -- extend the content with the rest
    extendContent input consumed input.size
    -- we have nothing more to consume, return
    return ⟨input.size, by omega⟩
termination_by input.size - consumed
decreasing_by all_goals decreasing_position

/-- Lexes the string literal. -/
def lexStringLiteral (input : ByteSlice) (start : Nat) (tokenStart : Location) (base : Nat)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // start ≤ next} := do
  if (← getCore).version == .v2_0 then
    -- in 2.0 mode, the string literals are lexed differently,
    -- hand over to the legacy lexing function
    lexStringLiteralLegacy input start start (Nat.le_refl _) tokenStart base h
  else
    lexStringLiteralFrom input start start (Nat.le_refl _) tokenStart base h

def lexSimpleSymbol (input : ByteSlice) (start : Nat) (tokenStart : Location) (base : Nat)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // start ≤ next} := do
  -- find the first byte that is not a simple symbol
  let index := runEnd input start RUN_SIMPLE_SYMBOL
  -- extend the token from slice
  extendContent input start index
  if index < input.size then
    -- we have successfully consumed the symbol, finish it
    expectDelimiter (get input index) index
    finishSimpleSymbol (.mkAtByte index) tokenStart base h
    setNormal
  return ⟨index, le_runEnd input start _⟩

/- LEAN: `origin` is where the step started, as at `lexWhitespace`. -/
def lexQuotedSymbol (input : ByteSlice) (consumed origin : Nat)
    (horigin : origin ≤ consumed)
    (hconsumed : consumed ≤ input.size) (tokenStart : Location)
    (base : Nat) (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // origin ≤ next} := do
  -- find the first byte that is not a quoted symbol
  let index := runEnd input consumed RUN_QUOTED_PLAIN
  have : consumed ≤ index := le_runEnd input _ _

  -- inspect the problematic byte
  match hc : get? input index with
  | some c =>
    have := lt_size_of_get? hc
    let afterSlicePosition := index + 1
    if c == byte! '|' then
      -- end of quoted symbol, extend its content
      extendContent input consumed index
      -- the byte after the pipe must delimit the token before it is sunk
      match get? input afterSlicePosition with
      | some next =>
        expectDelimiter next afterSlicePosition
        sinkStored .quotedSymbol nofun (.mkAtByte afterSlicePosition) tokenStart base h
        setNormal
      | none =>
        -- we do not have the next byte available,
        -- move to the state expecting it to be a delimiter
        setTokenState .quotedSymbolClosed tokenStart h
      -- consume the bytes including the pipe
      return ⟨afterSlicePosition, by simp +zetaDelta only at *; omega⟩
    else if c == byte! '\\' then
      -- backslash is forbidden in quoted symbols
      failAt .backslashInQuotedSymbol afterSlicePosition
    else if c == byte! '\n' then
      -- mark the line feed at the given position
      markLineFeedAt index
      -- prepare for the next run
      -- move everything including this LF to token content
      extendContent input consumed afterSlicePosition
      lexQuotedSymbol input afterSlicePosition origin (by simp +zetaDelta only at *; omega)
        (by simp +zetaDelta only at *; omega) tokenStart base h
    else
      -- forbidden character
      failAt .forbiddenCharInQuotedSymbol afterSlicePosition
  | none =>
    -- we ran out of bytes before the token ended
    -- extend content and keep the quoted symbol state
    extendContent input consumed input.size
    return ⟨input.size, Nat.le_trans horigin hconsumed⟩
termination_by input.size - consumed
decreasing_by decreasing_position

def lexKeyword (input : ByteSlice) (start : Nat) (tokenStart : Location) (base : Nat)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // start ≤ next} := do
  -- find the first byte that is not simple-symbol-like
  let index := runEnd input start RUN_SIMPLE_SYMBOL

  -- extend the token from slice
  extendContent input start index

  if index < input.size then
    -- we have successfully consumed the keyword, finish it
    finishKeyword (.mkAtByte index) (some (get input index)) tokenStart base h
    setNormal
  return ⟨index, le_runEnd input start _⟩

def lexQuotedSymbolClosed (input : ByteSlice) (start : Nat) (tokenStart : Location)
    (base : Nat) (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // start ≤ next} := do
  -- we expect a token delimiter to follow the closing pipe
  expectDelimiter (get input start) start
  -- all good, produce the quoted symbol token
  sinkStored .quotedSymbol nofun (.mkAtByte start) tokenStart base h
  -- the delimiter is not consumed
  setNormal
  return ⟨start, Nat.le_refl _⟩

/- LEAN: the loop of `lex_whitespace` is the recursion on `start`, shown to end as
`lexNormalFrom` is. `origin` is where the step started, which the index returned is at or
after; it stays the same while the loop runs, so that the recursive call is the last one. -/
def lexWhitespace (input : ByteSlice) (start origin : Nat)
    (horigin : origin ≤ start)
    (hstart : start ≤ input.size) (tokenStart : Location) (base : Nat)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // origin ≤ next} := do
  -- we know that the consumer is interested in the whitespace
  -- as it would otherwise be immediately discarded instead
  -- of the state change
  -- find the first byte that is not non-LF whitespace
  let index := runEnd input start RUN_NON_LF_WHITESPACE
  have : start ≤ index := le_runEnd input _ _
  -- inspect the problematic byte
  match hc : get? input index with
  | some c =>
    have := lt_size_of_get? hc
    if c == byte! '\n' then
      -- mark the line feed at the given position
      markLineFeedAt index
      -- prepare for the next run
      -- extend the token content with everything including this LF
      extendContent input start (index + 1)
      lexWhitespace input (index + 1) origin (by omega) (by omega) tokenStart base h
    else
      -- end of whitespace
      -- extend and finish the token
      extendContent input start index
      finishWhitespace (.mkAtByte index) tokenStart base h
      -- go back to normal state, consuming the whitespace
      setNormal
      return ⟨index, by omega⟩
  | none =>
    -- we ran out of bytes before the token ended
    -- extend the token content with everything
    -- keep the whitespace state
    extendContent input start input.size
    return ⟨input.size, by omega⟩
termination_by input.size - start
decreasing_by decreasing_position

def lexComment (input : ByteSlice) (start : Nat) (hstart : start ≤ input.size)
    (tokenStart : Location) (base : Nat) (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // start ≤ next} := do
  -- run until comment end
  let index := runEnd input start RUN_COMMENT_PLAIN
  have : start ≤ index := le_runEnd input _ _
  match hc : get? input index with
  | none =>
    -- the comment continues; if we are producing comments,
    -- extend the content from the whole slice
    if ← consumesWhitespaceAndComments then
      extendContent input start input.size
    -- remain in comment state
    return ⟨input.size, hstart⟩
  | some c =>

  -- the comment has ended, either by CR or LF
  -- if it ended by LF, we must mark it
  if c == byte! '\n' then
    markLineFeedAt index

  let afterCommentEnd := index + 1

  if ← consumesWhitespaceAndComments then
    -- we need to produce the comment token
    -- extend the comment content and finish the token
    extendContent input start afterCommentEnd
    sinkStored .comment nofun (.mkAtByte afterCommentEnd) tokenStart base h

  -- move back to the normal state and return
  setNormal
  return ⟨afterCommentEnd, by simp +zetaDelta only at *; omega⟩

/- LEAN: the step that finishes a token waiting for its delimiter consumes nothing: the
delimiter is the first byte of the next token. Rust's loop then makes its next pass with the
same rest of the slice, in the normal state, and so calls `lex_normal` on it; here the step
calls `lexNormal` at once instead, with the same arguments and the lexer in the same state,
which hands over the same tokens. So every step consumes at least one byte or is interrupted,
which the loop over the slice is shown to end by. A step consumes nothing only after it
finished a token, so the lexer is then in the normal state. -/
/-- Goes on with `lexNormal` at `start` if the step returned `start`, having consumed nothing. -/
@[inline]
def afterStep (input : ByteSlice) (start : Nat) (hstart : start < input.size)
    (next : {next : Nat // start ≤ next}) :
    LexM H m R E floor low {next : Nat // start < next} :=
  if h : start < next.1 then pure ⟨next.1, h⟩ else lexNormal input start hstart

/- LEAN: Rust's step reads the state from the lexer; here the state, the token start and the
index of the lexer's offset are given, as the loop over the slice read them, with what the
lexer state says of them. -/
/--
Lexes the slice from `start`, which is below its size, in the state, returning the index up
to which the slice was consumed, which is after `start`.
-/
def lexStep (input : ByteSlice) (start : Nat) (hstart : start < input.size)
    (state : LexerState) (tokenStart : Location) (base : Nat)
    (hpending : state = .normal ∨ Started floor low tokenStart) :
    LexM H m R E floor low {next : Nat // start < next} := do
  match state, hpending with
  | .normal, _ => lexNormal input start hstart
  | .numeralOrDecimal, h =>
    afterStep input start hstart
      (← lexNumeralOrDecimal input start tokenStart base (h.resolve_left nofun))
  | .fraction, h =>
    afterStep input start hstart
      (← lexFractionFrom input start tokenStart base (h.resolve_left nofun))
  | .baseSelection, h =>
    afterStep input start hstart
      (← lexBaseSelection input start tokenStart (h.resolve_left nofun))
  | .hexadecimal, h =>
    afterStep input start hstart
      (← lexDigitRun input start HEXADECIMAL_RUN (.inl rfl) tokenStart base
        (h.resolve_left nofun))
  | .binary, h =>
    afterStep input start hstart
      (← lexDigitRun input start BINARY_RUN (.inr rfl) tokenStart base
        (h.resolve_left nofun))
  | .stringLiteral, h | .stringLiteralDoubleQuote, h | .stringLiteralBackslashEscape, h =>
    afterStep input start hstart
      (← lexStringLiteral input start tokenStart base (h.resolve_left nofun))
  | .simpleSymbol, h =>
    afterStep input start hstart
      (← lexSimpleSymbol input start tokenStart base (h.resolve_left nofun))
  | .quotedSymbol, h =>
    afterStep input start hstart
      (← lexQuotedSymbol input start start (Nat.le_refl _) (Nat.le_of_lt hstart) tokenStart base
        (h.resolve_left nofun))
  | .keyword, h =>
    afterStep input start hstart
      (← lexKeyword input start tokenStart base (h.resolve_left nofun))
  | .comment, h =>
    afterStep input start hstart
      (← lexComment input start (Nat.le_of_lt hstart) tokenStart base
        (h.resolve_left nofun))
  | .whitespace, h =>
    afterStep input start hstart
      (← lexWhitespace input start start (Nat.le_refl _) (Nat.le_of_lt hstart) tokenStart base
        (h.resolve_left nofun))
  | .quotedSymbolClosed, h =>
    afterStep input start hstart
      (← lexQuotedSymbolClosed input start tokenStart base (h.resolve_left nofun))

/-- How lexing a slice from an index ends. -/
inductive SliceExit (R E : Type) (floor : Option Nat) where
  /-- The batch was handed over: the result to return. -/
  | done (result : Except (Failure E) (ControlFlow R))
  /-- The consumer stopped at the location, which is after the floor. -/
  | stopped (stop : Stop R) (location : Location)
    (after : ∀ p, floor = some p → p < location.offset)

/- LEAN: the loop of `lex_slice_inner`, up to the first stop of the consumer, which the loop
below acts on. `position` is where the part of the slice not lexed yet starts, the lexer's
base, and `fnResult` the result to return once the batch is handed over. The lexer state is
passed along by hand, with the floor (see `Interrupted`). The loop ends as every step consumes a
byte (see `lexStep`), and a lexical error is met at most once before the batch is handed over:
then the loop flushes, and a flush either ends the loop or stops it. -/
def lexSliceRun (input : ByteSlice) (position : Nat)
    (fnResult : Except (Failure E) (ControlFlow R)) (core : {c : LexerCore // c.Bound floor 0}) :
    StateT H m (SliceExit R E floor × {c : LexerCore // c.Bound floor 0}) := do
  let failed := match fnResult with
    | .error _ => true
    | .ok _ => false
  if hflush : position ≥ input.size || failed then
    -- hand over the batch
    let (flushed, core) ← (flushBatch (m := m) (R := R) (E := E)).run.run core
    match flushed with
    | .ok () =>
      -- we are done
      return (.done fnResult, core)
    | .error interrupted =>
      match interrupted with
      | { result := .ok stop, location, stopAfter } =>
        return (.stopped stop location fun p hp => stopAfter p hp stop rfl, core)
      | { result := .error cause, location, .. } =>
        /- LEAN: Rust's loop makes another pass, which hands over the batch, empty now; here
        the error is returned at once. -/
        return (.done (.error { cause, location }), core)
  else
    have hposition : position < input.size := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hflush
      omega
    let offset := core.val.offset
    -- a token in progress starts before the offset, which is then after the floor
    have hpending : core.val.state = .normal ∨ Started floor offset core.val.tokenStart := by
      by_cases hnormal : core.val.state = .normal
      · exact .inl hnormal
      · have h := core.val.tokenStarted.resolve_left hnormal
        exact .inr ⟨h, fun p hp => ((core.property.2 p hp).2.1.resolve_left hnormal).elim
          (fun hle => Nat.lt_of_le_of_lt hle h) id⟩
    let step := lexStep (low := offset) input position hposition core.val.state core.val.tokenStart
      core.val.base hpending
    let (stepped, core) ← step.run.run ⟨core.val, ⟨Nat.le_refl _, core.property.2⟩⟩
    let core : {c : LexerCore // c.Bound floor 0} := ⟨core.val, core.property.weaken⟩
    match stepped with
    | .ok ⟨next, hnext⟩ =>
      -- advance the offset by the number of consumed bytes
      -- the line positions are updated by the arm functions above
      -- move after consumed bytes, continue consuming
      lexSliceRun input next fnResult ⟨core.val.advance next, core.property.advance next⟩
    | .error interrupted =>
      match interrupted with
      | { result := .ok stop, location, stopAfter } =>
        return (.stopped stop location fun p hp => stopAfter p hp stop rfl, core)
      | { result := .error cause, location, .. } =>
        -- make sure the tokens before the error get handed over
        lexSliceRun input position (.error { cause, location }) core
termination_by (input.size - position, match fnResult with | .ok _ => 1 | .error _ => 0)
decreasing_by
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    cases fnResult <;> simp_all +zetaDelta

/- LEAN: the loop over the stops of the consumer in the slice. Every stop goes back to the end
of a token the consumer took, which is after the floor (see `Interrupted`): at or after the
start of the slice, and after the last relex in the slice, so that the loop ends. `floor` is
the offset before the first byte of the slice at first, and the location of the last relex
after it; the lexer state is passed along by hand, and the other arguments are those of
`lexSliceRun`. -/
def lexSliceFrom (input : ByteSlice) (initialOffset : Nat) (floor : Nat)
    (hfloor : initialOffset ≤ floor + 1) (position : Nat)
    (fnResult : Except (Failure E) (ControlFlow R))
    (core : {c : LexerCore // c.Bound (some floor) 0}) :
    StateT H m (Except (Failure E) (ControlFlow R) × LexerCore) := do
  let (exit, core) ← lexSliceRun input position fnResult core
  match exit with
  | .done result => return (result, core.val)
  | .stopped stop location after =>
    -- every handed-over token ends in this slice
    -- so the location is at or after the initial offset
    have hlocation : initialOffset ≤ location.offset := by
      have := after floor rfl
      omega
    let resumed := location.offset - initialOffset
    let core := core.val.resumeAt location resumed
    match stop with
    | .relex =>
      if hresumed : resumed < input.size then
        -- everything up to the index was already consumed
        -- continue from there
        lexSliceFrom input initialOffset location.offset (Nat.le_succ_of_le hlocation)
          resumed (.ok .continue) ⟨core, core.bound_resumeAt location resumed⟩
      else
        /- LEAN: the location is at the end of the slice, where Rust's loop ends, as no bytes
        are left; the batch was handed over. -/
        return (.ok .continue, core)
    | .finished result =>
      -- the consumer is done: the batch was handed over,
      -- the rest of the slice stays unlexed
      -- the lexer discards it and everything fed until the end of the input
      return (.ok (.break result), core)
termination_by input.size + 1 - (floor + 1 - initialOffset)
decreasing_by
  have := after floor rfl
  omega

def lexSliceInner (input : ByteSlice) :
    InnerM H m (Except (Failure E) (ControlFlow R)) := fun c =>
  let initialOffset := c.offset
  -- the slice starts at the lexer's offset,
  -- and the tokens borrowed from it have their contents in its array
  /- LEAN: the batch starts empty, as Rust's, which is a local of the call, does; it is empty
  already, as lexing returns with it handed over. -/
  let batch := c.batch
  let c := { c with batch := default, batchEnded := TokenBatch.lastEnd_default ▸ Nat.zero_le _ }
  let c : LexerCore := { c with
    base := 0, batch := { batch.clear initialOffset with bytes := input.byteArray }
    batchEnded := Nat.le_of_eq (TokenBatch.lastEnd_clear _ _) }
  -- the floor is just before the slice, and every token handed over ends after it: one begun in
  -- an earlier slice ends at the slice's start or later, one begun in this slice ends after its
  -- first byte. At offset 0 the floor is 0, as `Nat` subtraction stops there; no token begins
  -- earlier, and one begun here ends above 0. A token in progress starts before the offset.
  have hpending :
      c.state = .normal ∨ initialOffset - 1 ≤ c.tokenStart.offset ∨ initialOffset - 1 < c.offset :=
    c.tokenStarted.imp_right fun h => .inr (Nat.sub_one_lt_of_lt h)
  lexSliceFrom input initialOffset (initialOffset - 1) (by omega) 0 (.ok .continue)
    ⟨c, ⟨Nat.zero_le _, fun p hp => by
      cases hp
      exact ⟨Nat.sub_le _ _, hpending, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩⟩

/-- Resets the lexer to the initial state, including the location and version. -/
def reset : InnerM H m Unit :=
  modifyThe LexerCore fun c =>
    { c with
      version := c.initialVersion
      state := .normal
      discard := false
      consumedDepth := 0
      lexedDepth := 0
      recoveryState := none
      tokenStart := Location.initial
      tokenContent := c.tokenContent.clear
      offset := 0
      line := 0
      base := 0
      lineStart := 0
      /- LEAN: not in Rust: the batch, which was handed over, is empty already; its origin
      is set to the offset. -/
      batch := c.batch.clear 0
      tokenStarted := .inl rfl
      batchEnded := Nat.le_of_eq (TokenBatch.lastEnd_clear _ _) }

/- LEAN: the pending token is finished as a step does: it starts before the lexer's offset,
which is that of the index 0 at the end of the input. -/
def lexEofInner : InnerM H m (Except (Failure E) (ControlFlow R)) := fun c => do
  -- EOF is a token delimiter, we need to produce the token
  -- that waits for a delimiter if there is any
  -- there is no input at the end of the file, indices are relative to the offset
  let c := { c with base := 0 }
  let tokenStart := c.tokenStart
  let offset := c.offset
  let pending : LexM H m R E none offset Unit :=
    match c.state, c.tokenStarted with
    | .normal, _ =>
      -- nothing to do
      pure ()
    | .quotedSymbolClosed, h =>
      -- the end of the input is a token delimiter,
      -- produce the quoted symbol
      sinkStored .quotedSymbol nofun TokenEnd.EOF tokenStart 0
        ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .fraction, h =>
      finishDecimal TokenEnd.EOF none tokenStart 0 ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .numeralOrDecimal, h =>
      finishNumeral TokenEnd.EOF tokenStart 0 ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .hexadecimal, h =>
      finishDigitRun HEXADECIMAL_RUN (.inl rfl) TokenEnd.EOF none tokenStart 0
        ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .binary, h =>
      finishDigitRun BINARY_RUN (.inr rfl) TokenEnd.EOF none tokenStart 0
        ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .baseSelection, _ =>
      -- hash without selection following it
      fail .baseSelectionExpected TokenEnd.EOF
    | .stringLiteral, _ | .stringLiteralBackslashEscape, _ =>
      -- we are still within the string literal
      -- forbidden as the literal must be totally enclosed by double quotes
      fail .unclosedStringLiteral TokenEnd.EOF
    | .stringLiteralDoubleQuote, h =>
      -- string literal has ended by the previous character,
      -- a quote directly before the end of the file
      -- this works both for 2.0 and 2.5+
      finishStringLiteral TokenEnd.EOF tokenStart 0 ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .simpleSymbol, h =>
      finishSimpleSymbol TokenEnd.EOF tokenStart 0 ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .keyword, h =>
      finishKeyword TokenEnd.EOF none tokenStart 0 ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .quotedSymbol, _ =>
      -- EOF forbidden as the symbol must be totally enclosed by pipes
      fail .unclosedQuotedSymbol TokenEnd.EOF
    | .whitespace, h =>
      -- we can only be in this state if the consumer wants the
      -- whitespace to be emitted, so sink it
      sinkStored .whitespace nofun TokenEnd.EOF tokenStart 0
        ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .comment, h => do
      -- only produce the comment if the consumer wants it
      if ← consumesWhitespaceAndComments then
        sinkStored .comment nofun TokenEnd.EOF tokenStart 0
          ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
  let step : LexM H m R E none offset Unit := do
    -- if we were told to relex, treat it as a normal continuation,
    -- as there is nothing to relex (we are at the end of input)
    tryCatch pending fun interrupted =>
      match interrupted.result with
      | .ok .relex => pure ()
      | _ => throw interrupted
    -- everything has been processed, start the EOF token and sink it
    let ⟨location, _⟩ ← startToken offset 0 0 ⟨Nat.le_refl _, fun _ h => nomatch h⟩
    handOverEof location

  let (result, core) ← step.run.run ⟨c, ⟨Nat.le_refl _, fun _ h => nomatch h⟩⟩
  match result with
  | .ok () =>
    -- everything processed, there was no break out
    -- the lexer will be reset outside, just continue
    return (.ok .continue, core.val)
  | .error interrupted =>
    match interrupted.result with
    | .error cause => return (.error { cause, location := interrupted.location }, core.val)
    | .ok .relex =>
      -- we were asked to relex, but the file is ending anyway, nothing to relex
      return (.ok .continue, core.val)
    | .ok (.finished result) =>
      -- the consumer is done with the input
      -- the lexer will be reset outside
      return (.ok (.break result), core.val)

/-- Executes an inner lexer step, adding the break location to its result. -/
def executeStep (step : InnerM H m (Except (Failure E) (ControlFlow R))) :
    InnerM H m (Except (Failure E) (ControlFlow (Located R))) := do
  match ← step with
  | .ok .continue => return .ok .continue
  | .ok (.break result) =>
    -- add the break location: the lexer is at the last consumed token
    let location := (← getThe LexerCore).currentLocation
    return .ok (.break { value := result, location })
  | .error failure => return .error failure

/- LEAN: a lexer that stops at its first error is not given back by a call that fails, so it
needs no failure mode to refuse further calls, unlike Rust. -/
/--
Turns the failure into the error to return.

A recovering lexer makes the consumer abandon its current work and skips bytes until
recovery is made.
-/
def failCall (abandon : Location → StateT H m Unit) (failure : Failure E) (atEnd : Bool) :
    InnerM H m (LexError E) := do
  if !(← getThe LexerCore).recovers then
    return { cause := failure.cause, continuesFrom := none }

  let skip : RecoveryState := if atEnd then
      -- the input has ended, nothing is left to skip
      .end
    else
      -- start recovering from inside the string or quoted symbol if necessary
      match failure.cause with
      | .lexical err => match err.kind with
        | .forbiddenCharInString => .string
        | .backslashInQuotedSymbol | .forbiddenCharInQuotedSymbol => .quotedSymbol
        | _ => .plain
      -- the consumer fails at the boundary after a whole token
      | .consumer _ => .boundary

  -- start recovering from the given failure location
  -- there is no slice being lexed, so its index is zero
  modifyThe LexerCore (·.resumeAt failure.location 0)
  abandon failure.location
  modifyThe LexerCore fun c => { c with recoveryState := some skip }
  return { cause := failure.cause, continuesFrom := some failure.location }

/-- What skipping goes through, see `skipBytes`. -/
structure Skipping where
  skip : RecoveryState
  depth : Nat
  line : Nat
  lineStart : Nat

/- LEAN: the loop of Rust's `skip_slice` over the bytes, as a recursion on `index` that is shown
to end; it works on the values it changes and leaves the lexer state to `skipSlice`.
`offset` is the stream offset of the first byte. -/
/--
Skips the bytes from `index` on while recovering.

Returns the index where the recovery was made, if it was, and the skipping state there
or at the end of the bytes.
-/
def skipBytes (bytes : ByteSlice) (legacy : Bool) (offset index : Nat)
    (skipping : Skipping) : Option Nat × Skipping :=
  if h : index < bytes.size then
    let c := bytes[index]
    -- the state after the byte, or the index where the recovery was made
    let next : Sum (Nat × Skipping) Skipping := match skipping.skip with
      | .end | .boundary | .plain =>
        if c == byte! '"' then .inr { skipping with skip := .string }
        else if c == byte! '|' then .inr { skipping with skip := .quotedSymbol }
        else if isDelimiter c && skipping.depth == 0 then
          -- delimits the error end while nothing is open, we have recovered
          .inl (index, skipping)
        else if c == byte! ';' then .inr { skipping with skip := .comment }
        else if c == byte! '(' then
          .inr { skipping with skip := .plain, depth := skipping.depth + 1 }
        else if c == byte! ')' then
          -- depth must be nonzero here as zero depth would have ended recovery
          let depth := skipping.depth - 1
          if depth == 0 then
            -- recover after the closing parenthesis
            .inl (index + 1, { skipping with depth })
          else
            .inr { skipping with skip := .plain, depth }
        else .inr { skipping with skip := .plain }
      | .string =>
        if c == byte! '"' then .inr { skipping with skip := .plain }
        -- in the legacy 2.0 mode, a backslash escapes the byte after it
        else if c == byte! '\\' && legacy then .inr { skipping with skip := .stringEscape }
        else .inr skipping
      | .stringEscape => .inr { skipping with skip := .string }
      | .quotedSymbol =>
        if c == byte! '|' then .inr { skipping with skip := .plain } else .inr skipping
      | .comment =>
        if c == byte! '\n' || c == byte! '\r' then .inr { skipping with skip := .plain }
        else .inr skipping
    match next with
    | .inl (position, skipping) => (some position, skipping)
    | .inr skipping =>
      -- the line feed was skipped, it must be marked for line offsets
      let skipping := if c == byte! '\n' then
          { skipping with line := skipping.line + 1, lineStart := offset + index + 1 }
        else skipping
      skipBytes bytes legacy offset (index + 1) skipping
  else
    (none, skipping)
termination_by bytes.size - index

/--
Skips the input while recovering.

Returns the index in the slice where the recovery was made,
or returns `none` if it has not yet been done.
-/
def skipSlice (slice : ByteSlice) (skip : RecoveryState) : InnerM H m (Option Nat) := do
  let c ← getThe LexerCore
  if skip == .boundary && c.consumedDepth == 0 then
    -- the consumer failed after a whole value, no recovery needed
    return some 0
  -- at a boundary, we are still at some depth and need to recover
  let skip := if skip == .boundary then .plain else skip

  let legacy := c.version == .v2_0
  let skipping := { skip, depth := c.consumedDepth, line := c.line, lineStart := c.lineStart }
  match skipBytes slice legacy c.offset 0 skipping with
  | (some position, skipping) =>
    set { c with
      offset := c.offset + position
      consumedDepth := skipping.depth
      line := skipping.line
      lineStart := skipping.lineStart
      tokenStarted := c.tokenStarted.imp_right fun h => Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
      batchEnded := Nat.le_trans c.batchEnded (Nat.le_add_right _ _) }
    return some position
  | (none, skipping) =>
    -- we ran out of bytes, update the offset and what is being skipped
    set { c with
      offset := c.offset + slice.size
      consumedDepth := skipping.depth
      line := skipping.line
      lineStart := skipping.lineStart
      recoveryState := some skipping.skip
      tokenStarted := c.tokenStarted.imp_right fun h => Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
      batchEnded := Nat.le_trans c.batchEnded (Nat.le_add_right _ _) }
    return none

/- LEAN: Rust finds the last line feed with `rposition` and counts the line feeds in a second
pass; here one pass does both. -/
/-- The number of line feeds in the bytes, and the index after the last one, if any. -/
def countLineFeeds (bytes : ByteSlice) : Nat × Option Nat :=
  let rec loop (i count : Nat) (afterLast : Option Nat) : Nat × Option Nat :=
    if h : i < bytes.size then
      if bytes[i] == byte! '\n' then loop (i + 1) (count + 1) (some (i + 1))
      else loop (i + 1) count afterLast
    else
      (count, afterLast)
  termination_by bytes.size - i
  loop 0 0 none

/-- Discards the bytes while keeping the location correct. -/
def discardBytes (bytes : ByteSlice) : InnerM H m Unit :=
  -- the line feeds must be counted for the location to stay correct
  -- if there is a line feed, the line starts after the last one
  modifyThe LexerCore fun c =>
    let c := match countLineFeeds bytes with
      | (lineFeeds, some afterLast) =>
        { c with line := c.line + lineFeeds, lineStart := c.offset + afterLast }
      | (_, none) => c
    { c with
      offset := c.offset + bytes.size
      tokenStarted := c.tokenStarted.imp_right fun h => Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
      batchEnded := Nat.le_trans c.batchEnded (Nat.le_add_right _ _) }

/- LEAN: the consumer's recovery methods are passed in, those of `LexRecovery`; they are only
called by a recovering lexer. -/
/-- Lexes the slice, or discards it if the consumer has finished. -/
def lexSliceStep (abandon recover : Location → StateT H m Unit) (slice : ByteSlice) :
    InnerM H m (Except (LexError E) (ControlFlow (Located R))) := do
  if (← getThe LexerCore).discard then
    -- we are discarding bytes
    -- pretend that we lexed everything we were given
    discardBytes slice
    return .ok .continue

  -- a recovering lexer must skip until out of the root-level expression
  -- in which the error occurred
  let mut slice := slice
  if let some skip := (← getThe LexerCore).recoveryState then
    /- LEAN: Rust panics if the slice is not empty, as the end of the input raised the error.
    Only a `PendingEof` holds a lexer in this state, and it offers no `lexSlice`. -/
    if skip == .end then
      -- the input has ended, there is nothing to skip to
      return .ok .continue
    let some skipped ← skipSlice slice skip
      -- the whole slice was skipped
      | return .ok .continue
    -- the lexing goes on from here, tell the consumer before any token
    modifyThe LexerCore fun c => { c with recoveryState := none, lexedDepth := c.consumedDepth }
    recover (← getThe LexerCore).currentLocation
    slice := slice.slice skipped

  let start := (← getThe LexerCore).offset
  -- call inner lexing and fail on error
  let result ← executeStep (lexSliceInner slice)
  match result with
  | .error failure => return .error (← failCall abandon failure false)
  | .ok flow =>
    -- if the consumer has produced a result, remember to stop feeding it
    if let .break located := flow then
      modifyThe LexerCore fun c => { c with discard := true }
      -- discard the remaining bytes after break
      discardBytes (slice.slice (located.location.offset - start))
    return .ok flow

/-- Lexes the end of the input, which resets the lexer unless it fails and recovers. -/
def lexEofStep (abandon recover : Location → StateT H m Unit) :
    InnerM H m (Except (LexError E) (ControlFlow (Located R))) := do
  if (← getThe LexerCore).discard then
    -- no need to feed anything, just reset the lexer
    reset
    return .ok .continue

  -- the end of the input forces recovery
  let recovered := (← getThe LexerCore).recoveryState.isSome
  if recovered then
    modifyThe LexerCore fun c => { c with recoveryState := none }
    recover (← getThe LexerCore).currentLocation

  -- call inner EOF lexing
  match ← executeStep lexEofInner with
  | .ok flow =>
    -- the input has ended, reset the lexer
    reset
    return .ok flow
  | .error failure =>
    if recovered then
      -- the consumer has refused the EOF token with nothing left to abandon:
      -- the error is final and the input has ended, reset the lexer
      reset
      return .error { cause := failure.cause, continuesFrom := none }
    return .error (← failCall abandon failure true)

end

namespace Lexer

/--
Constructs the lexer.

The lexer stops at its first error.
-/
def new (consumer : H) (version : Version) : Lexer H :=
  { handler := consumer,
    core := {
      version
      initialVersion := version
      state := .normal
      discard := false
      recovers := false
      consumedDepth := 0
      lexedDepth := 0
      recoveryState := none
      tokenStart := Location.initial
      tokenContent := ContentBuffer.empty
      offset := 0
      base := 0
      line := 0
      lineStart := 0
      batch := TokenBatch.empty BATCH_CAPACITY
      tokenStarted := .inl rfl
      batchEnded := Nat.zero_le _ } }

/- LEAN: Rust requires the consumer to recover by the bound `C: SmtRecover`; here by the
instance argument, which the construction itself does not use. -/
/-- Constructs a lexer that recovers from errors. -/
def newRecovering [Recover H m] (consumer : H) (version : Version) : Lexer H .recovering :=
  let { handler, core } := new consumer version
  { handler, core := { core with recovers := true } }

def currentLocation (self : Lexer H recovery) : Location :=
  self.core.currentLocation

/--
The SMT-LIB version currently in force.

The version can change if the token consumer asks for it from the
cursor. The end of the input resets the version to the initial one.
-/
def version (self : Lexer H recovery) : Version :=
  self.core.version

/- LEAN: takes the lexer apart so that the consumer and the fields are each held once, runs
the step on them, and puts the lexer together again; Rust does the same through
`&mut self`. -/
@[inline]
def run [Monad m] (self : Lexer H recovery) (step : InnerM H m α) :
    m (α × Lexer H recovery) := do
  let { handler, core } := self
  let ((result, core), handler) ← (step.run core).run handler
  return (result, { handler, core })

/- LEAN: what Rust's `&mut self` leaves usable after a call that failed: the type of the
recovering lexer, and nothing for a lexer that stops at its first error, whose further calls
panic in Rust. -/
/--
What a lexer call that failed gives back: nothing for a lexer that stops
at its first error, which cannot be used again, and the lexer itself for a
recovering one, from which the rest of the input is to be fed.
-/
def AfterError (H : Type) : Recovery → Type
  | .failFast => Unit
  | .recovering => Lexer H .recovering

/--
A recovering lexer whose end of the input raised an error.

The input has ended, so only the end of the input can be lexed again,
which completes the recovery.
-/
structure PendingEof (H : Type) where
  lexer : Lexer H .recovering

/- LEAN: what Rust's `&mut self` leaves usable after `lex_eof` failed. Rust panics on a
non-empty slice fed to a recovering lexer whose end of the input failed and continues. -/
/--
What a recovering lexer gives back after its end of the input failed: the
lexer, if the error is final, or the lexer that can only lex the end of the
input again, if the error continues at the end.
-/
inductive AfterEof (H : Type) where
  | lexer (lexer : Lexer H .recovering)
  | pending (pending : PendingEof H)

/--
What a lexer gives back after its end of the input failed: nothing for a
lexer that stops at its first error, and what remains of a recovering one.
-/
def AfterEofError (H : Type) : Recovery → Type
  | .failFast => Unit
  | .recovering => AfterEof H

def afterError : {recovery : Recovery} → Lexer H recovery → AfterError H recovery
  | .failFast, _ => ()
  | .recovering, lexer => lexer

def afterEofError : {recovery : Recovery} → Lexer H recovery → (continues : Bool) →
    AfterEofError H recovery
  | .failFast, _, _ => ()
  | .recovering, lexer, true => .pending ⟨lexer⟩
  | .recovering, lexer, false => .lexer lexer

/- LEAN: the Rust methods take `&mut self`; these take the lexer and return it updated along
with the result. If the caller does not keep the old lexer, it is updated in place. -/

/--
Lexes the given slice, sending the lexed tokens to the consumer.

If the token consumer returns `ControlFlow.break` on some token,
the lexer passes it through, adding the break location.
Subsequent bytes are discarded until EOF, which resets
the lexer.

If the token consumer returns `ControlFlow.continue` on all tokens,
the lexer is ready for further lexing.

If an error occurs, a lexer that stops at its first error is not given
back. A recovering lexer makes the consumer abandon its unfinished work
and returns the error. `LexError.continuesFrom` determines the location
from which further lexing should be started for error recovery.
-/
def lexSlice [Monad m] [Consume H m R E] [LexRecovery recovery H m] (self : Lexer H recovery)
    (slice : ByteSlice) :
    m (Except (LexError E × AfterError H recovery)
      (ControlFlow (Located R) × Lexer H recovery)) := do
  let step := lexSliceStep (LexRecovery.abandon recovery) (LexRecovery.recover recovery) slice
  let (result, self) ← self.run step
  return match result with
    | .ok flow => .ok (flow, self)
    | .error err => .error (err, afterError self)

/--
Lexes end-of-file, sending the lexed tokens to the consumer.

If the token consumer returns `ControlFlow.break` on the EOF token,
the lexer passes it through, adding the break location.
Subsequent bytes are discarded until EOF, which resets
the lexer.

If the token consumer returns `ControlFlow.continue` on the EOF token,
the lexer resets itself and returns `ControlFlow.continue`.

If an error occurs, a lexer that stops at its first error is not given
back. A recovering lexer makes the consumer abandon its unfinished work
and returns the error. `LexError.continuesFrom` determines the location
from which further lexing should be started for error recovery.
-/
def lexEof [Monad m] [Consume H m R E] [LexRecovery recovery H m] (self : Lexer H recovery) :
    m (Except (LexError E × AfterEofError H recovery)
      (ControlFlow (Located R) × Lexer H recovery)) := do
  let step := lexEofStep (LexRecovery.abandon recovery) (LexRecovery.recover recovery)
  let (result, self) ← self.run step
  return match result with
    | .ok flow => .ok (flow, self)
    | .error err => .error (err, afterEofError self err.continuesFrom.isSome)

/--
Lexes the end of the input again, which completes the recovery.

The lexer hands over the end-of-file token. An error is final: the
lexer resets itself and does not continue.
-/
def PendingEof.lexEof [Monad m] [Consume H m R E] [Recover H m] (self : PendingEof H) :
    m (Except (LexError E × Lexer H .recovering)
      (ControlFlow (Located R) × Lexer H .recovering)) := do
  let step := lexEofStep (Recover.abandon (H := H)) (Recover.recover (H := H))
  let (result, lexer) ← self.lexer.run step
  return match result with
    | .ok flow => .ok (flow, lexer)
    | .error err => .error (err, lexer)

/--
Lexes the whole input including EOF at the end.

If the token consumer returns `ControlFlow.break` on some token,
the lexer passes it through, adding the break location, and
resets itself as if at the start of a new input.

If the token consumer returns `ControlFlow.continue` on all tokens
including EOF, the lexer resets itself after EOF
and returns `ControlFlow.continue`.

If an error occurs, the lexer is not given back.
-/
def lexAll [Monad m] [Consume H m R E] (self : Lexer H) (input : ByteSlice) :
    m (Except (LexError E × AfterError H .failFast) (ControlFlow (Located R) × Lexer H)) := do
  match ← self.lexSlice input with
  | .ok (.break result, self) =>
    -- reset the lexer as if we are at the start of a new file
    let ((), self) ← self.run (reset (H := H) (m := m))
    return .ok (.break result, self)
  | .ok (.continue, self) => self.lexEof
  | .error err => return .error err

end Lexer

end BSmtLib.Proofs.Lexer.X2Contents

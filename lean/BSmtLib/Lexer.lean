module

public import BSmtLib.Lexer.Internal.CharClass
public import BSmtLib.Lexer.Error
public import BSmtLib.Lexer.Internal.Helpers
public import BSmtLib.Lexer.Recovery
public import BSmtLib.Token
public import BSmtLib.Token.Cursor
public import BSmtLib.Token.ConsumeFrom
import all Std.Data.ByteSlice

public section

namespace BSmtLib.Lexer

open Recovery (FailFast Recovering)
open BSmtLib.Token.BatchCursor.Internal (discardRequested resetConsumed remaining relexRequested
    EndsAfter consumedSpanOf foldConsumedCategories consumedEndOf)

/- The lexer's state and the monads of its steps. They are public, in `Internal`, only so that the
proofs of the lexers can read them; they are not a part of the library's interface. -/
namespace Internal

/-- Maximal number of tokens that can be batched. -/
def BATCH_CAPACITY : Nat := 256

/-- Why lexing stopped before the end of the slice. -/
inductive Stop (R : Type) where
  /-- The consumer requested lexing again from the stop location. -/
  | relex
  /-- The consumer finished with a result at the stop location. -/
  | finished (result : R)
  /-- The consumer had the rest discarded from the stop location, finishing with the result if
  there is one. -/
  | discarded (result : Option R)

/- LEAN: not in Rust: the floor and `stopAfter`. The loop over a slice lexes with a floor that
every token it hands over ends after, and so every stop of the consumer, at the end of a token
the consumer took. At first the floor is the offset before the first byte of the slice: the
batch starts empty, a token lexed in the slice starts in it, and a token that began in an
earlier slice ends in this one. After the loop has gone back to the end of the last token the
consumer took, the floor is that offset: every token lexed from then on starts at or after it
and has a byte. So every stop is at or after the start of the slice, which Rust asserts, and
after the last location gone back to, which ends the loop. -/
structure Interrupted (R E : Type) (floor : Option Nat) where
  result : Except (Error.LexErrorCause E) (Stop R)
  /-- The span of the error: that of the bytes that raised a lexical error, or that of the last
  token the consumer took. For a stop of the consumer, that of the last token it took. -/
  span : Span
  location : Span.Location
  /-- A stop of the consumer is after the floor, if there is one. -/
  stopAfter : ∀ p, floor = some p → ∀ stop, result = .ok stop → p < location.offset

/--
A lexing error with the effective failure location.

For a lexical error, the effective failure location is before the byte that
raised it, or the end of the input if the end raised it. For a consumer error,
it is after the last token the consumer has consumed.
-/
structure Failure (E : Type) where
  cause : Error.LexErrorCause E
  /-- The span of the error: that of the bytes that raised a lexical error, or that of the last
  token the consumer consumed. -/
  span : Span
  location : Span.Location

/- LEAN: the fields of the Rust `Lexer` except the handler, which the lexer's monad keeps
separately (see `LexM`). The lexer states are documented at `LexerState` in Rust. The
batch lives here instead of in a local of `lex_slice_inner`, so that its storage is reused
from one slice to the next; it is empty whenever lexing returns. -/
structure LexerCore where
  /-- The SMT-LIB version the lexer currently operates under. -/
  version : Token.Version
  /-- The initial SMT-LIB version the lexer will reset to. -/
  initialVersion : Token.Version
  /-- Current lexer state. -/
  state : Helpers.LexerState
  /--
  Where the lexer began to discard bytes until the end of the input, if it discards.

  The consumer asks for discarding through its cursor.
  -/
  discardedFrom : Option Span.Location
  /--
  Whether the lexer holds the result the consumer broke with.

  The result itself is kept by the lexer outside its state; any entry handed over while it is
  held is trailing input.
  -/
  holding : Bool
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
  recoveryState : Option Helpers.RecoveryState
  /-- Location of the start of the currently-processed token. -/
  tokenStart : Span.Location
  /-- The currently-built string content of the currently-processed token. -/
  tokenContent : Helpers.ContentBuffer
  /--
  Offset of the start of the byte being processed during lexing.

  It only advances after byte consumption.
  -/
  offset : Nat
  /- LEAN: not in Rust, where positions are relative to the rest of the slice, whose first
  byte is at `offset`. Here positions are in the input's array, and `base` is the position of
  the byte at `offset`; it is zero when no slice is being lexed. -/
  /-- The position in the input of the byte at `offset`. -/
  base : USize
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
  batch : Token.Internal.TokenBatch
  /- LEAN: not in Rust: two facts about the fields above, which show that every token handed
  over has a byte and is after the tokens before it (see `TokenBatch.ordered`). Between the
  steps of the loop over a slice, `offset` is the offset of the next byte to be lexed. A step
  that leaves a token unfinished sets the state, the token start and the offset in one change
  of the fields, and so does a step that puts the batch back, so that the facts hold after
  every change. They cost nothing when the lexer runs. -/
  /-- The token in progress, if any, starts before `offset`. -/
  tokenStarted : state = .normal ∨ tokenStart.offset < offset
  /-- The tokens of the batch end at or before `offset`. -/
  batchEnded : batch.lastEnd ≤ offset

/- LEAN: Rust keeps the held result in the lexer as `Option<SmtLocated<C::Result>>`; the result
type is the consumer's, which its instance of `Consume` gives, so the lexer takes the instance. -/
structure _root_.BSmtLib.Lexer (H : Type) {R E : Type} [Token.Consume H R E]
    (recovery : Type := Lexer.Recovery.FailFast) where
  private mk ::
  /-- Consumer of produced tokens. -/
  private handler : H
  private core : LexerCore
  /-- The result the consumer broke with, located where it broke, held until the end of the
  input. -/
  private held : Option (Span.Located R)

/- LEAN: Rust's lexer methods take `&mut self` and return `Result<usize, Interrupted<..>>`,
using `?` to pass an interruption up. In Lean the same is a monad: `StateT LexerCore` holds
the lexer's fields as mutable state, `StateT H` the handler, and `ExceptT (Interrupted R E)`
is the `Err` that `throw` raises and that passes up through every `←` like `?`. `ExceptT` is
outermost so that the lexer's fields keep their changes when an interruption is thrown, as
in Rust. The handler is a separate state so that it can be handed to `consume` without
another reference to it remaining in the lexer's state, which would make the handler's
updates copy it. -/
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
@[expose]
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

/-- The stream offset of `position` in the input. -/
@[inline]
def LexerCore.offsetAt (self : LexerCore) (position : USize) : Nat :=
  self.offset + (position - self.base).toNat

/-- Location of `position` in the input.

Every line feed before `position` must be marked before calling this. -/
@[inline]
def LexerCore.locationAt (self : LexerCore) (position : USize) : Span.Location :=
  let offset := self.offsetAt position
  Span.Location.Internal.new offset self.line (offset - self.lineStart)

/-- The current location: that of the next byte to be lexed. -/
@[inline]
def LexerCore.currentLocation (self : LexerCore) : Span.Location :=
  self.locationAt self.base

/-- The lexer state with the offset moved on to that of `position`, the next byte to be lexed. -/
@[inline]
def LexerCore.advance (self : LexerCore) (position : USize) : LexerCore :=
  { self with
    offset := self.offsetAt position
    base := position
    tokenStarted := self.tokenStarted.imp_right fun h => Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)
    batchEnded := Nat.le_trans self.batchEnded (Nat.le_add_right _ _) }

theorem LexerCore.Bound.advance {self : LexerCore} {floor : Option Nat} {low : Nat}
    (h : self.Bound floor low) (position : USize) : (self.advance position).Bound floor low :=
  ⟨Nat.le_trans h.1 (Nat.le_add_right _ _), fun p hp =>
    ⟨Nat.le_trans (h.2 p hp).1 (Nat.le_add_right _ _),
      (h.2 p hp).2.1.imp_right
        (Or.imp_right fun h => Nat.lt_of_lt_of_le h (Nat.le_add_right _ _)),
      (h.2 p hp).2.2⟩⟩

/--
Moves the lexer back to `location`, which the tokens handed over
so far end at, discarding whatever was lexed beyond it; `position` is its position in the
input.
-/
def LexerCore.resumeAt (self : LexerCore) (location : Span.Location)
    (position : USize) : LexerCore :=
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
    batchEnded := Nat.le_of_eq (Token.Internal.TokenBatch.lastEnd_clear _ _) }

theorem LexerCore.bound_resumeAt (self : LexerCore) (location : Span.Location) (position : USize) :
    (self.resumeAt location position).Bound (some location.offset) 0 :=
  ⟨Nat.zero_le _, fun p hp => by
    cases hp
    exact ⟨Nat.le_refl _, .inl rfl, Token.Internal.TokenBatch.startsFrom_clear _ _ _⟩⟩

theorem LexerCore.Bound.weaken {self : LexerCore} {floor : Option Nat} {low : Nat}
    (h : self.Bound floor low) : self.Bound floor 0 :=
  ⟨Nat.zero_le _, h.2⟩

/-!
The steps of the lexer. They are public, in `Internal`, only so that the proofs of the lexers
can read them; they are not a part of the library's interface.
-/

/- LEAN: not in Rust. The lexer takes the batch back after the consumer is done with the
cursor; if nothing else refers to it, its storage is overwritten by the next batch, as the
Rust lexer overwrites its fixed arrays. -/
/-- The batch of the cursor, for reuse of its storage once the cursor is spent. -/
@[inline]
def intoBatch {batch : Token.BatchTag} (cursor : Token.BatchCursor batch) :
    Token.Internal.TokenBatch :=
  Token.BatchCursor.Internal.batch cursor

theorem tag_intoBatch {batch : Token.BatchTag} (cursor : Token.BatchCursor batch) :
    (intoBatch cursor).tag = batch :=
  Token.BatchCursor.Internal.tag_batch cursor

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]
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
abbrev Started (floor : Option Nat) (low : Nat) (start : Span.Location) : Prop :=
  start.offset < low ∧ ∀ p, floor = some p → p < low

/-- Moves the token in progress, which starts at `start`, to the state. -/
@[inline]
def setTokenState (state : Helpers.LexerState) (start : Span.Location)
    (h : Started floor low start) :
    LexM H m R E floor low Unit :=
  modifyBound fun c hc =>
    ⟨{ c with state, tokenStart := start, tokenStarted := .inr (Nat.lt_of_lt_of_le h.1 hc.1) },
      ⟨hc.1, fun p hp =>
        ⟨(hc.2 p hp).1, .inr (.inr (Nat.lt_of_lt_of_le (h.2 p hp) hc.1)), (hc.2 p hp).2.2⟩⟩⟩

/- LEAN: Rust's `C::IS_CONCRETE`, read from the consumer's instance. -/
@[inline]
def consumesWhitespaceAndComments : LexM H m R E floor low Bool :=
  pure (Token.Consume.isConcrete (H := H))

/- LEAN: the content buffer is taken out of the state before it is changed:
changing `c.tokenContent` while `c` still refers to it would find it shared and copy it,
together with its array. -/
/-- Changes the content buffer in place. -/
@[inline]
def modifyContent (f : Helpers.ContentBuffer → Helpers.ContentBuffer) : LexM H m R E floor low Unit
    :=
  modifyCore fun c =>
    let content := c.tokenContent
    let c := { c with tokenContent := Helpers.ContentBuffer.empty }
    { c with tokenContent := f content }

@[inline]
def extendContent (input : CharClass.Input) (start stop : USize) : LexM H m R E floor low Unit :=
  modifyContent (·.extendFrom input.bytes start.toNat stop.toNat)

@[inline]
def pushContent (c : UInt8) : LexM H m R E floor low Unit :=
  modifyContent (·.push c)

/- LEAN: what the loop of `lexNormal` keeps true of the offset `offset` of the position `base`,
from which it computes the offsets of the positions after it. -/
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
def startToken (offset : Nat) (base position : USize) (hframe : Frame floor low offset) :
    LexM H m R E floor low
      {start : Span.Location // start.offset = offset + (position - base).toNat} := do
  -- update the token start to the computed location
  let c ← getCore
  let startOffset := offset + (position - base).toNat
  let start : Span.Location :=
    Span.Location.Internal.new startOffset c.line (startOffset - c.lineStart)
  modifyCore (fun c => { c with tokenStart := start, state := .normal, tokenStarted := .inl rfl })
    fun _ hc => ⟨hc.1, fun p hp =>
      ⟨(hc.2 p hp).1, .inr (.inl (by
        simp only [start, Span.Location.Internal.offset_new]
        exact Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _))),
        (hc.2 p hp).2.2⟩⟩
  -- clear the token string
  modifyContent (·.clear)
  return ⟨start, Span.Location.Internal.offset_new ..⟩

@[inline]
def markLineFeedAt (position : USize) : LexM H m R E floor low Unit :=
  -- when lexing a run, this is used to mark a line feed
  -- the locations must only refer to positions after it afterwards
  modifyCore fun c => { c with line := c.line + 1, lineStart := c.offsetAt position + 1 }

/-- Fails with an error spanning up to `position` with effective failure at `failure`. -/
def failWith (kind : Error.LexicalErrorKind) (position failure : USize) :
    LexM H m R E floor low α := do
  let c ← getCore
  let span := Span.Internal.newUnchecked c.tokenStart (c.locationAt position)
  -- no tokens have been consumed, as this is an error
  -- that occurred during lexing
  throw {
    result := .error (.lexical kind)
    span
    location := c.locationAt failure
    stopAfter := fun _ _ _ h => nomatch h }

/--
Fails with an error spanning the token up to `position`.

Used for errors detected mid-run, e.g. forbidden byte in a string
or a backslash in a quoted symbol.
-/
/- LEAN: Rust panics if `position` is zero, which no caller passes: an error detected at a
byte spans that byte. -/
def failAt (kind : Error.LexicalErrorKind) (position : USize) : LexM H m R E floor low α :=
  -- the byte before the position raised the error
  failWith kind position (position - 1)

/-- Fails with an error spanning the token so far and, if it ended at a byte, that byte. -/
def fail (kind : Error.LexicalErrorKind) (tokenEnd : Helpers.TokenEnd) : LexM H m R E floor low α :=
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
def expectDelimiter (next : UInt8) (position : USize) : LexM H m R E floor low Unit := do
  unless Helpers.isDelimiter next do
    failAt .missingDelimiter (position + 1)

/- LEAN: runs the consumer on the cursor. The consumer runs in `StateT H m`, which the `←` lifts
into the lexer's monad, where the consumer is the inner state. -/
def callConsumer {batch : Token.BatchTag} (cursor : Token.BatchCursor batch) (h : cursor.HasNext) :
    LexM H m R E floor low
      (Except E (ControlFlow R) × { c : Token.BatchCursor batch // c.Consumed cursor }) := do
  let action : StateT H m
      (Except E (ControlFlow R) × { c : Token.BatchCursor batch // c.Consumed cursor }) :=
    Token.ConsumeFrom.consume (H := H) cursor h
  action

/-- The error that the entry at the span is trailing input, after the value the consumer broke
with. -/
@[inline]
def trailingAt (span : Span) : Interrupted R E floor :=
  { result := .error (.lexical .unexpectedTrailingToken)
    span
    location := span.start
    stopAfter := fun _ _ _ h => nomatch h }

/- LEAN: Rust's `flush_cursor` loops while the cursor is not empty; here the loop is the
recursion, which ends as every call of the consumer consumes a token, by the proof the
consumer returns. The interruption is returned rather than thrown, so that the caller can
take the batch back first. A stop is after the floor, as every token of the batch ends after
it (`BatchCursor.Consumed.lt_consumedEndOf`). -/
/--
Hands the cursor over to the consumer until nothing remains in it or the consumer stops.

While the lexer holds a result, the first token is trailing input, and is not handed over. When
the consumer breaks, the tokens it left in the cursor are trailing input.

Returns the stop, if the consumer stopped, and the cursor as the consumer left it.
-/
def flushCursor {batch : Token.BatchTag} (cursor : Token.BatchCursor batch)
    (hfloor : ∀ p, floor = some p → EndsAfter cursor p) :
    LexM H m R E floor low (Option (Interrupted R E floor) × Token.BatchCursor batch) := do
  -- flush the cursor until nothing remains
  if h : cursor.HasNext then
    if (← getCore).holding then
      -- a result is held: what follows it is trailing input
      return (some (trailingAt (cursor.span (cursor.peek h))), cursor)
    else
      let (result, ⟨next, consumed⟩) ← callConsumer cursor h
      -- the stop takes effect after the consumed tokens
      let location := consumedEndOf next consumed
      have after : ∀ p, floor = some p → p < location.offset := fun p hp =>
        consumed.lt_consumedEndOf (hfloor p hp)
      -- process the result
      match result with
      | .ok flow =>
        if discardRequested next then
          -- the rest is to be discarded, whatever the consumer answered
          let held := match flow with
            | .continue => none
            | .break result => some result
          return (some {
            result := .ok (.discarded held)
            span := consumedSpanOf next consumed
            location
            stopAfter := fun p hp _ _ => after p hp }, next)
        else
          match flow with
          | .continue =>
            if relexRequested next then
              -- we need to stop and relex here
              return (some {
                result := .ok .relex
                span := consumedSpanOf next consumed
                location
                stopAfter := fun p hp _ _ => after p hp }, next)
            else
              -- zero the number of consumed tokens in the cursor
              -- continue flushing until nothing remains
              have : remaining (resetConsumed next) < remaining cursor := by
                rw [Token.BatchCursor.remaining_resetConsumed]
                exact consumed.remaining_lt
              flushCursor (resetConsumed next) fun p hp =>
                Token.BatchCursor.endsAfter_resetConsumed (consumed.follows.endsAfter (hfloor p hp))
          | .break result =>
            if h : next.HasNext then
              -- the tokens the consumer left are trailing input
              return (some (trailingAt (next.span (next.peek h))), next)
            else
              return (some {
                result := .ok (.finished result)
                span := consumedSpanOf next consumed
                location
                stopAfter := fun p hp _ _ => after p hp }, next)
      | .error err =>
        if discardRequested next then
          -- the consumer fails where it has had the rest discarded: the discarding stands,
          -- from where it began
          modifyCore fun c => { c with discardedFrom := c.discardedFrom.or (some location) }
        return (some {
          result := .error (.consumer err)
          span := consumedSpanOf next consumed
          location
          stopAfter := fun _ _ _ h => nomatch h }, next)
  else
    -- everything was consumed without break or error
    return (none, cursor)
termination_by remaining cursor

/-- Puts a spent batch back into the lexer state, empty. -/
@[inline]
def storeSpent (spent : Token.Internal.TokenBatch) : LexM H m R E floor low Unit :=
  modifyBound fun c hc =>
    ⟨{ c with
        batch := spent.clear c.offset
        batchEnded := Nat.le_of_eq (Token.Internal.TokenBatch.lastEnd_clear _ _) },
      ⟨hc.1, fun p hp => ⟨(hc.2 p hp).1, (hc.2 p hp).2.1,
          Token.Internal.TokenBatch.startsFrom_clear _ _ _⟩⟩⟩

/- LEAN: Rust's `flush_cursor` takes a cursor over the lexer's arrays; here the batch itself
is handed to the consumer in the cursor, and taken back afterwards, whatever the consumer
decides, so that its storage is overwritten by the next batch. The batch's array of contents
is then set to `bytesAfter`, so that the batch does not keep a reference to the lexer's
content buffer, which would make the buffer's next change copy it. If the consumer stops,
the batch goes back into the lexer state, empty, before the stop is thrown; otherwise the
caller takes it. -/
/-- Hands the batch over to the consumer and takes it back, spent. -/
def handOver (batch : Token.Internal.TokenBatch) (bytesAfter : ByteArray)
    (hfloor : ∀ p, floor = some p → batch.EndsAfter p) :
        LexM H m R E floor low Token.Internal.TokenBatch :=
    do
  let (stop, cursor) ←
      flushCursor (Token.BatchCursor.Internal.new (← getCore).version batch) fun p hp =>
    Token.BatchCursor.endsAfter_new (hfloor p hp) _
  if (← getCore).recovers then
    match stop with
    | some _ =>
      -- the consumer has not taken the whole batch
      -- count the actually consumed parentheses only
      -- and reset the lexed depth to them
      modifyCore fun c =>
        let consumedDepth := foldConsumedCategories cursor c.consumedDepth fun depth category =>
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
  let spent : Token.Internal.TokenBatch := { intoBatch cursor with bytes := bytesAfter }
  if let some interrupted := stop then
    storeSpent spent
    throw interrupted
  return spent

/-- Takes the batch out of the lexer state, leaving an empty one without storage. -/
@[inline]
def takeBatch :
    LexM H m R E floor low {batch : Token.Internal.TokenBatch // ∀ p, floor = some p →
        batch.StartsFrom p} :=
  modifyGetThe {c : LexerCore // c.Bound floor low} fun c =>
    (⟨c.val.batch, fun p hp => (c.property.2 p hp).2.2⟩,
      ⟨{ c.val with
          batch := default
          batchEnded := Token.Internal.TokenBatch.lastEnd_default ▸ Nat.zero_le _ },
        ⟨c.property.1, fun p hp =>
          ⟨(c.property.2 p hp).1, (c.property.2 p hp).2.1,
              Token.Internal.TokenBatch.startsFrom_default p⟩⟩⟩)

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
def handOverStored (ty : Token.TokenCategory) (start «end» : Span.Location)
    (hend : start.offset < «end».offset) (hfloor : ∀ p, floor = some p → p < «end».offset) :
    LexM H m R E floor low Unit := do
  -- flush the batch, then hand over this token
  flushBatch
  let ⟨batch, _⟩ ← takeBatch
  let bytes := batch.bytes
  let c ← getCore
  let batch :=
      ({ batch.clear start.offset with bytes := c.tokenContent.bytes } : Token.Internal.TokenBatch)
    |>.pushLocated ty 0 c.tokenContent.len start «end»
      (Nat.le_of_eq (Token.Internal.TokenBatch.lastEnd_clear _ _)) (.inl hend)
  storeSpent (← handOver batch bytes fun p hp =>
    Token.Internal.TokenBatch.endsAfter_pushLocated (fun _ h => absurd h (Nat.not_lt_zero _))
        (hfloor p hp))

/-- Hands over the end-of-file token, at the location, unless a result is held, which the end
of the input confirms instead. -/
def handOverEof (location : Span.Location) : LexM H m R E none low Unit := do
  -- flush the batch, then hand over this token
  flushBatch
  if (← getCore).holding then
    -- the held result is returned without the end of the input handed over
    return
  let ⟨batch, _⟩ ← takeBatch
  let bytes := batch.bytes
  let c ← getCore
  let batch := ({ batch.clear location.offset with bytes := c.tokenContent.bytes } :
      Token.Internal.TokenBatch)
    |>.pushLocated .endOfFile 0 c.tokenContent.len location location
      (Nat.le_of_eq (Token.Internal.TokenBatch.lastEnd_clear _ _)) (.inr ⟨rfl, rfl⟩)
  storeSpent (← handOver batch bytes fun _ h => nomatch h)

/-- The location of `position`, given that `base` is the position of the step's offset. -/
@[inline]
def locationFrom (base position : USize) :
    LexM H m R E floor low {location : Span.Location // low ≤ location.offset} := do
  let c ← getCore
  let offset := low + (position - base).toNat
  return ⟨Span.Location.Internal.new offset c.line (offset - c.lineStart),
    by rw [Span.Location.Internal.offset_new]; exact Nat.le_add_right _ _⟩

/- LEAN: Rust sinks a token with its content either borrowed from the slice or stored in the
content buffer. A token lexed by `lexNormal` is borrowed and put into the batch that the loop
holds (see `pushBorrowed`); the token in progress of a step that started with it is stored,
and sunk here. `start` is where it starts, and `base` the position of the step's offset. -/
/-- Sinks the token in progress, which ends at `tokenEnd`; its content is in the content
buffer. -/
@[inline]
def sinkStored (ty : Token.TokenCategory) (tokenEnd : Helpers.TokenEnd)
    (start : Span.Location) (base : USize) (h : Started floor low start) :
    LexM H m R E floor low Unit := do
  -- this is in our own buffer, so we cannot put it into the batch
  -- as we need the buffer usable for the next token
  let ⟨«end», hend⟩ ← locationFrom base tokenEnd.position
  handOverStored ty start «end» (Nat.lt_of_lt_of_le h.1 hend) fun p hp =>
    Nat.lt_of_lt_of_le (h.2 p hp) hend

/--
Sinks a decimal token.

The token's own shape is checked first, then that `next`, the byte
at the end (if there is one), delimits it.
-/
@[inline]
def finishDecimal (tokenEnd : Helpers.TokenEnd) (next : Option UInt8) (start : Span.Location)
    (base : USize) (h : Started floor low start) : LexM H m R E floor low Unit := do
  -- decimals of the form 7. without any digit in fractional part are disallowed
  let last := Helpers.Content.stored.last? (← getCore).tokenContent
  if last.isNone || last == some (byte! '.') then
    fail (.expected .fractionDigit) tokenEnd
  if let some next := next then
    expectDelimiter next tokenEnd.position
  sinkStored .decimal tokenEnd start base h

@[inline]
def finishNumeral (tokenEnd : Helpers.TokenEnd) (start : Span.Location) (base : USize)
    (h : Started floor low start) : LexM H m R E floor low Unit :=
  sinkStored .numeral tokenEnd start base h

/-- The type of the token of the digit run: hexadecimal or binary. -/
theorem DigitRun.tokenType_ne {run : Helpers.DigitRun}
    (h : run = Helpers.HEXADECIMAL_RUN ∨ run = Helpers.BINARY_RUN) : run.tokenType ≠ .endOfFile :=
    by
  rcases h with h | h <;> (subst h; nofun)

/--
Sinks a hexadecimal/binary token.

The token's own shape is checked first, then that `next`, the byte
at the end (if there is one), delimits it.
-/
@[inline]
def finishDigitRun (run : Helpers.DigitRun)
    (tokenEnd : Helpers.TokenEnd) (next : Option UInt8) (start : Span.Location) (base : USize)
    (h : Started floor low start) : LexM H m R E floor low Unit := do
  -- digit runs must not be empty
  if Helpers.Content.stored.size (← getCore).tokenContent == 0 then
    fail run.emptyError tokenEnd
  if let some next := next then
    expectDelimiter next tokenEnd.position
  sinkStored run.tokenType tokenEnd start base h

@[inline]
def finishSimpleSymbol (tokenEnd : Helpers.TokenEnd) (start : Span.Location) (base : USize)
    (h : Started floor low start) : LexM H m R E floor low Unit :=
  sinkStored .unquotedSymbol tokenEnd start base h

/--
Sinks a keyword.

The token's own shape is checked first, then that `next`, the byte
at the end (if there is one), delimits it.
-/
@[inline]
def finishKeyword (tokenEnd : Helpers.TokenEnd) (next : Option UInt8) (start : Span.Location)
    (base : USize) (h : Started floor low start) : LexM H m R E floor low Unit := do
  -- ensure the keyword is not empty
  if Helpers.Content.stored.size (← getCore).tokenContent == 0 then
    fail .emptyKeyword tokenEnd
  if let some next := next then
    expectDelimiter next tokenEnd.position
  sinkStored .keyword tokenEnd start base h

@[inline]
def finishStringLiteral (tokenEnd : Helpers.TokenEnd) (start : Span.Location) (base : USize)
    (h : Started floor low start) : LexM H m R E floor low Unit :=
  sinkStored .string tokenEnd start base h

@[inline]
def finishWhitespace (tokenEnd : Helpers.TokenEnd) (start : Span.Location) (base : USize)
    (h : Started floor low start) : LexM H m R E floor low Unit :=
  sinkStored .whitespace tokenEnd start base h

/- LEAN: Rust keeps the batch length, the line and the line start in locals of `lex_normal`.
Here the local is the batch itself, which the loop passes along; the line and the line start
stay in the lexer state, which the fast path only reads. While the loop holds the batch, the
lexer state has an empty batch. Unlike Rust, the loop holds the batch on its slow path too,
and puts it back into the lexer state only where it ends: where it returns or throws an
error (`leave`, `leavePending`). Its offset and position, `offset` and `base`, go back into
the lexer state with it, moved on to where the loop ends; this is where the lexer is anyway,
as the loop over the slice moves them there after the step. The batch is a local of its own,
not a field of a structure of locals, so that it is not shared when it is changed. What the
loop knows of the batch it holds at `index` (`Held`) shows that the tokens it appends are in
order. -/

/-- The offsets of positions at or after `base` grow with the positions. -/
theorem sub_toNat_le {base x y : USize} (hx : base.toNat ≤ x.toNat)
    (hy : x.toNat ≤ y.toNat) : (x - base).toNat ≤ (y - base).toNat := by
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hx),
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (Nat.le_trans hx hy))]
  omega

theorem sub_toNat_lt {base x y : USize} (hx : base.toNat ≤ x.toNat)
    (hy : x.toNat < y.toNat) : (x - base).toNat < (y - base).toNat := by
  rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr hx),
    USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (Nat.le_trans hx (Nat.le_of_lt hy)))]
  omega

/-- The batch that the loop of `lexNormal` holds at `index`: its tokens end at or before
`index`, and start at or after the floor. -/
abbrev Held (floor : Option Nat) (offset : Nat) (base index : USize)
    (batch : Token.Internal.TokenBatch) :
    Prop :=
  batch.lastEnd ≤ offset + (index - base).toNat ∧ ∀ p, floor = some p → batch.StartsFrom p

theorem Held.mono {floor : Option Nat} {offset : Nat} {base index next : USize}
    {batch : Token.Internal.TokenBatch} (h : Held floor offset base index batch)
    (hindex : base.toNat ≤ index.toNat)
    (hnext : index.toNat ≤ next.toNat) : Held floor offset base next batch :=
  ⟨Nat.le_trans h.1 (Nat.add_le_add_left (sub_toNat_le hindex hnext) _), h.2⟩

/-- Puts the batch held by the loop back into the lexer state, with the lexer at `position`,
between tokens. -/
@[inline]
def leave (offset : Nat) (base position : USize) (batch : Token.Internal.TokenBatch)
    (hframe : Frame floor low offset) (hbatch : Held floor offset base position batch) :
    LexM H m R E floor low Unit :=
  modifyBound fun c _ =>
    ⟨{ c with
        batch, offset := offset + (position - base).toNat, base := position, state := .normal,
        tokenStarted := .inl rfl, batchEnded := hbatch.1 },
      ⟨Nat.le_trans hframe.1 (Nat.le_add_right _ _), fun p hp =>
        ⟨Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _), .inl rfl, hbatch.2 p hp⟩⟩⟩

/-- Puts the batch held by the loop back into the lexer state, with the token from `start`
left unfinished in `state` at `position`. -/
@[inline]
def leavePending (state : Helpers.LexerState) (start : Span.Location) (offset : Nat)
    (base position : USize) (batch : Token.Internal.TokenBatch) (hframe : Frame floor low offset)
    (hbatch : Held floor offset base position batch)
    (hstart : start.offset < offset + (position - base).toNat)
    (hfloor : ∀ p, floor = some p → p ≤ start.offset) : LexM H m R E floor low Unit :=
  modifyBound fun c _ =>
    ⟨{ c with
        batch, offset := offset + (position - base).toNat, base := position, state,
        tokenStart := start, tokenStarted := .inr hstart, batchEnded := hbatch.1 },
      ⟨Nat.le_trans hframe.1 (Nat.le_add_right _ _), fun p hp =>
        ⟨Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _), .inr (.inl (hfloor p hp)),
          hbatch.2 p hp⟩⟩⟩

/-- Hands the full batch held by the loop over, and gives it back empty, with the origin. -/
/- LEAN: not inlined. Inlined into the loop of `lexNormalFrom`, the compiler reads the batch's
array of contents, which the hand-over takes, right after each token is put into the batch,
and so takes and drops a reference to it for every token. -/
@[noinline]
def flushHeld (batch : Token.Internal.TokenBatch) (origin : Nat)
    (hbatch : ∀ p, floor = some p → batch.StartsFrom p) :
    LexM H m R E floor low
      {batch : Token.Internal.TokenBatch //
        batch.lastEnd = origin ∧ ∀ p, floor = some p → batch.StartsFrom p} := do
  -- batch capacity reached, we need to flush the batch
  let bytes := batch.bytes
  let spent ← handOver batch bytes fun p hp => (hbatch p hp).endsAfter
  return ⟨spent.clear origin, Token.Internal.TokenBatch.lastEnd_clear _ _,
    fun _ _ => Token.Internal.TokenBatch.startsFrom_clear _ _ _⟩

/--
Puts a fast-path token into the batch if `emit` is set, flushing the batch
when it is full.

The content is from `contentStart` to `contentStop` in the input, and the span is on the
current line, over `start` to `end` in the input. `offset` is the stream offset of the
position `base`.
-/
/- LEAN: Rust writes the entry even when it is not emitted, as the next token overwrites it;
here a token that is not emitted is not written. -/
@[inline]
def pushFast (batch : Token.Internal.TokenBatch) (offset : Nat) (base : USize)
    (ty : Token.TokenCategory) (contentStart contentStop start «end» : USize) (emit : Bool)
    (hty : ty ≠ .endOfFile) (hstart : base.toNat ≤ start.toNat)
    (hend : start.toNat < «end».toNat) (hframe : Frame floor low offset)
    (hbatch : Held floor offset base start batch) :
    LexM H m R E floor low {batch : Token.Internal.TokenBatch //
        Held floor offset base «end» batch} := do
  if !emit then
    return ⟨batch, hbatch.mono hstart (Nat.le_of_lt hend)⟩
  let c ← getCore
  let line := c.line
  let lineStart := c.lineStart
  have hlt := Nat.add_lt_add_left (sub_toNat_lt hstart hend) offset
  let batch := batch.pushOnLine ty contentStart.toNat contentStop.toNat
    line lineStart (offset + (start - base).toNat) (offset + («end» - base).toNat) hbatch.1
    (.inl hlt)
  have hfrom : ∀ p, floor = some p → batch.StartsFrom p := fun p hp =>
    Token.Internal.TokenBatch.startsFrom_pushOnLine (hbatch.2 p hp)
      (Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _)) hty
  if batch.len == BATCH_CAPACITY then
    let ⟨batch, hlast, hfrom⟩ ← flushHeld batch (offset + («end» - base).toNat) hfrom
    return ⟨batch, Nat.le_of_eq hlast, hfrom⟩
  else
    return ⟨batch, Nat.le_of_eq (Token.Internal.TokenBatch.lastEnd_pushOnLine ..), hfrom⟩

/--
Puts a token lexed on the slow path into the batch, flushing the batch when it is full.

The content is from `contentStart` to `contentStop` in the input, and the span from `start`
to `tokenEnd` in the input. `offset` is the stream offset of the position `base`.
-/
/- LEAN: Rust's `sink_slice` with borrowed content, which puts the token into the lexer's
batch; here into the batch the loop holds. -/
@[inline]
def pushBorrowed (batch : Token.Internal.TokenBatch) (offset : Nat) (base : USize)
    (ty : Token.TokenCategory)
    (contentStart contentStop : USize) (start : Span.Location) (tokenEnd : USize)
    (hty : ty ≠ .endOfFile) (hafter : batch.lastEnd ≤ start.offset)
    (hend : start.offset < offset + (tokenEnd - base).toNat)
    (hfloor : ∀ p, floor = some p → p ≤ start.offset ∧ batch.StartsFrom p) :
    LexM H m R E floor low {batch : Token.Internal.TokenBatch //
        Held floor offset base tokenEnd batch} := do
  let c ← getCore
  let endOffset := offset + (tokenEnd - base).toNat
  let «end» : Span.Location :=
      Span.Location.Internal.new endOffset c.line (endOffset - c.lineStart)
  have hendOffset : «end».offset = endOffset := Span.Location.Internal.offset_new ..
  let batch := batch.pushLocated ty contentStart.toNat contentStop.toNat start «end» hafter
    (.inl (hendOffset ▸ hend))
  have hfrom : ∀ p, floor = some p → batch.StartsFrom p := fun p hp =>
    Token.Internal.TokenBatch.startsFrom_pushLocated (hfloor p hp).2 (hfloor p hp).1 hty
  if batch.len == BATCH_CAPACITY then
    let ⟨batch, hlast, hfrom⟩ ← flushHeld batch endOffset hfrom
    return ⟨batch, Nat.le_of_eq hlast, hfrom⟩
  else
    return ⟨batch,
      Nat.le_of_eq ((Token.Internal.TokenBatch.lastEnd_pushLocated ..).trans hendOffset), hfrom⟩

/--
Moves a fast-path symbol run that cannot be finished
in this slice to the stored path.

The token itself starts at `index`, its content either at `index`
(simple symbol) or `after` (quoted symbol, excludes pipe), and
the token continues at least to `runEndAt`, where it has been
left unfinished.
-/
def storeUnfinishedSymbolRun (input : CharClass.Input) (entry : UInt8) (offset : Nat)
    (base index after runEndAt : USize) (batch : Token.Internal.TokenBatch)
    (hframe : Frame floor low offset)
    (hindex : base.toNat ≤ index.toNat) (hrun : index.toNat < runEndAt.toNat)
    (hbatch : Held floor offset base index batch) : LexM H m R E floor low Unit := do
  let ⟨start, hstart⟩ ← startToken offset base index hframe
  have hpending : start.offset < offset + (runEndAt - base).toNat := by
    rw [hstart]; exact Nat.add_lt_add_left (sub_toNat_lt hindex hrun) _
  have hfloor : ∀ p, floor = some p → p ≤ start.offset := fun p hp => by
    rw [hstart]; exact Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _)
  have hbatch := hbatch.mono hindex (Nat.le_of_lt hrun)
  if entry &&& Helpers.FAST_PIPE != 0 then
    -- quoted symbol, skip the start pipe
    extendContent input after runEndAt
    leavePending .quotedSymbol start offset base runEndAt batch hframe hbatch hpending hfloor
  else
    -- simple symbol, do not skip anything
    extendContent input index runEndAt
    leavePending .simpleSymbol start offset base runEndAt batch hframe hbatch hpending hfloor

/- LEAN: the loops of the lexer are recursions on a position in the slice, which are shown to
end by the bytes left after it: every call goes on after a byte it has read. The facts that
show it are stated with `have` before the call; the tactic expands the local definitions that
they and the call are stated with, and does the arithmetic. -/
local macro "decreasing_position" : tactic =>
  `(tactic| ((try simp +zetaDelta only at *) <;> omega))

/- LEAN: not in Rust. What `startWhitespace` needs to return a position after the start of the
run: a byte there that the run takes. -/
/--
Whether the byte at `position` continues a whitespace run: a line feed, or whitespace other
than it.
-/
def ContinuesWhitespace (input : CharClass.Input) (position : USize) : Prop :=
  ∃ c, input.get? position = some c ∧ (c = byte! '\n' ∨ CharClass.endsRun c
      CharClass.RUN_NON_LF_WHITESPACE = false)

/-- The run ends after its start: the search has passed the start, or the byte where it continues
belongs to the run. -/
theorem lt_whitespaceRunEnd {input : CharClass.Input} {index start : USize} {c : UInt8}
    (hindex : index.toNat ≤ start.toNat)
    (hrun : index.toNat < start.toNat ∨ ContinuesWhitespace input start)
    (h : input.get? (CharClass.runEnd input start CharClass.RUN_NON_LF_WHITESPACE) = some c)
    (hc : ¬(c == byte! '\n') = true) :
    index.toNat < (CharClass.runEnd input start CharClass.RUN_NON_LF_WHITESPACE).toNat := by
  have hle := CharClass.le_runEnd input start CharClass.RUN_NON_LF_WHITESPACE
  rcases hrun with hlt | ⟨first, hfirst, hlf | hcontinues⟩
  · omega
  · -- the search stops at the line feed, where the byte is not one
    have : CharClass.runEnd input start CharClass.RUN_NON_LF_WHITESPACE ≠ start := by
      intro heq
      rw [heq, hfirst] at h
      cases h
      exact hc (by rw [hlf]; rfl)
    have : (CharClass.runEnd input start CharClass.RUN_NON_LF_WHITESPACE).toNat ≠ start.toNat :=
      fun heq => this (USize.toNat_inj.mp heq)
    omega
  · have := CharClass.lt_runEnd CharClass.RUN_NON_LF_WHITESPACE hfirst hcontinues
    omega

/-- A token that starts at `index` ends after its start at a later position. -/
theorem started_lt {offset : Nat} {base index position : USize} {start : Span.Location}
    (hstart : start.offset = offset + (index - base).toNat) (hindex : base.toNat ≤ index.toNat)
    (hlt : index.toNat < position.toNat) : start.offset < offset + (position - base).toNat := by
  rw [hstart]
  exact Nat.add_lt_add_left (sub_toNat_lt hindex hlt) _

/-- A token that starts at a position of the loop starts at or after the floor. -/
theorem started_floor {floor : Option Nat} {low offset : Nat} {base index : USize}
    {start : Span.Location} (hstart : start.offset = offset + (index - base).toNat)
    (hframe : Frame floor low offset) : ∀ p, floor = some p → p ≤ start.offset := fun p hp => by
  rw [hstart]
  exact Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _)

/-- What a token that starts at the position `index` of the loop gives to `pushBorrowed`. -/
theorem started_held {floor : Option Nat} {low offset : Nat} {base index : USize}
    {start : Span.Location} {batch : Token.Internal.TokenBatch}
    (hstart : start.offset = offset + (index - base).toNat)
    (hframe : Frame floor low offset) (hbatch : Held floor offset base index batch) :
    batch.lastEnd ≤ start.offset ∧
      ∀ p, floor = some p → p ≤ start.offset ∧ batch.StartsFrom p :=
  ⟨by rw [hstart]; exact hbatch.1, fun p hp => ⟨started_floor hstart hframe p hp, hbatch.2 p hp⟩⟩

/-- The position after an earlier one is past the earlier one. -/
theorem past_of_lt {input : CharClass.Input} {index next result : USize}
    (h : index.toNat < next.toNat) (hnext : next.toNat ≤ result.toNat) :
    index.toNat ≤ result.toNat ∧ (index.toNat < input.stop.toNat → index.toNat < result.toNat) :=
  ⟨by omega, fun _ => by omega⟩

/-- A position without a byte is at or after the end of the slice. -/
theorem stop_le_of_get?_none {input : CharClass.Input} {position : USize}
    (h : input.get? position = none) : input.stop.toNat ≤ position.toNat := by
  unfold CharClass.Input.get? at h
  split at h
  · cases h
  · rename_i hlt
    exact Nat.le_of_not_lt fun hl => hlt (USize.lt_iff_toNat_lt.mpr hl)

/- LEAN: the loop of `start_whitespace`, as a recursion on `«end»` that is shown to end.
`index` is where the run starts and `«end»` where the search for its end continues; the
search has passed `index` or the byte at `«end»` belongs to the run, so that the position
returned is after `index`, which `lexNormalFrom` is shown to end by. The token of the run starts
at `start`, and goes into the batch that `lexNormalFrom` holds, which comes back with the
position after the run; if the run reaches the end of the slice, the batch goes back into the
lexer state instead, and `none` is returned. -/
def startWhitespaceFrom (input : CharClass.Input) (offset : Nat) (base index «end» : USize)
    (start : Span.Location) (batch : Token.Internal.TokenBatch) (hframe : Frame floor low offset)
    (hstart : start.offset = offset + (index - base).toNat)
    (hend : base.toNat ≤ index.toNat ∧ index.toNat ≤ «end».toNat ∧ «end».toNat ≤ input.stop.toNat)
    (hrun : index.toNat < «end».toNat ∨ ContinuesWhitespace input «end»)
    (hbatch : Held floor offset base index batch) :
    LexM H m R E floor low (Option {next : USize × Token.Internal.TokenBatch //
      index.toNat < next.1.toNat ∧ Held floor offset base next.1 next.2}) := do
  -- find the first byte that is not whitespace other than a line feed
  let «end» := CharClass.runEnd input «end» CharClass.RUN_NON_LF_WHITESPACE
  -- the search goes on from where it was
  have : _ ≤ «end».toNat := CharClass.le_runEnd input _ CharClass.RUN_NON_LF_WHITESPACE
  match h : input.get? «end» with
  | some c =>
    if hc : c == byte! '\n' then
      -- the line feed is a part of the run, mark it and continue
      markLineFeedAt «end»
      have := CharClass.Input.toNat_add_one_of_get? h
      startWhitespaceFrom input offset base index («end» + 1) start batch hframe hstart
        ⟨hend.1, by omega, by omega⟩ (.inl (by omega)) hbatch
    else
      -- the run has ended inside the slice
      have hlt := lt_whitespaceRunEnd hend.2.1 hrun h hc
      let ⟨batch, hbatch⟩ ← pushBorrowed batch offset base .whitespace index «end» start «end»
        nofun (started_held hstart hframe hbatch).1 (started_lt hstart hend.1 hlt)
        (started_held hstart hframe hbatch).2
      return some ⟨(«end», batch), hlt, hbatch⟩
  | none =>
    -- we ran out of bytes, update the content and state
    extendContent input index input.stop
    have hstop : index.toNat < input.stop.toNat := by
      rcases hrun with hlt | ⟨_, hfirst, _⟩
      · omega
      · have := CharClass.Input.lt_stop_of_get? hfirst
        omega
    leavePending .whitespace start offset base input.stop batch hframe
      (hbatch.mono hend.1 (Nat.le_of_lt hstop)) (started_lt hstart hend.1 hstop)
      (started_floor hstart hframe)
    return none
termination_by input.stop.toNat - «end».toNat
decreasing_by decreasing_position

/--
Lexes the whitespace run that starts at `index` of the slice,
to be handed over as a token.

Returns the position after the run and the batch with its token, if the run ends inside the
slice. Otherwise, the run is stored, the state becomes `whitespace`, the batch goes back into
the lexer state, and `none` is returned.
-/
def startWhitespace (input : CharClass.Input) (offset : Nat) (base index : USize)
    (batch : Token.Internal.TokenBatch) (hrun : ContinuesWhitespace input index)
    (hframe : Frame floor low offset)
    (hindex : base.toNat ≤ index.toNat) (hbatch : Held floor offset base index batch) :
    LexM H m R E floor low (Option {next : USize × Token.Internal.TokenBatch //
      index.toNat < next.1.toNat ∧ Held floor offset base next.1 next.2}) := do
  let ⟨start, hstart⟩ ← startToken offset base index hframe
  have hstop : index.toNat ≤ input.stop.toNat := by
    have ⟨_, hfirst, _⟩ := hrun
    have := CharClass.Input.lt_stop_of_get? hfirst
    omega
  startWhitespaceFrom input offset base index index start batch hframe hstart
    ⟨hindex, Nat.le_refl _, hstop⟩ (.inr hrun) hbatch

/-- What the loops of `lexNormal` return: a position at or after `index`, and after it if
`index` is below the end of the slice. -/
abbrev Past (input : CharClass.Input) (index : USize) :=
  {next : USize //
    index.toNat ≤ next.toNat ∧ (index.toNat < input.stop.toNat → index.toNat < next.toNat)}

/-- A position past `index` is past every position at or before `index`. -/
@[inline]
def Past.from {input : CharClass.Input} {origin index : USize} (h : origin.toNat ≤ index.toNat)
    (next : Past input index) : Past input origin :=
  ⟨next.1, Nat.le_trans h next.2.1, fun hlt =>
    if hi : index.toNat < input.stop.toNat then Nat.lt_of_le_of_lt h (next.2.2 hi)
    else by have := next.2.1; omega⟩

/-- The type of a token on the fast path: a quoted symbol, whitespace or a simple symbol. -/
@[inline]
def fastCategory (isQuoted emitsWhitespace : Bool) : Token.TokenCategory :=
  if isQuoted then .quotedSymbol else if emitsWhitespace then .whitespace else .unquotedSymbol

theorem fastCategory_ne (isQuoted emitsWhitespace : Bool) :
    fastCategory isQuoted emitsWhitespace ≠ .endOfFile := by
  unfold fastCategory
  split
  · nofun
  · split <;> nofun

/- LEAN: the Rust function loops over the slice with `while let`; here the loop is the
recursion on `index`. Every arm that continues the loop in Rust calls `lexNormalFrom` again
at the new index, which is after `index`. `offset` is the offset of the position `base`, from
which the loop computes the offsets of the positions after it; they stay the same while the
loop runs. `origin` is where the loop started, which the position returned is past; it stays
the same too, so that the recursive call is the last one and the loop takes no stack. The
recursion is encoded as a well-founded one, which for a function this long nests
deeper than the default limit allows. -/
set_option maxRecDepth 2048 in
def lexNormalFrom (input : CharClass.Input) (offset : Nat) (base index : USize)
    (batch : Token.Internal.TokenBatch) (hframe : Frame floor low offset) (hindex : base.toNat ≤
        index.toNat)
    (hbatch : Held floor offset base index batch) (origin : USize)
    (horigin : origin.toNat ≤ index.toNat) : LexM H m R E floor low (Past input origin) := do
  match hget : input.get? index with
  | none =>
    -- we have consumed every byte of the slice
    -- write the locals back before returning
    leave offset base index batch hframe hbatch
    return Past.«from» horigin
      ⟨index, Nat.le_refl _, fun h => absurd h (Nat.not_lt.mpr (stop_le_of_get?_none hget))⟩
  | some c =>
  have := CharClass.Input.toNat_add_one_of_get? hget
  -- A fast path handles the most common token types.
  -- It is determined by one table lookup. If the started token is not on
  -- the fast path, a slower path is taken, again looked up. Arms eagerly
  -- try to complete the token with the whole content borrowed from the slice,
  -- which resets the lexer back to the normal state, so the loop can continue.
  --
  -- Lexing only returns early if eager dispatch is not possible,
  -- typically due to running out of bytes in the slice.

  let after := index + 1
  have hafter : index.toNat < after.toNat := by decreasing_position
  -- Handle the parentheses first as they are numerous and
  -- need no special processing. The closing parenthesis is first
  -- as it forms more clusters.
  if c == byte! ')' then
    if (← getCore).recovers then
      -- saturate to avoid going below zero depth
      -- which would happen with too many closing parentheses
      modifyCore fun core => { core with lexedDepth := core.lexedDepth - 1 }
    let ⟨batch, hbatch⟩ ← pushFast batch offset base .parenClose index after index after true
      nofun hindex hafter hframe hbatch
    return ← lexNormalFrom input offset base after batch hframe
      (by decreasing_position) hbatch origin
      (Nat.le_trans horigin (Nat.le_of_lt hafter))
  if c == byte! '(' then
    if (← getCore).recovers then
      modifyCore fun core => { core with lexedDepth := core.lexedDepth + 1 }
    let ⟨batch, hbatch⟩ ← pushFast batch offset base .parenOpen index after index after true
      nofun hindex hafter hframe hbatch
    return ← lexNormalFrom input offset base after batch hframe
      (by decreasing_position) hbatch origin
      (Nat.le_trans horigin (Nat.le_of_lt hafter))
  -- Handle whitespace and symbols in a fast path.
  let fastEntry := Helpers.fastFlags c
  if fastEntry &&& Helpers.FAST_ON != 0 then
    -- Fast path, compute where the run ends and where the token ends.
    -- For quoted symbols, the token will end after the closing pipe.
    let runEndAt := CharClass.runEnd input after (fastEntry &&& Helpers.FAST_RUN_MASK)
    have : after.toNat ≤ runEndAt.toNat := CharClass.le_runEnd input after _
    let isQuoted := fastEntry &&& Helpers.FAST_PIPE != 0

    -- Check if we need to fall back to state-machine lexing
    -- if we have been asked to emit whitespace and are handling it.
    -- We need to fall back if we have overrun the slice or encountered
    -- a line-feed which needs to update the location line/column.
    let isWhitespace := fastEntry &&& CharClass.RUN_NON_LF_WHITESPACE != 0
    let emitsWhitespace := (← consumesWhitespaceAndComments) && isWhitespace
    if hws : emitsWhitespace && (input.get? runEndAt).all (· == byte! '\n') then
      -- the whitespace token does not end on this line inside the slice
      match ← startWhitespace input offset base index batch
          ⟨c, hget, .inr (Helpers.not_endsRun_of_fastFlags (by
            simp only [emitsWhitespace, isWhitespace, fastEntry, Bool.and_eq_true] at hws
            exact hws.1.2))⟩ hframe hindex hbatch with
      | none =>
        -- we ran out of bytes inside the whitespace
        return Past.«from» horigin
          ⟨input.stop, by decreasing_position, fun _ => by decreasing_position⟩
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
    let isUnfinished := (runEndAt == input.stop || isQuoted) &&
      if isQuoted then input.get? runEndAt != some (byte! '|')
      else fastEntry &&& CharClass.RUN_SIMPLE_SYMBOL != 0
    if hunfinished : isUnfinished then
      -- write the locals back
      storeUnfinishedSymbolRun input fastEntry offset base index after runEndAt batch hframe hindex
        (by decreasing_position) hbatch
      return Past.«from» horigin ⟨runEndAt, by decreasing_position, fun _ => by decreasing_position⟩
    else
    let tokenEnd := if isQuoted then runEndAt + 1 else runEndAt
    have htokenEnd : runEndAt.toNat ≤ tokenEnd.toNat := by
      simp only [tokenEnd]
      split
      · rename_i hquoted
        have hpipe : input.get? runEndAt = some (byte! '|') := by
          simpa [isUnfinished, hquoted] using hunfinished
        rw [CharClass.toNat_add_one_of_lt (CharClass.Input.lt_stop_of_get? hpipe)]
        omega
      · omega
    have hend : index.toNat < tokenEnd.toNat := by decreasing_position

    -- No need to fall back, construct the token: the pipes delimit a quoted
    -- symbol but are not part of its content, any other fast token is its
    -- whole text. The token is on a single line as all fast-lex runs exclude
    -- newlines. Whitespace is only emitted if the consumer wants it.
    let ty := fastCategory isQuoted emitsWhitespace
    let contentStart := if isQuoted then after else index
    let contentStop := if isQuoted then runEndAt else tokenEnd
    let emit := fastEntry &&& Helpers.FAST_EMIT != 0
    -- A token must be delimited by the byte after it,
    -- fall back to the state machine if the delimiter is not found.
    if emit then
      match input.get? tokenEnd with
      | some next =>
        -- the token ended inside the slice: the byte after it must delimit it
        if !Helpers.isDelimiter next then
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
        return Past.«from» horigin ⟨tokenEnd, Nat.le_of_lt hend, fun _ => hend⟩
    -- whitespace needs no delimiter, it is emitted only if the consumer takes it
    let emit := emit || emitsWhitespace
    let ⟨batch, hbatch⟩ ← pushFast batch offset base ty contentStart contentStop index tokenEnd emit
      (fastCategory_ne _ _) hindex hend hframe hbatch
    -- Fast path done, continue normally after the token end.
    return ← lexNormalFrom input offset base tokenEnd batch hframe
      (by decreasing_position) hbatch origin
      (Nat.le_trans horigin (Nat.le_of_lt hend))

  -- Fast path was not taken, use the slow path.
  match hstart : Helpers.startOf c with
  | .lineFeed =>
    if ← consumesWhitespaceAndComments then
      -- the line feed starts a whitespace token
      match ← startWhitespace input offset base index batch
          ⟨c, hget, .inl (Helpers.eq_of_startOf_eq_lineFeed hstart)⟩ hframe hindex hbatch with
      | none =>
        return Past.«from» horigin
          ⟨input.stop, by decreasing_position, fun _ => by decreasing_position⟩
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
    let «end» := CharClass.runEnd input after CharClass.RUN_COMMENT_PLAIN
    have : after.toNat ≤ «end».toNat := CharClass.le_runEnd input after _
    match hbyte : input.get? «end» with
    | some c =>
      have := CharClass.Input.toNat_add_one_of_get? hbyte
      have hnext : index.toNat < («end» + 1).toNat := by decreasing_position
      if c == byte! '\n' then
        -- line feed, we need to mark it
        markLineFeedAt «end»
      -- otherwise a carriage return, which also ends the comment
      -- we have reached the end of the comment, which includes
      -- the byte that ended it but not its semicolon
      -- sink the content if it should be emitted
      let ⟨batch, hbatch⟩ ← if ← consumesWhitespaceAndComments then
          pushBorrowed batch offset base .comment after («end» + 1) tokenStart («end» + 1) nofun
            (started_held hts hframe hbatch).1 (started_lt hts hindex hnext)
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
      have hlt : index.toNat < «end».toNat := by decreasing_position
      leavePending .comment tokenStart offset base «end» batch hframe
        (hbatch.mono hindex (Nat.le_of_lt hlt)) (started_lt hts hindex hlt)
        (started_floor hts hframe)
      return Past.«from» horigin ⟨«end», Nat.le_of_lt hlt, fun _ => hlt⟩
  | .hash =>
    -- base selection
    let ⟨tokenStart, hts⟩ ← startToken offset base index hframe
    let selected := (input.get? after).bind fun c =>
      if c == byte! 'x' then some Helpers.HEXADECIMAL_RUN
      else if c == byte! 'b' then some Helpers.BINARY_RUN
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
        return Past.«from» horigin ⟨after, Nat.le_of_lt hafter, fun _ => hafter⟩
    have hkind : run = Helpers.HEXADECIMAL_RUN ∨ run = Helpers.BINARY_RUN := by
      have ⟨_, _, hselection⟩ := Option.bind_eq_some_iff.mp hrun
      split at hselection
      · exact .inl (Option.some.inj hselection).symm
      · split at hselection
        · exact .inr (Option.some.inj hselection).symm
        · cases hselection
    -- the base has been selected, get a run of its digits
    let start := after + 1
    let afterEnd := CharClass.runEnd input start run.flag
    have : start.toNat ≤ afterEnd.toNat := CharClass.le_runEnd input start _
    have : start.toNat = after.toNat + 1 := by
      have ⟨_, hselection, _⟩ := Option.bind_eq_some_iff.mp hrun
      exact CharClass.toNat_add_one_of_lt (CharClass.Input.lt_stop_of_get? hselection)
    have hlt : index.toNat < afterEnd.toNat := by decreasing_position
    if hend : afterEnd == input.stop then
      -- we ran out of bytes
      -- update the content and the state and return
      extendContent input start afterEnd
      leavePending run.state tokenStart offset base afterEnd batch hframe
        (hbatch.mono hindex (Nat.le_of_lt hlt)) (started_lt hts hindex hlt)
        (started_floor hts hframe)
      return Past.«from» horigin ⟨afterEnd, Nat.le_of_lt hlt, fun _ => hlt⟩
    else
    -- dispatch a token with borrowed content
    -- digit runs must not be empty
    have hwithin : afterEnd.toNat ≤ input.stop.toNat := CharClass.runEnd_le input _ (by
      have ⟨_, hselection, _⟩ := Option.bind_eq_some_iff.mp hrun
      have := CharClass.Input.lt_stop_of_get? hselection
      decreasing_position)
    if (Helpers.Content.borrow input start afterEnd (by decreasing_position) hwithin).size
        (← getCore).tokenContent == 0 then
      leave offset base index batch hframe hbatch
      fail run.emptyError (.mkAtByte afterEnd)
    let next := input.get afterEnd (CharClass.Input.lt_stop_of_ne hwithin hend)
    if !Helpers.isDelimiter next then
      leave offset base index batch hframe hbatch
      failAt .missingDelimiter (afterEnd + 1)
    let ⟨batch, hbatch⟩ ← pushBorrowed batch offset base run.tokenType start afterEnd tokenStart
      afterEnd (DigitRun.tokenType_ne hkind) (started_held hts hframe hbatch).1
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
      return Past.«from» horigin ⟨after, Nat.le_of_lt hafter, fun _ => hafter⟩
    -- determine the run of content bytes
    let afterContentEnd := CharClass.runEnd input after CharClass.RUN_STRING_PLAIN
    have : after.toNat ≤ afterContentEnd.toNat := CharClass.le_runEnd input after _
    -- we can only eagerly borrow if the content is ended by a closing quote
    -- that is definitely not followed by another closing quote
    -- (we cannot borrow a string containing an escape)
    /- LEAN: Rust looks at a two-byte window; here the byte after the closing quote is only
    looked at once the quote is found, so that its position is formed from one below the end
    of the slice. -/
    let closed := match input.get? afterContentEnd with
      | some quote =>
        if quote == byte! '"' then
          let afterQuote := afterContentEnd + 1
          match input.get? afterQuote with
          | some next => if next != byte! '"' then some (afterQuote, next) else none
          | none => none
        else
          none
      | none => none
    match hclosed : closed with
    | some (afterQuote, next) =>
      have : after.toNat < afterQuote.toNat := by
        simp only [closed] at hclosed
        split at hclosed
        · rename_i hquote
          have := CharClass.Input.toNat_add_one_of_get? hquote
          split at hclosed
          · split at hclosed
            · split at hclosed
              · cases hclosed
                omega
              · cases hclosed
            · cases hclosed
          · cases hclosed
        · cases hclosed
      have hlt : index.toNat < afterQuote.toNat := by decreasing_position
      -- definitely closed by a quote not followed by another quote
      -- borrow the string literal content and produce a token
      if !Helpers.isDelimiter next then
        leave offset base index batch hframe hbatch
        failAt .missingDelimiter (afterQuote + 1)
      let ⟨batch, hbatch⟩ ← pushBorrowed batch offset base .string after afterContentEnd
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
      have hlt : index.toNat < afterContentEnd.toNat := by decreasing_position
      leavePending .stringLiteral tokenStart offset base afterContentEnd batch hframe
        (hbatch.mono hindex (Nat.le_of_lt hlt)) (started_lt hts hindex hlt)
        (started_floor hts hframe)
      return Past.«from» horigin ⟨afterContentEnd, Nat.le_of_lt hlt, fun _ => hlt⟩
  | .colon =>
    -- starts a keyword
    let ⟨tokenStart, hts⟩ ← startToken offset base index hframe
    -- get a run of simple-symbol bytes
    let afterEnd := CharClass.runEnd input after CharClass.RUN_SIMPLE_SYMBOL
    have : after.toNat ≤ afterEnd.toNat := CharClass.le_runEnd input after _
    have hlt : index.toNat < afterEnd.toNat := by decreasing_position
    if hend : afterEnd == input.stop then
      -- we ran out of bytes
      -- update the content and state and return
      extendContent input after afterEnd
      leavePending .keyword tokenStart offset base afterEnd batch hframe
        (hbatch.mono hindex (Nat.le_of_lt hlt)) (started_lt hts hindex hlt)
        (started_floor hts hframe)
      return Past.«from» horigin ⟨afterEnd, Nat.le_of_lt hlt, fun _ => hlt⟩
    else
    -- dispatch a token with borrowed content
    -- ensure the keyword is not empty
    have hwithin : afterEnd.toNat ≤ input.stop.toNat :=
      CharClass.runEnd_le input _ (by decreasing_position)
    if (Helpers.Content.borrow input after afterEnd (by decreasing_position) hwithin).size
        (← getCore).tokenContent == 0 then
      leave offset base index batch hframe hbatch
      fail .emptyKeyword (.mkAtByte afterEnd)
    let next := input.get afterEnd (CharClass.Input.lt_stop_of_ne hwithin hend)
    if !Helpers.isDelimiter next then
      leave offset base index batch hframe hbatch
      failAt .missingDelimiter (afterEnd + 1)
    let ⟨batch, hbatch⟩ ← pushBorrowed batch offset base .keyword after afterEnd tokenStart afterEnd
      nofun (started_held hts hframe hbatch).1 (started_lt hts hindex hlt)
      (started_held hts hframe hbatch).2
    -- update the index and continue the loop
    lexNormalFrom input offset base afterEnd batch hframe
      (by decreasing_position) hbatch origin
      (Nat.le_trans horigin (Nat.le_of_lt hlt))
  | .digit =>
    let ⟨tokenStart, hts⟩ ← startToken offset base index hframe
    -- determine the run of digits
    let afterEnd := CharClass.runEnd input after CharClass.RUN_DIGIT
    have : after.toNat ≤ afterEnd.toNat := CharClass.le_runEnd input after _
    have hlt : index.toNat < afterEnd.toNat := by decreasing_position
    -- check that we are not in a leading zero condition,
    -- which is only possible if the first character was zero
    -- and there is a subsequent digit;
    -- it is possible we will not be able to decide it here
    -- if the slice ends with a single zero, so we need to handle that
    -- when lexing digit in the state `numeralOrDecimal`
    if c == byte! '0' && afterEnd > after then
      leave offset base index batch hframe hbatch
      failAt .numeralLeadingZero (after + 1)
    match hnext : input.get? afterEnd with
    | some next =>
      if next == byte! '.' then
        -- a dot starts a fraction, try to do a subsequent run of fraction digits
        let afterFractionEnd := CharClass.runEnd input (afterEnd + 1) CharClass.RUN_DIGIT
        have : (afterEnd + 1).toNat ≤ afterFractionEnd.toNat :=
          CharClass.le_runEnd input _ _
        have := CharClass.Input.toNat_add_one_of_get? hnext
        have hfraction : index.toNat < afterFractionEnd.toNat := by decreasing_position
        if hend : afterFractionEnd == input.stop then
          -- we ran out of bytes
          -- update the content and state and return
          extendContent input index afterFractionEnd
          leavePending .fraction tokenStart offset base afterFractionEnd batch hframe
            (hbatch.mono hindex (Nat.le_of_lt hfraction)) (started_lt hts hindex hfraction)
            (started_floor hts hframe)
          return Past.«from» horigin ⟨afterFractionEnd, Nat.le_of_lt hfraction, fun _ => hfraction⟩
        else
        -- dispatch a decimal token with borrowed content
        -- decimals of the form 7. without any digit in fractional part are disallowed
        have hwithin : afterFractionEnd.toNat ≤ input.stop.toNat :=
          CharClass.runEnd_le input _ (by decreasing_position)
        let last := (Helpers.Content.borrow input index afterFractionEnd (by decreasing_position)
          hwithin).last? (← getCore).tokenContent
        if last.isNone || last == some (byte! '.') then
          leave offset base index batch hframe hbatch
          fail (.expected .fractionDigit) (.mkAtByte afterFractionEnd)
        let following := input.get afterFractionEnd (CharClass.Input.lt_stop_of_ne hwithin hend)
        if !Helpers.isDelimiter following then
          leave offset base index batch hframe hbatch
          failAt .missingDelimiter (afterFractionEnd + 1)
        let ⟨batch, hbatch⟩ ← pushBorrowed batch offset base .decimal index afterFractionEnd
          tokenStart afterFractionEnd nofun (started_held hts hframe hbatch).1
          (started_lt hts hindex hfraction) (started_held hts hframe hbatch).2
        -- update the index and continue the loop
        lexNormalFrom input offset base afterFractionEnd batch hframe
          (by decreasing_position) hbatch origin
          (Nat.le_trans horigin (Nat.le_of_lt hfraction))
      else
        -- the numeral is not actually a decimal and ends
        -- dispatch a numeral token with borrowed content
        if !Helpers.isDelimiter next then
          leave offset base index batch hframe hbatch
          failAt .missingDelimiter (afterEnd + 1)
        let ⟨batch, hbatch⟩ ← pushBorrowed batch offset base .numeral index afterEnd tokenStart
          afterEnd nofun (started_held hts hframe hbatch).1 (started_lt hts hindex hlt)
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
      return Past.«from» horigin ⟨afterEnd, Nat.le_of_lt hlt, fun _ => hlt⟩
  | .other | .whitespace | .parenOpen | .parenClose | .symbol | .pipe =>
    -- can actually only be other (resulting in unexpected character),
    -- as the other arms have already been handled in the fast path.
    let _ ← startToken offset base index hframe
    leave offset base index batch hframe hbatch
    failAt .unexpectedCharacter after
termination_by input.stop.toNat - index.toNat
decreasing_by all_goals decreasing_position

/- LEAN: Rust's `lex_normal` gets the rest of the slice, whose first byte is at the lexer's
offset. Here `start` is the position of the step, the lexer's `base`; the loop takes its offset
as that of `base` moved on to `start`, so that the proofs know that the positions it reads are
at or after the position of its offset. -/
/-- Lexes from `start`, which is below the end of the input, in the normal state, returning the
position up to which the input was consumed, which is after `start`. -/
def lexNormal (input : CharClass.Input) (start : USize) (hstart : start.toNat < input.stop.toNat) :
    LexM H m R E floor low {next : USize // start.toNat < next.toNat} := do
  -- use locals for variables commonly used on the fast path
  let ⟨(offset, base, batch), hframe, hbatch, hfloor⟩ ←
    modifyGetThe {c : LexerCore // c.Bound floor low} fun c =>
      ((⟨(c.val.offset, c.val.base, c.val.batch),
          ⟨c.property.1, fun p hp => (c.property.2 p hp).1⟩, c.val.batchEnded,
          fun p hp => (c.property.2 p hp).2.2⟩ :
          {x : Nat × USize × Token.Internal.TokenBatch // Frame floor low x.1 ∧
              x.2.2.lastEnd ≤ x.1 ∧
            ∀ p, floor = some p → x.2.2.StartsFrom p}),
        ⟨{ c.val with
            batch := default
            batchEnded := Token.Internal.TokenBatch.lastEnd_default ▸ Nat.zero_le _ },
          ⟨c.property.1, fun p hp =>
            ⟨(c.property.2 p hp).1, (c.property.2 p hp).2.1,
                Token.Internal.TokenBatch.startsFrom_default
                p⟩⟩⟩)
  let offset := offset + (start - base).toNat
  let ⟨next, hnext⟩ ← lexNormalFrom input offset start start batch
    ⟨Nat.le_trans hframe.1 (Nat.le_add_right _ _),
      fun p hp => Nat.le_trans (hframe.2 p hp) (Nat.le_add_right _ _)⟩ (Nat.le_refl _)
    ⟨by simp only [USize.sub_self, USize.toNat_zero, Nat.add_zero]
        exact Nat.le_trans hbatch (Nat.le_add_right _ _), hfloor⟩ start (Nat.le_refl _)
  return ⟨next, hnext.2 hstart⟩

/- LEAN: each of the following steps lexes the input from `start`, where Rust's step gets the
rest of the slice; a position that is 0 in Rust is `start` here, and a step returns the
position up to which it has consumed the input, where Rust returns the number of bytes, with
the proof that it is at or after `start`. Each of them lexes on the token in progress, which
starts at `tokenStart`, before the step's offset; `base` is the position of that offset. -/

def lexFractionFrom (input : CharClass.Input) (start : USize) (tokenStart : Span.Location)
    (base : USize)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // start.toNat ≤ next.toNat} := do
  -- find the first byte in the remainder that is not a digit
  let «end» := CharClass.runEnd input start CharClass.RUN_DIGIT
  -- extend the token from slice
  extendContent input start «end»
  if hlt : «end» < input.stop then
    -- we have successfully consumed the fraction, finish the decimal
    finishDecimal (.mkAtByte «end») (some (input.get «end» (USize.lt_iff_toNat_lt.mp hlt)))
      tokenStart base h
    setNormal
  else
    -- we ran out of bytes for now
    setTokenState .fraction tokenStart h
  return ⟨«end», CharClass.le_runEnd input start _⟩

def lexNumeralOrDecimal (input : CharClass.Input) (start : USize) (tokenStart : Span.Location)
    (base : USize) (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // start.toNat ≤ next.toNat} := do
  -- find the first byte that is not a digit
  let index := CharClass.runEnd input start CharClass.RUN_DIGIT
  have : start.toNat ≤ index.toNat := CharClass.le_runEnd input start _

  -- check that we are not in a leading zero condition
  -- this could not have been done when starting the numeral/decimal
  -- since just a single '0' is allowed

  -- as we emplace the first digit in the normal state,
  -- it suffices for the leading zero condition that
  -- 1. at least one additional digit has been consumed
  -- 2. the content lexed previously is exactly "0"
  let content := (← getCore).tokenContent
  let isZero :=
    if h : content.len = 1 then content.bytes[0]'(by have := content.fits; omega) == byte! '0'
    else false
  if index > start && isZero then
    failAt .numeralLeadingZero (start + 1)

  -- extend the token from slice
  extendContent input start index

  match hnext : input.get? index with
  | some next =>
    if next == byte! '.' then
      -- decimal, the next character will start fraction
      -- add the dot and immediately start lexing the fraction after it
      pushContent (byte! '.')
      have := CharClass.Input.toNat_add_one_of_get? hnext
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

def lexBaseSelection (input : CharClass.Input) (start : USize)
    (hstart : start.toNat < input.stop.toNat) (tokenStart : Span.Location)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // start.toNat ≤ next.toNat} := do
  let c := input.get start hstart
  if c == byte! 'x' then
    setTokenState .hexadecimal tokenStart h
  else if c == byte! 'b' then
    setTokenState .binary tokenStart h
  else
    failAt (.expected .base) (start + 1)
  return ⟨start + 1, by rw [CharClass.toNat_add_one_of_lt hstart]; omega⟩

/-- Lexes a digit run, either hexadecimal or binary. -/
def lexDigitRun (input : CharClass.Input) (start : USize) (run : Helpers.DigitRun)
    (tokenStart : Span.Location) (base : USize)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // start.toNat ≤ next.toNat} := do
  -- find the first byte that is not allowed in the run
  let index := CharClass.runEnd input start run.flag
  -- extend the token from slice
  extendContent input start index
  if hlt : index < input.stop then
    -- we have successfully consumed the digit run, finish it
    finishDigitRun run (.mkAtByte index) (some (input.get index (USize.lt_iff_toNat_lt.mp hlt)))
      tokenStart base h
    setNormal
  return ⟨index, CharClass.le_runEnd input start _⟩

/- LEAN: the Rust loops keep the rest of the slice and the number of bytes consumed from it;
here the loops keep the position `consumed` in the input, so a position in the rest in Rust
is `consumed` plus it here. The loops are shown to end as `lexNormalFrom` is. Where a loop
moves `consumed` on before its run, the position is kept with the proof that it is not
before the one the call started from, which the code after the move is shown to end by. -/

/--
Lexes the string literal in the legacy 2.0 mode.

The legacy 2.0 mode has two backslash escapes, \" and \\.
There are no other escapes.
-/
/- LEAN: `origin` is where the step started, as at `lexWhitespace`. -/
def lexStringLiteralLegacy (input : CharClass.Input) (consumed origin : USize)
    (horigin : origin.toNat ≤ consumed.toNat) (tokenStart : Span.Location)
    (base : USize) (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // origin.toNat ≤ next.toNat} := do
  let some ⟨first, hfirst⟩ := (input.get? consumed).attach
    | return ⟨consumed, horigin⟩
  have := CharClass.Input.toNat_add_one_of_get? hfirst
  let mut consumed : { position : USize // consumed.toNat ≤ position.toNat } :=
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
  let index := CharClass.runEndAll input consumed (CharClass.RUN_STRING_PLAIN |||
      CharClass.RUN_QUOTED_PLAIN)
  have : consumed.1.toNat ≤ index.toNat := CharClass.le_runEndAll input _ _
  have := consumed.2

  let some ⟨c, hc⟩ := (input.get? index).attach
    | do
      -- extend the content with the rest
      extendContent input consumed input.stop
      -- we have nothing more to consume, return
      return ⟨input.stop, by have := CharClass.Input.lt_stop_of_get? hfirst; omega⟩

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
  have := CharClass.Input.toNat_add_one_of_get? hc
  lexStringLiteralLegacy input (index + 1) origin (by simp +zetaDelta only at *; omega)
    tokenStart base h
termination_by input.stop.toNat - consumed.toNat
decreasing_by decreasing_position

/-- Lexes the string literal. -/
def lexStringLiteralFrom (input : CharClass.Input) (consumed origin : USize)
    (horigin : origin.toNat ≤ consumed.toNat) (tokenStart : Span.Location)
    (base : USize) (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // origin.toNat ≤ next.toNat} := do
  let some ⟨first, hfirst⟩ := (input.get? consumed).attach
    | return ⟨consumed, horigin⟩
  have := CharClass.Input.toNat_add_one_of_get? hfirst
  let mut consumed : { position : USize // consumed.toNat ≤ position.toNat } :=
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
  let index := CharClass.runEnd input consumed CharClass.RUN_STRING_PLAIN
  have : consumed.1.toNat ≤ index.toNat := CharClass.le_runEnd input _ _
  have := consumed.2

  match hc : input.get? index with
  | some c =>
    have := CharClass.Input.toNat_add_one_of_get? hc
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
    extendContent input consumed input.stop
    -- we have nothing more to consume, return
    return ⟨input.stop, by have := CharClass.Input.lt_stop_of_get? hfirst; omega⟩
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals decreasing_position

/-- Lexes the string literal. -/
def lexStringLiteral (input : CharClass.Input) (start : USize) (tokenStart : Span.Location)
    (base : USize)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // start.toNat ≤ next.toNat} := do
  if (← getCore).version == .v2_0 then
    -- in 2.0 mode, the string literals are lexed differently,
    -- hand over to the legacy lexing function
    lexStringLiteralLegacy input start start (Nat.le_refl _) tokenStart base h
  else
    lexStringLiteralFrom input start start (Nat.le_refl _) tokenStart base h

def lexSimpleSymbol (input : CharClass.Input) (start : USize) (tokenStart : Span.Location)
    (base : USize)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // start.toNat ≤ next.toNat} := do
  -- find the first byte that is not a simple symbol
  let index := CharClass.runEnd input start CharClass.RUN_SIMPLE_SYMBOL
  -- extend the token from slice
  extendContent input start index
  if hlt : index < input.stop then
    -- we have successfully consumed the symbol, finish it
    expectDelimiter (input.get index (USize.lt_iff_toNat_lt.mp hlt)) index
    finishSimpleSymbol (.mkAtByte index) tokenStart base h
    setNormal
  return ⟨index, CharClass.le_runEnd input start _⟩

/- LEAN: `origin` is where the step started, as at `lexWhitespace`. -/
def lexQuotedSymbol (input : CharClass.Input) (consumed origin : USize)
    (horigin : origin.toNat ≤ consumed.toNat)
    (hconsumed : consumed.toNat ≤ input.stop.toNat) (tokenStart : Span.Location)
    (base : USize) (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // origin.toNat ≤ next.toNat} := do
  -- find the first byte that is not a quoted symbol
  let index := CharClass.runEnd input consumed CharClass.RUN_QUOTED_PLAIN
  have : consumed.toNat ≤ index.toNat := CharClass.le_runEnd input _ _

  -- inspect the problematic byte
  match hc : input.get? index with
  | some c =>
    have := CharClass.Input.toNat_add_one_of_get? hc
    let afterSlicePosition := index + 1
    if c == byte! '|' then
      -- end of quoted symbol, extend its content
      extendContent input consumed index
      -- the byte after the pipe must delimit the token before it is sunk
      match input.get? afterSlicePosition with
      | some next =>
        expectDelimiter next afterSlicePosition
        sinkStored .quotedSymbol (.mkAtByte afterSlicePosition) tokenStart base h
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
    extendContent input consumed input.stop
    return ⟨input.stop, Nat.le_trans horigin hconsumed⟩
termination_by input.stop.toNat - consumed.toNat
decreasing_by decreasing_position

def lexKeyword (input : CharClass.Input) (start : USize) (tokenStart : Span.Location) (base : USize)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // start.toNat ≤ next.toNat} := do
  -- find the first byte that is not simple-symbol-like
  let index := CharClass.runEnd input start CharClass.RUN_SIMPLE_SYMBOL

  -- extend the token from slice
  extendContent input start index

  if hlt : index < input.stop then
    -- we have successfully consumed the keyword, finish it
    finishKeyword (.mkAtByte index) (some (input.get index (USize.lt_iff_toNat_lt.mp hlt)))
      tokenStart base h
    setNormal
  return ⟨index, CharClass.le_runEnd input start _⟩

def lexQuotedSymbolClosed (input : CharClass.Input) (start : USize)
    (hstart : start.toNat < input.stop.toNat) (tokenStart : Span.Location)
    (base : USize) (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // start.toNat ≤ next.toNat} := do
  -- we expect a token delimiter to follow the closing pipe
  expectDelimiter (input.get start hstart) start
  -- all good, produce the quoted symbol token
  sinkStored .quotedSymbol (.mkAtByte start) tokenStart base h
  -- the delimiter is not consumed
  setNormal
  return ⟨start, Nat.le_refl _⟩

/- LEAN: the loop of `lex_whitespace` is the recursion on `start`, shown to end as
`lexNormalFrom` is. `origin` is where the step started, which the position returned is at or
after; it stays the same while the loop runs, so that the recursive call is the last one. -/
def lexWhitespace (input : CharClass.Input) (start origin : USize)
    (horigin : origin.toNat ≤ start.toNat)
    (hstart : start.toNat ≤ input.stop.toNat) (tokenStart : Span.Location) (base : USize)
    (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // origin.toNat ≤ next.toNat} := do
  -- we know that the consumer is interested in the whitespace
  -- as it would otherwise be immediately discarded instead
  -- of the state change
  -- find the first byte that is not non-LF whitespace
  let index := CharClass.runEnd input start CharClass.RUN_NON_LF_WHITESPACE
  have : start.toNat ≤ index.toNat := CharClass.le_runEnd input _ _
  -- inspect the problematic byte
  match hc : input.get? index with
  | some c =>
    have := CharClass.Input.toNat_add_one_of_get? hc
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
    extendContent input start input.stop
    return ⟨input.stop, by omega⟩
termination_by input.stop.toNat - start.toNat
decreasing_by decreasing_position

def lexComment (input : CharClass.Input) (start : USize) (hstart : start.toNat ≤ input.stop.toNat)
    (tokenStart : Span.Location) (base : USize) (h : Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // start.toNat ≤ next.toNat} := do
  -- run until comment end
  let index := CharClass.runEnd input start CharClass.RUN_COMMENT_PLAIN
  have : start.toNat ≤ index.toNat := CharClass.le_runEnd input _ _
  match hc : input.get? index with
  | none =>
    -- the comment continues; if we are producing comments,
    -- extend the content from the whole slice
    if ← consumesWhitespaceAndComments then
      extendContent input start input.stop
    -- remain in comment state
    return ⟨input.stop, hstart⟩
  | some c =>

  -- the comment has ended, either by CR or LF
  -- if it ended by LF, we must mark it
  if c == byte! '\n' then
    markLineFeedAt index

  let afterCommentEnd := index + 1
  have := CharClass.Input.toNat_add_one_of_get? hc

  if ← consumesWhitespaceAndComments then
    -- we need to produce the comment token
    -- extend the comment content and finish the token
    extendContent input start afterCommentEnd
    sinkStored .comment (.mkAtByte afterCommentEnd) tokenStart base h

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
def afterStep (input : CharClass.Input) (start : USize) (hstart : start.toNat < input.stop.toNat)
    (next : {next : USize // start.toNat ≤ next.toNat}) :
    LexM H m R E floor low {next : USize // start.toNat < next.toNat} :=
  if h : start.toNat < next.1.toNat then pure ⟨next.1, h⟩ else lexNormal input start hstart

/- LEAN: Rust's step reads the state from the lexer; here the state, the token start and the
position of the lexer's offset are given, as the loop over the slice read them, with what the
lexer state says of them. -/
/--
Lexes the input from `start`, which is below its end, in the state, returning the position up
to which the input was consumed, which is after `start`.
-/
def lexStep (input : CharClass.Input) (start : USize) (hstart : start.toNat < input.stop.toNat)
    (state : Helpers.LexerState) (tokenStart : Span.Location) (base : USize)
    (hpending : state = .normal ∨ Started floor low tokenStart) :
    LexM H m R E floor low {next : USize // start.toNat < next.toNat} := do
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
      (← lexBaseSelection input start hstart tokenStart (h.resolve_left nofun))
  | .hexadecimal, h =>
    afterStep input start hstart
      (← lexDigitRun input start Helpers.HEXADECIMAL_RUN tokenStart base
        (h.resolve_left nofun))
  | .binary, h =>
    afterStep input start hstart
      (← lexDigitRun input start Helpers.BINARY_RUN tokenStart base (h.resolve_left nofun))
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
      (← lexComment input start (Nat.le_of_lt hstart) tokenStart base (h.resolve_left nofun))
  | .whitespace, h =>
    afterStep input start hstart
      (← lexWhitespace input start start (Nat.le_refl _) (Nat.le_of_lt hstart) tokenStart base
        (h.resolve_left nofun))
  | .quotedSymbolClosed, h =>
    afterStep input start hstart
      (← lexQuotedSymbolClosed input start hstart tokenStart base (h.resolve_left nofun))

/-- How lexing a slice from a position ends. -/
inductive SliceExit (R E : Type) (floor : Option Nat) where
  /-- The batch was handed over: the result to return. -/
  | done (result : Except (Failure E) (ControlFlow R))
  /-- The consumer stopped at the location, which is after the floor. -/
  | stopped (stop : Stop R) (location : Span.Location)
    (after : ∀ p, floor = some p → p < location.offset)

/- LEAN: the loop of `lex_slice_inner`, up to the first stop of the consumer, which the loop
below acts on. `position` is where the part of the input not lexed yet starts, the lexer's
base, and `fnResult` the result to return once the batch is handed over. The lexer state is
passed along by hand, with the floor (see `Interrupted`). The loop ends as every step consumes a
byte (see `lexStep`), and a lexical error is met at most once before the batch is handed over:
then the loop flushes, and a flush either ends the loop or stops it. -/
def lexSliceRun (input : CharClass.Input) (position : USize)
    (fnResult : Except (Failure E) (ControlFlow R)) (core : {c : LexerCore // c.Bound floor 0}) :
    StateT H m (SliceExit R E floor × {c : LexerCore // c.Bound floor 0}) := do
  let failed := match fnResult with
    | .error _ => true
    | .ok _ => false
  if hflush : position ≥ input.stop || failed then
    -- hand over the batch
    let (flushed, core) ← (flushBatch (m := m) (R := R) (E := E)).run.run core
    match flushed with
    | .ok () =>
      -- we are done
      return (.done fnResult, core)
    | .error interrupted =>
      match interrupted with
      | { result := .ok stop, location, stopAfter, .. } =>
        return (.stopped stop location fun p hp => stopAfter p hp stop rfl, core)
      | { result := .error cause, span, location, .. } =>
        /- LEAN: Rust's loop makes another pass, which hands over the batch, empty now; here
        the error is returned at once. -/
        return (.done (.error { cause, span, location }), core)
  else
    have hposition : position.toNat < input.stop.toNat := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hflush
      have := hflush.1
      simp only [ge_iff_le, USize.le_iff_toNat_le] at this
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
      | { result := .ok stop, location, stopAfter, .. } =>
        return (.stopped stop location fun p hp => stopAfter p hp stop rfl, core)
      | { result := .error cause, span, location, .. } =>
        -- make sure the tokens before the error get handed over
        lexSliceRun input position (.error { cause, span, location }) core
termination_by (input.stop.toNat - position.toNat, match fnResult with | .ok _ => 1 | .error _ => 0)
decreasing_by
  · apply Prod.Lex.left
    omega
  · apply Prod.Lex.right
    cases fnResult <;> simp_all +zetaDelta

/- LEAN: the loop over the stops of the consumer in the slice. Every stop goes back to the end
of a token the consumer took, which is after the floor (see `Interrupted`): at or after the
start of the slice, and after the last relex or break in the slice, so that the loop ends.
`floor` is the offset before the first byte of the slice at first, and the location of the last
relex or break after it; the lexer state is passed along by hand, and the other arguments are
those of `lexSliceRun`, with `held`, the result the consumer broke with in the slice, if it
did. -/
/--
Lexes the slice from `position` on, going back to the end of the last token the consumer took
at each of its stops: to relex there, or after a break, to go on lexing what follows the held
result, as trailing input. A request to discard ends the lexing, with the location in
`discardedFrom`: the caller discards the rest of the slice.

Returns the result the consumer broke with in the slice, if it did, and the lexer state.
-/
def lexSliceFrom (input : CharClass.Input) (initialOffset : Nat) (floor : Nat)
    (hfloor : initialOffset ≤ floor + 1) (position : USize)
    (fnResult : Except (Failure E) (ControlFlow R)) (held : Option (Span.Located R))
    (core : {c : LexerCore // c.Bound (some floor) 0}) :
    StateT H m (Except (Failure E) (Option (Span.Located R)) × LexerCore) := do
  let (exit, core) ← lexSliceRun input position fnResult core
  match exit with
  | .done result => return (result.map fun _ => held, core.val)
  | .stopped stop location after =>
    -- every handed-over token ends in this slice
    -- so the location is at or after the initial offset
    have hlocation : initialOffset ≤ location.offset := by
      have := after floor rfl
      omega
    let resumed := location.offset - initialOffset
    let position := input.start + USize.ofNat resumed
    let core := core.val.resumeAt location position
    match stop with
    | .relex =>
      if hresumed : resumed < input.stop.toNat - input.start.toNat then
        -- everything up to the position was already consumed
        -- continue from there
        lexSliceFrom input initialOffset location.offset (Nat.le_succ_of_le hlocation)
          position (.ok .continue) held ⟨core, core.bound_resumeAt location position⟩
      else
        /- LEAN: the location is at the end of the slice, where Rust's loop ends, as no bytes
        are left; the batch was handed over. -/
        return (.ok held, core)
    | .finished result =>
      -- the consumer is done: hold its result, which the end of the input confirms,
      -- and go on lexing the rest of the slice, which is trailing input
      let held := some (Span.Located.Internal.new result location)
      let core := { core with holding := true }
      if hresumed : resumed < input.stop.toNat - input.start.toNat then
        lexSliceFrom input initialOffset location.offset (Nat.le_succ_of_le hlocation)
          position (.ok .continue) held ⟨core, core.bound_resumeAt location position⟩
      else
        return (.ok held, core)
    | .discarded result =>
      -- the rest of the input is discarded from the location, the rest of the slice by the
      -- caller; if the consumer is done, its result is held
      let core := { core with discardedFrom := some location }
      match result with
      | some result =>
        return (.ok (some (Span.Located.Internal.new result location)),
          { core with holding := true })
      | none => return (.ok held, core)
termination_by input.stop.toNat - input.start.toNat + 1 - (floor + 1 - initialOffset)
decreasing_by
  all_goals
    have := after floor rfl
    omega

/-- Lexes the slice, returning the result the consumer broke with in it, if it did. -/
def lexSliceInner (input : CharClass.Input) :
    InnerM H m (Except (Failure E) (Option (Span.Located R))) := fun c =>
  let initialOffset := c.offset
  -- the slice starts at the lexer's offset,
  -- and the tokens borrowed from it have their contents in its array
  /- LEAN: the batch starts empty, as Rust's, which is a local of the call, does; it is empty
  already, as lexing returns with it handed over. -/
  let batch := c.batch
  let c :=
      { c with batch := default, batchEnded := Token.Internal.TokenBatch.lastEnd_default ▸
          Nat.zero_le _ }
  let c : LexerCore := { c with
    base := input.start, batch := { batch.clear initialOffset with bytes := input.bytes }
    batchEnded := Nat.le_of_eq (Token.Internal.TokenBatch.lastEnd_clear _ _) }
  -- the floor is just before the slice, and every token handed over ends after it: one begun in
  -- an earlier slice ends at the slice's start or later, one begun in this slice ends after its
  -- first byte. At offset 0 the floor is 0, as `Nat` subtraction stops there; no token begins
  -- earlier, and one begun here ends above 0. A token in progress starts before the offset.
  have hpending :
      c.state = .normal ∨ initialOffset - 1 ≤ c.tokenStart.offset ∨ initialOffset - 1 < c.offset :=
    c.tokenStarted.imp_right fun h => .inr (Nat.sub_one_lt_of_lt h)
  lexSliceFrom input initialOffset (initialOffset - 1) (by omega) input.start (.ok .continue)
    none
    ⟨c, ⟨Nat.zero_le _, fun p hp => by
      cases hp
      exact ⟨Nat.sub_le _ _, hpending, fun _ h => absurd h (Nat.not_lt_zero _)⟩⟩⟩

/-- Resets the lexer to the initial state, including the location and version. -/
def reset : InnerM H m Unit :=
  modifyThe LexerCore fun c =>
    { c with
      version := c.initialVersion
      state := .normal
      discardedFrom := none
      holding := false
      consumedDepth := 0
      lexedDepth := 0
      recoveryState := none
      tokenStart := Span.Location.initial
      tokenContent := c.tokenContent.clear
      offset := 0
      line := 0
      base := 0
      lineStart := 0
      /- LEAN: not in Rust: the batch, which was handed over, is empty already; its origin
      is set to the offset. -/
      batch := c.batch.clear 0
      tokenStarted := .inl rfl
      batchEnded := Nat.le_of_eq (Token.Internal.TokenBatch.lastEnd_clear _ _) }

/- LEAN: the pending token is finished as a step does: it starts before the lexer's offset,
which is that of the position 0 at the end of the input. -/
def lexEofInner : InnerM H m (Except (Failure E) (ControlFlow R)) := fun c => do
  -- EOF is a token delimiter, we need to produce the token
  -- that waits for a delimiter if there is any
  -- there is no input at the end of the file, positions are relative to the offset
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
      sinkStored .quotedSymbol Helpers.TokenEnd.EOF tokenStart 0
        ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .fraction, h =>
      finishDecimal Helpers.TokenEnd.EOF none tokenStart 0
          ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .numeralOrDecimal, h =>
      finishNumeral Helpers.TokenEnd.EOF tokenStart 0
          ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .hexadecimal, h =>
      finishDigitRun Helpers.HEXADECIMAL_RUN Helpers.TokenEnd.EOF none tokenStart 0
        ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .binary, h =>
      finishDigitRun Helpers.BINARY_RUN Helpers.TokenEnd.EOF none tokenStart 0
        ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .baseSelection, _ =>
      -- hash without selection following it
      fail (.expected .base) Helpers.TokenEnd.EOF
    | .stringLiteral, _ | .stringLiteralBackslashEscape, _ =>
      -- we are still within the string literal
      -- forbidden as the literal must be totally enclosed by double quotes
      fail .unclosedStringLiteral Helpers.TokenEnd.EOF
    | .stringLiteralDoubleQuote, h =>
      -- string literal has ended by the previous character,
      -- a quote directly before the end of the file
      -- this works both for 2.0 and 2.5+
      finishStringLiteral Helpers.TokenEnd.EOF tokenStart 0
          ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .simpleSymbol, h =>
      finishSimpleSymbol Helpers.TokenEnd.EOF tokenStart 0
          ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .keyword, h =>
      finishKeyword Helpers.TokenEnd.EOF none tokenStart 0
          ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .quotedSymbol, _ =>
      -- EOF forbidden as the symbol must be totally enclosed by pipes
      fail .unclosedQuotedSymbol Helpers.TokenEnd.EOF
    | .whitespace, h =>
      -- we can only be in this state if the consumer wants the
      -- whitespace to be emitted, so sink it
      sinkStored .whitespace Helpers.TokenEnd.EOF tokenStart 0
        ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
    | .comment, h => do
      -- only produce the comment if the consumer wants it
      if ← consumesWhitespaceAndComments then
        sinkStored .comment Helpers.TokenEnd.EOF tokenStart 0
          ⟨h.resolve_left nofun, fun _ h => nomatch h⟩
  let step : LexM H m R E none offset Unit := do
    -- if we were told to relex, treat it as a normal continuation,
    -- as there is nothing to relex (we are at the end of input);
    -- the end of the input is handed over also while discarding
    tryCatch pending fun interrupted =>
      match interrupted.result with
      | .ok .relex => pure ()
      | .ok (.discarded none) =>
        -- the consumer had the rest discarded at the token: the lexer discards from there, and
        -- hands the end of the input over as it does while discarding
        modifyCore fun c => { c with discardedFrom := some interrupted.location }
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
    | .error cause =>
      return (.error { cause, span := interrupted.span, location := interrupted.location },
        core.val)
    | .ok .relex | .ok (.discarded none) =>
      -- we were asked to relex or to discard, but the file is ending anyway
      return (.ok .continue, core.val)
    | .ok (.finished result) | .ok (.discarded (some result)) =>
      -- the consumer is done with the input
      -- the lexer will be reset outside
      return (.ok (.break result), core.val)

/-- Executes an inner lexer step, adding the break location to its result. -/
def executeStep (step : InnerM H m (Except (Failure E) (ControlFlow R))) :
    InnerM H m (Except (Failure E) (ControlFlow (Span.Located R))) := do
  match ← step with
  | .ok .continue => return .ok .continue
  | .ok (.break result) =>
    -- add the break location: the lexer is at the last consumed token
    let location := (← getThe LexerCore).currentLocation
    return .ok (.break (Span.Located.Internal.new result location))
  | .error failure => return .error failure

/- LEAN: a lexer that stops at its first error is not given back by a call that fails, so it
needs no failure mode to refuse further calls, unlike Rust. -/
/--
Turns the failure into the error to return.

A recovering lexer makes the consumer abandon its current work and skips bytes until
recovery is made.
-/
def failCall (abandon : Span.Location → StateT H m Unit) (failure : Failure E) (atEnd : Bool) :
    InnerM H m (Error.LexError E) := do
  if !(← getThe LexerCore).recovers then
    return Error.LexError.Internal.new failure.cause failure.span none

  -- a value is confirmed only at the end of the input: an error after a break drops it
  modifyThe LexerCore fun c => { c with holding := false }

  let skip : Helpers.RecoveryState := if atEnd then
      -- the input has ended, nothing is left to skip
      .end
    else
      -- start recovering from inside the string or quoted symbol if necessary
      match failure.cause with
      | .lexical kind => match kind with
        | .forbiddenCharInString => .string
        | .backslashInQuotedSymbol | .forbiddenCharInQuotedSymbol => .quotedSymbol
        | _ => .plain
      -- the consumer fails at the boundary after a whole token
      | .consumer _ => .boundary

  -- start recovering from the given failure location
  -- there is no slice being lexed, so its position is zero
  modifyThe LexerCore (·.resumeAt failure.location 0)
  abandon failure.location
  modifyThe LexerCore fun c => { c with recoveryState := some skip }
  return Error.LexError.Internal.new failure.cause failure.span (some failure.location)

/-- What skipping goes through, see `skipBytes`. -/
structure Skipping where
  skip : Helpers.RecoveryState
  depth : Nat
  line : Nat
  lineStart : Nat

/- LEAN: the loop of Rust's `skip_slice` over the bytes, as a recursion on `index` that is shown
to end; it works on the values it changes and leaves the lexer state to `skipSlice`.
`offset` is the stream offset of the first byte. -/
/--
Skips the bytes from `index` on while recovering.

Returns the position where the recovery was made, if it was, and the skipping state there
or at the end of the bytes.
-/
def skipBytes (bytes : ByteSlice) (legacy : Bool) (offset index : Nat)
    (skipping : Skipping) : Option Nat × Skipping :=
  if h : index < bytes.size then
    let c := bytes[index]
    -- the state after the byte, or the position where the recovery was made
    let next : Sum (Nat × Skipping) Skipping := match skipping.skip with
      | .end | .boundary | .plain =>
        if c == byte! '"' then .inr { skipping with skip := .string }
        else if c == byte! '|' then .inr { skipping with skip := .quotedSymbol }
        else if Helpers.isDelimiter c && skipping.depth == 0 then
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

Returns the position in the slice where the recovery was made,
or returns `none` if it has not yet been done.
-/
def skipSlice (slice : ByteSlice) (skip : Helpers.RecoveryState) : InnerM H m (Option Nat) := do
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

/-- The number of bytes of a chunk of a slice too large for the positions of the lexer. -/
def CHUNK_SIZE : Nat := 2 ^ 31

/-- Lexes the slice, which ends below `USize.size`, from the position after the bytes skipped
while recovering. -/
def lexFitting (abandon : Span.Location → StateT H m Unit) (slice : ByteSlice)
    (h : slice.stop < USize.size) : InnerM H m (Except (Error.LexError E)
    (Option (Span.Located R))) := do
  -- execute the inner lexing step, and fail on error
  match ← lexSliceInner (CharClass.Input.ofSlice slice h) with
  | .ok held => return .ok held
  | .error failure => return .error (← failCall abandon failure false)

/-- A part of a slice that ends below `USize.size` ends below it too. -/
theorem stop_slice_lt {slice : ByteSlice} (h : slice.stop < USize.size) (k : Nat) :
    (slice.slice k).stop < USize.size := by
  have := slice.start_le_stop
  have hs : slice.size = slice.stop - slice.start := rfl
  unfold ByteSlice.slice
  dsimp only
  split
  · split
    · show slice.start + min slice.size slice.size < USize.size
      omega
    · show slice.start + min slice.size slice.size < USize.size
      omega
  · show slice.start < USize.size
    omega

/- LEAN: the consumer's recovery methods are passed in, those of `LexRecovery`; they are only
called by a recovering lexer. -/
/--
Lexes the slice, which ends below `USize.size`, or discards it if the consumer has had the rest
discarded.

Returns the result the consumer broke with in the slice, if it did.
-/
def lexSliceFitting (abandon recover : Span.Location → StateT H m Unit) (slice : ByteSlice)
    (h : slice.stop < USize.size) : InnerM H m (Except (Error.LexError E)
    (Option (Span.Located R))) := do
  if (← getThe LexerCore).discardedFrom.isSome then
    -- we are discarding bytes
    -- pretend that we lexed everything we were given
    return .ok none

  -- a recovering lexer must skip until out of the root-level expression
  -- in which the error occurred
  match (← getThe LexerCore).recoveryState with
  | some skip =>
    /- LEAN: Rust panics if the slice is not empty, as the end of the input raised the error.
    Only a `PendingEof` holds a lexer in this state, and it offers no `lexSlice`. -/
    if skip == .end then
      -- the input has ended, there is nothing to skip to
      return .ok none
    let some skipped ← skipSlice slice skip
      -- the whole slice was skipped
      | return .ok none
    -- the lexing goes on from here, tell the consumer before any token
    modifyThe LexerCore fun c => { c with recoveryState := none, lexedDepth := c.consumedDepth }
    recover (← getThe LexerCore).currentLocation
    lexFitting abandon (slice.slice skipped) (stop_slice_lt h skipped)
  | none => lexFitting abandon slice h

/-- The end of the view of a whole array is its size. -/
theorem stop_toByteSlice (bytes : ByteArray) : bytes.toByteSlice.stop = bytes.size := by
  simp [ByteArray.toByteSlice, ByteSlice.stop]

/- LEAN: not in Rust, whose slices are in memory and so end below the largest position. A slice
whose end is not below `USize.size` cannot be in memory either, but Lean's logic has such slices;
they are lexed here, in chunks of `CHUNK_SIZE` bytes, below `USize.size` on every platform. Each
chunk is copied into an array of its own, as positions in `Input` are positions in the whole
array, and is lexed as a slice of its own, from `position` in the slice on, with `held` the
result the consumer broke with in an earlier chunk, if it did. Lexing stops at an error, as it
does in a slice; the bytes after it are left to the caller, as those of a slice are. -/
/-- Lexes the slice from `position` on, a chunk at a time. -/
@[noinline]
def lexChunks (abandon recover : Span.Location → StateT H m Unit) (slice : ByteSlice)
    (position : Nat) (held : Option (Span.Located R)) :
    InnerM H m (Except (Error.LexError E) (Option (Span.Located R))) := do
  if h : position < slice.size then
    let chunkStart := slice.start + position
    let chunk := slice.byteArray.extract chunkStart (min (chunkStart + CHUNK_SIZE) slice.stop)
    have hsize : chunk.toByteSlice.stop < USize.size := by
      rw [stop_toByteSlice]
      have := USize.le_size
      simp only [chunk, ByteArray.size_extract, CHUNK_SIZE] at *
      omega
    match ← lexSliceFitting abandon recover chunk.toByteSlice hsize with
    | .ok chunkHeld => lexChunks abandon recover slice (position + CHUNK_SIZE) (chunkHeld.or held)
    | .error err => return .error err
  else
    return .ok held
termination_by slice.size - position
decreasing_by simp only [CHUNK_SIZE] at *; omega

/--
Lexes the slice, or discards it if the consumer has had the rest discarded.

Returns the result the consumer broke with in the slice, if it did.
-/
def lexSliceStep (abandon recover : Span.Location → StateT H m Unit) (slice : ByteSlice) :
    InnerM H m (Except (Error.LexError E) (Option (Span.Located R))) :=
  if h : slice.stop < USize.size then lexSliceFitting abandon recover slice h
  else lexChunks abandon recover slice 0 none

/--
Lexes the end of the input, which resets the lexer unless it fails and recovers.

Hands the end of the input over unless a result is held, also while discarding. Returns the
result the consumer broke with at the end of the input, if it did.
-/
def lexEofStep (abandon recover : Span.Location → StateT H m Unit) :
    InnerM H m (Except (Error.LexError E) (ControlFlow (Span.Located R))) := do
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
      return .error (Error.LexError.Internal.new failure.cause failure.span none)
    return .error (← failCall abandon failure true)

end

end Internal

section

variable {H : Type} {R E : Type} [Token.Consume H R E]

/--
Constructs the lexer.

The lexer stops at its first error.
-/
def new (consumer : H) (version : Token.Version) : Lexer H :=
  { handler := consumer,
    core := {
      version
      initialVersion := version
      state := .normal
      discardedFrom := none
      holding := false
      recovers := false
      consumedDepth := 0
      lexedDepth := 0
      recoveryState := none
      tokenStart := Span.Location.initial
      tokenContent := Internal.Helpers.ContentBuffer.empty
      offset := 0
      base := 0
      line := 0
      lineStart := 0
      batch := Token.Internal.TokenBatch.empty Internal.BATCH_CAPACITY
      tokenStarted := .inl rfl
      batchEnded := Nat.zero_le _ }
    held := none }

/- LEAN: Rust requires the consumer to recover by the bound `C: SmtRecover`; here by the
instance argument, which the construction itself does not use. -/
/--
Constructs a lexer that recovers from errors (EXPERIMENTAL).

Lexer recovery is implemented but experimental
since the exact semantics have not yet been set in stone.
It can change or be removed in any version and should not be used.
-/
def newRecovering [Token.Recover H m] (consumer : H)
    (version : Token.Version) : Lexer H Recovering :=
  let { handler, core, held } := new consumer version
  { handler, core := { core with recovers := true }, held }

/--
Returns the current lexer location.

While discarding, the lexer location does not change
and stays where discarding began.
-/
def currentLocation (self : Lexer H recovery) : Span.Location :=
  self.core.currentLocation

/--
The SMT-LIB version currently in force.

The version can change if the token consumer asks for it from the
cursor. The end of the input resets the version to the initial one.
-/
def version (self : Lexer H recovery) : Token.Version :=
  self.core.version

/--
Where the lexer began to discard the input, if it discards.

The consumer asks for discarding through its cursor. The lexer then drops everything it is fed
and hands over nothing but the end of the input. The end of the input ends discarding.
-/
def discardedFrom (self : Lexer H recovery) : Option Span.Location :=
  self.core.discardedFrom

/- LEAN: on the lexer that stops at its first error only, as in Rust. -/
/-- Returns the token consumer. -/
def consumer (self : Lexer H) : H :=
  self.handler

/- LEAN: Rust's `consumer_mut`, on the lexer that stops at its first error only, as in Rust. The
lexer is taken apart so that the consumer is held once and changed in place, if the caller does
not keep the old lexer. -/
/-- Returns the lexer with its token consumer changed by `f`. -/
def modifyConsumer (self : Lexer H) (f : H → H) : Lexer H :=
  let { handler, core, held } := self
  { handler := f handler, core, held }

namespace Internal

/- LEAN: not in Rust: the public `consumer`, for every recovery, under the name the proofs use. -/
/-- The consumer of the lexer. -/
def handler (self : Lexer H recovery) : H :=
  self.handler

/-- The fields of the lexer other than its consumer and the held result. -/
def core (self : Lexer H recovery) : LexerCore :=
  self.core

/-- The result the consumer broke with, which the lexer holds. -/
def held (self : Lexer H recovery) : Option (Span.Located R) :=
  self.held

/-- The lexer with the consumer, the fields and the held result. -/
def ofParts (handler : H) (core : LexerCore) (held : Option (Span.Located R)) : Lexer H recovery :=
  { handler, core, held }

/- LEAN: takes the lexer apart so that the consumer and the fields are each held once, runs
the step on them, and puts the lexer together again; Rust does the same through
`&mut self`. -/
@[inline]
def run [Monad m] (self : Lexer H recovery) (step : InnerM H m α) :
    m (α × Lexer H recovery) := do
  let { handler, core, held } := self
  let ((result, core), handler) ← (step.run core).run handler
  return (result, { handler, core, held })

/-- The lexer with the held result. -/
def withHeld (self : Lexer H recovery) (held : Option (Span.Located R)) : Lexer H recovery :=
  { self with held }

end Internal

end

end BSmtLib.Lexer

namespace BSmtLib

section

open Lexer.Recovery (FailFast Recovering Recovers)

variable {H : Type} {R E : Type} [Token.Consume H R E]

/- LEAN: the type `AfterError` is, by whether the lexer recovers: a function of a `Bool` that
can be matched on, which a function of the recovery type cannot. -/
/-- What a lexer call that failed gives back, by whether the lexer recovers. -/
@[expose]
def Lexer.Internal.AfterErrorOf (H : Type) [Token.Consume H R E] (recovery : Type) :
    Bool → Type
  | false => H
  | true => Lexer H recovery

/- LEAN: what Rust's `&mut self` leaves usable after a call that failed: the type of the
recovering lexer, and the token consumer for a lexer that stops at its first error, whose
further calls panic in Rust but whose `consumer` can still be called. -/
/--
What a lexer call that failed gives back: the token consumer for a lexer
that stops at its first error, which cannot be used again, and the lexer
itself for a recovering one, from which the rest of the input is to be fed.
-/
@[expose]
def Lexer.AfterError (H : Type) [Token.Consume H R E] (recovery : Type) [Recovers recovery] :
    Type :=
  Lexer.Internal.AfterErrorOf H recovery (Recovers.recovers recovery)

/--
A recovering lexer whose end of the input raised an error.

The input has ended, so only the end of the input can be lexed again,
which completes the recovery.
-/
/- LEAN: what Rust's `&mut self` leaves usable after `lex_eof` failed in a recovering lexer and
the error continues at the end, where Rust panics on any slice but the end of the input. -/
structure Lexer.PendingEof (H : Type) [Token.Consume H R E] (recovery : Type := Recovering)
    where
  private mk ::
  private lexer : Lexer H recovery

/- LEAN: not in Rust, which has no accessor for it either. -/
/-- The lexer held by a recovering lexer whose end of the input failed. -/
def Lexer.Internal.pendingLexer (self : Lexer.PendingEof H recovery) : Lexer H recovery :=
  self.lexer

/- LEAN: what Rust's `&mut self` leaves usable after `lex_eof` failed. Rust panics on a
non-empty slice fed to a recovering lexer whose end of the input failed and continues. -/
/--
What a recovering lexer gives back after its end of the input failed: the
lexer, if the error is final, or the lexer that can only lex the end of the
input again, if the error continues at the end.
-/
inductive Lexer.AfterEof (H : Type) [Token.Consume H R E] (recovery : Type := Recovering) where
  | lexer (lexer : Lexer H recovery)
  | pending (pending : Lexer.PendingEof H recovery)

/-- What a lexer gives back after its end of the input failed, by whether the lexer recovers. -/
@[expose]
def Lexer.Internal.AfterEofErrorOf (H : Type) [Token.Consume H R E] (recovery : Type) :
    Bool → Type
  | false => H
  | true => Lexer.AfterEof H recovery

/--
What a lexer gives back after its end of the input failed: the token
consumer for a lexer that stops at its first error, and what remains of a
recovering one.
-/
/- LEAN: what Rust's `&mut self` leaves usable after `lex_eof` failed, by whether the lexer
recovers, as `AfterError` is for the other calls. -/
@[expose]
def Lexer.AfterEofError (H : Type) [Token.Consume H R E] (recovery : Type)
    [Recovers recovery] : Type :=
  Lexer.Internal.AfterEofErrorOf H recovery (Recovers.recovers recovery)

namespace Lexer

/-- What a failed call gives back, by whether the lexer recovers. -/
def Internal.afterErrorOf : (recovers : Bool) → Lexer H recovery →
    Internal.AfterErrorOf H recovery recovers
  | false, lexer => lexer.handler
  | true, lexer => lexer

private def afterError [Recovers recovery] (lexer : Lexer H recovery) : AfterError H recovery :=
  Internal.afterErrorOf (Recovers.recovers recovery) lexer

/-- What a failed end of the input gives back, by whether the lexer recovers. -/
def Internal.afterEofErrorOf : (recovers : Bool) → Lexer H recovery → (continues : Bool) →
    Internal.AfterEofErrorOf H recovery recovers
  | false, lexer, _ => lexer.handler
  | true, lexer, true => .pending ⟨lexer⟩
  | true, lexer, false => .lexer lexer

private def afterEofError [Recovers recovery] (lexer : Lexer H recovery) (continues : Bool) :
    AfterEofError H recovery :=
  Internal.afterEofErrorOf (Recovers.recovers recovery) lexer continues

/- LEAN: what Rust's `lex_eof` returns, or panics on where the consumer continues at the end of
the input, a broken contract. Here the broken contract is an obligation on the caller, who does
not give the lexer such a consumer: it is answered by `none` rather than a panic. -/
/-- The result to return at the end of the input: the held one, else the one the consumer broke
with at the end of the input. -/
private def eofResult (held : Option (Span.Located R)) (flow : ControlFlow (Span.Located R)) :
    Option (Span.Located R) :=
  match held, flow with
  | some held, _ => some held
  | none, .break located => some located
  | none, .continue => none

/- LEAN: the Rust methods take `&mut self`; these take the lexer and return it updated along
with the result. If the caller does not keep the old lexer, it is updated in place. -/

/--
Lexes the given slice, sending the lexed tokens to the consumer.

If the token consumer returns `ControlFlow.break` on some token, the
lexer holds the result, located where the consumer broke, and goes on
lexing what it is fed. Any token handed over after it, including those
the consumer left in its cursor, is the error `UnexpectedTrailingToken`.
The result is returned by `lexEof`.

If the consumer has the rest discarded, the lexer drops everything it is
fed until the end of the input (see `discardedFrom`).

If an error occurs, a lexer that stops at its first error gives back
only its token consumer. A recovering lexer makes the consumer abandon its unfinished work,
drops the held result, and returns the error. `LexError.continuesFrom`
determines the location from which further lexing should be started for
error recovery.
-/
def lexSlice [Monad m] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]
    [Recovery.Recovers recovery] [Recovery.LexRecovery recovery H m]
    (self : Lexer H recovery) (slice : ByteSlice) :
    m (Except (Error.LexError E × AfterError H recovery) (Lexer H recovery)) := do
  let step := Internal.lexSliceStep (Recovery.LexRecovery.abandon recovery)
      (Recovery.LexRecovery.recover recovery) slice
  let (result, self) ← Internal.run self step
  return match result with
    | .ok held => .ok (Internal.withHeld self (held.or self.held))
    | .error err => .error (err, afterError (Internal.withHeld self none))

/--
Lexes end-of-file, sending the lexed tokens to the consumer.

If the lexer holds a result, the end of the input is not handed over and
the held result is returned. Otherwise the end-of-file token is handed
over, also while the lexer discards, and the consumer must break on it:
the result it breaks with is returned, with its location. A consumer
that continues on the end-of-file token breaks its contract; the lexer
then returns `none`.

The end of the input resets the lexer: the version to the initial one,
discarding, the held result, and any partial token.

If an error occurs, a lexer that stops at its first error gives back
only its token consumer. A recovering lexer makes the consumer abandon its unfinished work
and returns the error. `LexError.continuesFrom` determines the location
from which further lexing should be started for error recovery.
-/
def lexEof [Monad m] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]
    [Recovery.Recovers recovery] [Recovery.LexRecovery recovery H m]
    (self : Lexer H recovery) :
    m (Except (Error.LexError E × AfterEofError H recovery)
        (Option (Span.Located R) × Lexer H recovery)) := do
  let step := Internal.lexEofStep (Recovery.LexRecovery.abandon recovery)
      (Recovery.LexRecovery.recover recovery)
  let (result, self) ← Internal.run self step
  return match result with
    | .ok flow => .ok (eofResult self.held flow, Internal.withHeld self none)
    | .error err => .error (err, afterEofError (Internal.withHeld self none)
        err.continuesFrom.isSome)

/- LEAN: Rust's `lex_eof` on the recovering lexer that `PendingEof` stands for. -/
/--
Lexes the end of the input again, which completes the recovery.

The lexer hands over the end-of-file token, and returns what `lexEof`
does. An error is final: the lexer resets itself and does not continue.
-/
def PendingEof.lexEof [Monad m] [∀ batch, Token.ConsumeFrom H
    (Token.BatchCursor batch) m] [Token.Recover H m]
    (self : PendingEof H) :
    m (Except (Error.LexError E × Lexer H Recovering)
        (Option (Span.Located R) × Lexer H Recovering)) := do
  let step := Internal.lexEofStep (Token.Recover.abandon (H := H)) (Token.Recover.recover (H := H))
  let (result, lexer) ← Internal.run self.lexer step
  return match result with
    | .ok flow => .ok (eofResult lexer.held flow, Internal.withHeld lexer none)
    | .error err => .error (err, Internal.withHeld lexer none)

/--
Lexes the whole input including EOF at the end.

Returns what `lexEof` does, and the lexer reset by the end of the input.

If an error occurs, the lexer gives back only its token consumer.
-/
def lexAll [Monad m] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] (self : Lexer H)
    (input : ByteSlice) :
    m (Except (Error.LexError E × AfterError H FailFast) (Option (Span.Located R) × Lexer H)) := do
  match ← self.lexSlice input with
  | .ok self => self.lexEof
  | .error err => return .error err

end Lexer

end

end BSmtLib

import BSmtLib.Proofs.Lexer.WRustPort

/-!
The lexer with the batch kept in the lexer's state: a lexer of the chain that leads from the
specification to the library's lexer, after the Rust lexer ported to Lean `WRustPort`.

It is the code of the Rust port `WRustPort` over operations of its own (`WRustPort.Ops`): the
batch is kept in the lexer's state (`LexerCore.batch`) and reused from slice to slice. It is
handed to the consumer in the cursor and taken back, whatever the consumer decides
(`handOver`), and a token handed over alone is put into it (`handOverStored`), where the Rust
port makes a fresh batch for every slice and for every token handed over alone. With it come
the locals of the fast path as the Lean port adapts them: the line and the line start stay in
the lexer's state, which the fast path reads, where the Rust port keeps them in locals
(`WRustPort.FastState`).

Everything else is the Rust port's, and so are the lexer's type and its construction.
-/

namespace BSmtLib.Proofs.Lexer.X1BatchInCore

open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)
open WRustPort

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat}

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
def handOverStored (ty : TokenCategory) (start «end» : Location)
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
here a token that is not emitted is not written. Rust keeps the line and the line start in
locals of `lex_normal`; here they stay in the lexer state, which the fast path only reads, and
the locals are empty. -/
@[inline]
def pushFast (input : ByteSlice) (batch : TokenBatch) (_locals : Unit) (offset : Nat)
    (base : Nat) (ty : TokenCategory) (contentStart contentStop start «end» : Nat) (emit : Bool)
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

/- LEAN: the batch lives in the lexer state between the calls, so that its storage is reused
from one slice to the next; it is empty whenever lexing returns. A slice starts with it, as
Rust's starts with an empty batch, a local of the call; the end of the input keeps it. -/
/-- The operations of the lexer with the batch kept in its state: the batch is reused, and the
line counters stay in the lexer state. -/
@[instance_reducible]
def ops : Ops H m R E where
  Locals := Unit
  loadLocals := pure ()
  storeLocals _ := pure ()
  pushFast := pushFast
  flushHeld := flushHeld
  flushBatch := flushBatch
  sinkStoredAt := handOverStored
  sinkEof := handOverEof
  sliceStorage batch := batch
  eofBatch c := ⟨c.batch, c.batchEnded⟩

end

namespace Lexer

/- LEAN: the lexer's type and the functions that do not lex are the Rust port's
(`WRustPort.Lexer`); the functions that lex run the Rust port's code over the operations
`X1BatchInCore.ops`. -/

/--
Lexes the given slice, sending the lexed tokens to the consumer, as `WRustPort.Lexer.lexSlice`
does.
-/
def lexSlice [Monad m] [Consume H m R E] [LexRecovery recovery H m]
    (self : WRustPort.Lexer H recovery) (slice : ByteSlice) :
    m (Except (LexError E × WRustPort.Lexer.AfterError H recovery)
      (ControlFlow (Located R) × WRustPort.Lexer H recovery)) := do
  let step := lexSliceStep (ops := X1BatchInCore.ops) (LexRecovery.abandon recovery)
    (LexRecovery.recover recovery) slice
  let (result, self) ← self.run step
  return match result with
    | .ok flow => .ok (flow, self)
    | .error err => .error (err, WRustPort.Lexer.afterError self)

/--
Lexes end-of-file, sending the lexed tokens to the consumer, as `WRustPort.Lexer.lexEof` does.
-/
def lexEof [Monad m] [Consume H m R E] [LexRecovery recovery H m]
    (self : WRustPort.Lexer H recovery) :
    m (Except (LexError E × WRustPort.Lexer.AfterEofError H recovery)
      (ControlFlow (Located R) × WRustPort.Lexer H recovery)) := do
  let step := lexEofStep (ops := X1BatchInCore.ops) (LexRecovery.abandon recovery)
    (LexRecovery.recover recovery)
  let (result, self) ← self.run step
  return match result with
    | .ok flow => .ok (flow, self)
    | .error err => .error (err, WRustPort.Lexer.afterEofError self err.continuesFrom.isSome)

/--
Lexes the end of the input again, which completes the recovery, as
`WRustPort.Lexer.PendingEof.lexEof` does.
-/
def PendingEof.lexEof [Monad m] [Consume H m R E] [Recover H m]
    (self : WRustPort.Lexer.PendingEof H) :
    m (Except (LexError E × WRustPort.Lexer H .recovering)
      (ControlFlow (Located R) × WRustPort.Lexer H .recovering)) := do
  let step := lexEofStep (ops := X1BatchInCore.ops) (Recover.abandon (H := H))
    (Recover.recover (H := H))
  let (result, lexer) ← self.lexer.run step
  return match result with
    | .ok flow => .ok (flow, lexer)
    | .error err => .error (err, lexer)

/-- Lexes the whole input including EOF at the end, as `WRustPort.Lexer.lexAll` does. -/
def lexAll [Monad m] [Consume H m R E] (self : WRustPort.Lexer H) (input : ByteSlice) :
    m (Except (LexError E × WRustPort.Lexer.AfterError H .failFast)
      (ControlFlow (Located R) × WRustPort.Lexer H)) := do
  match ← lexSlice self input with
  | .ok (.break result, self) =>
    -- reset the lexer as if we are at the start of a new file
    let ((), self) ← self.run (reset (H := H) (m := m))
    return .ok (.break result, self)
  | .ok (.continue, self) => lexEof self
  | .error err => return .error err

end Lexer

end BSmtLib.Proofs.Lexer.X1BatchInCore

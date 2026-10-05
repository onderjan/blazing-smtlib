import BSmtLib.Proofs.Lexer.V1Naive

/-!
The batched lexer: the second of the chain of lexers that leads from the specification to the
library's lexer.

It is the naive lexer `V1Naive` with one change: where the hand-overs to the consumer are cut.
It lexes the bytes with the naive lexer's pure step, keeps the naive lexer's state and its
lexer type, and lexes the end of the input with the naive lexer's own operation. Only the
lexing of a slice is its own: it collects the tokens of a slice in a batch and hands them over
as the library's lexer `BSmtLib.Lexer` does.

- A batch holds at most `batchCapacity` tokens; when it is full, it is handed over.
- The end of a slice hands the batch over.
- Some tokens are handed over alone, in a cursor of their own, after the batch before them
  (`handedAlone`): a token cut by a slice boundary, a string under version 2.0, a string with a
  doubled quote or a line feed, and a quoted symbol with a line feed. The end of the input hands
  every token over alone.
- The tokens the consumer leaves in a cursor are handed over again, before any other.

The tokens of a batch are lexed ahead of the consumer's answers, under the version in force
when the batch was started. When the consumer switches the version in a way that changes the
lexing (`BatchCursor.setVersion`), or finishes, the lexer goes back to the end of the last token
the consumer took: it lexes the slice again from there under the new version, or discards it
from there. A lexical error met ahead is reported only after the batch before it has been
handed over and taken whole; a stop of the consumer in that batch drops the error.
-/

namespace BSmtLib.Proofs.Lexer.V2Batched

open V1Naive

/-! ## Batches -/

/-- The number of tokens a batch holds at most: that of the library's lexer. -/
def batchCapacity : Nat := BSmtLib.Lexer.BATCH_CAPACITY

/-- Whether the byte is among the bytes. -/
def hasByte (bytes : ByteArray) (c : UInt8) : Bool :=
  bytes.data.contains c

/--
Whether the lexeme is handed over alone, in a cursor of its own, and not in the batch, when it
is lexed under `version` in a slice whose first byte is at the offset `sliceStart`.

These are the tokens the library's lexer builds in its own buffer instead of borrowing them
from the slice: a token that started in an earlier slice, a string under version 2.0, whose
escapes leave out bytes, a string with a doubled quote, which stands for one quote, a string or
a quoted symbol with a line feed, at which the run of its bytes is cut to count the line.
-/
def handedAlone (version : Version) (sliceStart : Nat) (l : Lexeme) : Bool :=
  -- the token was cut by the boundary of the slice
  l.start.offset < sliceStart ||
    match l.category with
    -- under version 2.0 and with a doubled quote, the content is not the bytes of the token;
    -- a quote in the content of a later version stands for a doubled one
    | .string => version == .v2_0 || hasByte l.content (byte! '\n') || hasByte l.content (byte! '"')
    | .quotedSymbol => hasByte l.content (byte! '\n')
    | _ => false

/-- The batch of the lexemes, in order, with their contents one after the other. -/
def toTokenBatch (lexemes : Array Lexeme) : TokenBatch :=
  lexemes.foldl (init := TokenBatch.empty lexemes.size) fun batch l =>
    let start := batch.bytes.size
    ({ batch with bytes := batch.bytes ++ l.content } : TokenBatch).pushLocated l.category start
      (start + l.content.size) l.start l.end

/-- Why the consumer stopped in a batch. -/
inductive Stop (R E : Type) where
  /-- It switched the version so that the rest is to be lexed again from the location. -/
  | relex (location : Location)
  /-- It finished, at the location of the value; the rest of the input is discarded. -/
  | finished (located : Located R)
  | failed (failure : Failure E)

/-- What lexing a byte leaves to the loop over the slice. -/
inductive Outcome (R E : Type) where
  /-- Lexing goes on with the next byte. -/
  | next
  /-- The consumer finished on a token handed over alone; the input is discarded from the next
  byte on. -/
  | finished (located : Located R)
  /-- The consumer stopped in a batch. -/
  | stopped (stop : Stop R E)
  /-- The byte raised a lexical error, or the consumer failed on a token handed over alone. -/
  | failed (failure : Failure E)

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

/- As in the naive lexer, the functions below thread the lexer state `Core` and the batch
through by hand, while the consumer is the state of the monad `StateT H m`. -/

/--
Hands the cursor over to the consumer until nothing remains in it or the consumer stops.

Returns the stop, if the consumer stopped, and the cursor as the consumer left it. A stop takes
effect at the end of the last token the consumer took.
-/
def handOverCursor (cursor : BatchCursor) : StateT H m (Option (Stop R E) × BatchCursor) := do
  if h : cursor.HasNext then
    let (answer, ⟨next, consumed⟩) ← Consume.consume (H := H) cursor h
    let location := next.consumedEndOf consumed
    match answer with
    | .ok .continue =>
      if next.relexRequested then
        return (some (.relex location), next)
      else
        -- the tokens left are handed over again
        have : next.resetConsumed.remaining < cursor.remaining := by
          rw [BatchCursor.remaining_resetConsumed]
          exact consumed.remaining_lt
        handOverCursor next.resetConsumed
    | .ok (.break value) => return (some (.finished { value, location }), next)
    | .error err => return (some (.failed { cause := .consumer err, location }), next)
  else
    return (none, cursor)
termination_by cursor.remaining

/--
Hands the batch over under the version in force, if it has a token. The version on the cursor
the consumer leaves is in force from then on, and the tokens it took count for the parentheses
open.
-/
def flush (core : Core) (batch : Array Lexeme) : StateT H m (Option (Stop R E) × Core) := do
  let (stop, cursor) ← handOverCursor (BatchCursor.new core.version (toTokenBatch batch))
  return (stop, { core with
    version := cursor.version
    depth := cursor.foldConsumedCategories core.depth depthAfter })

/--
Hands the lexeme over: alone, after the batch, if `handedAlone` says so, or in the batch,
which is handed over when it is full. `sliceStart` is the offset of the first byte of the slice.
-/
def emit (sliceStart : Nat) (core : Core) (batch : Array Lexeme) (l : Lexeme) :
    StateT H m (Outcome R E × Core × Array Lexeme) := do
  if handedAlone core.version sliceStart l then
    let (stop, core) ← flush core batch
    if let some stop := stop then
      return (.stopped stop, core, #[])
    -- the naive lexer's hand-over of a token alone; its version applies from the next byte on,
    -- which is not lexed yet
    let (result, core) ← handOverAt core l
    return match result with
      | .ok none => (.next, core, #[])
      | .ok (some located) => (.finished located, core, #[])
      | .error failure => (.failed failure, core, #[])
  else
    let batch := batch.push l
    if batch.size < batchCapacity then
      return (.next, core, batch)
    let (stop, core) ← flush core batch
    return match stop with
      | some stop => (.stopped stop, core, #[])
      | none => (.next, core, #[])

/-- Lexes the byte `c` with no token in progress. -/
def lexStart (sliceStart : Nat) (core : Core) (batch : Array Lexeme) (c : UInt8) :
    StateT H m (Outcome R E × Core × Array Lexeme) := do
  let whitespace := Consume.consumesWhitespaceAndComments (H := H)
  let after := core.location.afterByte c
  match start core.version whitespace core.location c with
  | .idle => return (.next, { core with activity := .idle, location := after }, batch)
  | .pending p => return (.next, { core with activity := .token p, location := after }, batch)
  | .token l => emit sliceStart { core with activity := .idle, location := after } batch l
  | .error failure =>
    return (.failed { cause := .lexical failure.error, location := failure.location }, core, batch)

/--
Lexes the byte `c`, at the lexer's location, as the naive lexer's `lexByte` does, except that
the tokens go through `emit`.

`recover` is the consumer's call at the end of a recovery.
-/
def lexByte (recover : Location → StateT H m Unit) (sliceStart : Nat) (core : Core)
    (batch : Array Lexeme) (c : UInt8) : StateT H m (Outcome R E × Core × Array Lexeme) := do
  let location := core.location
  match core.activity with
  | .discarding => return (.next, { core with location := location.afterByte c }, batch)
  -- only the end of the input can follow, there is nothing to lex
  | .ended => return (.next, core, batch)
  | .recovered =>
    -- the consumer is told of a recovery before any token
    recover location
    lexStart sliceStart { core with activity := .idle } batch c
  | .skipping skip =>
    match scan (core.version == .v2_0) skip core.depth c with
    | .skip skip depth =>
      let core := { core with location := location.afterByte c, activity := .skipping skip, depth }
      return (.next, core, batch)
    | .before =>
      recover location
      lexStart sliceStart { core with activity := .idle } batch c
    | .after =>
      let location := location.afterByte c
      recover location
      return (.next, { core with location, activity := .idle, depth := 0 }, batch)
  | .idle => lexStart sliceStart core batch c
  | .token p =>
    let whitespace := Consume.consumesWhitespaceAndComments (H := H)
    let after := location.afterByte c
    match advance whitespace p location c with
    | .pending p => return (.next, { core with activity := .token p, location := after }, batch)
    | .idle => return (.next, { core with activity := .idle, location := after }, batch)
    | .tokenWith l => emit sliceStart { core with activity := .idle, location := after } batch l
    | .tokenBefore l =>
      let (outcome, core, batch) ← emit sliceStart { core with activity := .idle } batch l
      match outcome with
      -- the byte is lexed under the version the consumer has left in force
      | .next => lexStart sliceStart core batch c
      -- the consumer has finished on the token alone: the byte is the first one discarded
      | .finished located => return (.finished located, { core with location := after }, batch)
      | outcome => return (outcome, core, batch)
    | .error failure =>
      let failure := { cause := .lexical failure.error, location := failure.location }
      return (.failed failure, core, batch)

/-- What the loop over the slice does next. -/
inductive Next (R E : Type) where
  /-- Lexing goes on with the next byte, or ends at the end of the slice. -/
  | proceed (core : Core) (batch : Array Lexeme) (flow : ControlFlow (Located R))
  /-- The consumer stopped in a batch. -/
  | stop (stop : Stop R E) (core : Core) (flow : ControlFlow (Located R))
  | fail (failure : Failure E) (core : Core)

/--
What the loop does after the outcome of a byte: a lexical error hands the batch before it over
first, and is reported only if the consumer takes the batch whole.
-/
def settle (outcome : Outcome R E) (core : Core) (batch : Array Lexeme)
    (flow : ControlFlow (Located R)) : StateT H m (Next R E) := do
  match outcome with
  | .next => return .proceed core batch flow
  | .finished located => return .proceed core batch (.break located)
  | .stopped stop => return .stop stop core flow
  | .failed failure =>
    let (stop, core) ← flush core batch
    return match stop with
      | none => .fail failure core
      | some stop => .stop stop core flow

/-- What the loop does at the end of the slice: it hands the batch over. -/
def settleEnd (core : Core) (batch : Array Lexeme) (flow : ControlFlow (Located R)) :
    StateT H m (Next R E) := do
  let (stop, core) ← flush core batch
  return match stop with
    | none => .proceed core #[] flow
    | some stop => .stop stop core flow

end

/--
Where lexing goes on after the consumer stopped in a batch: at the end of the last token it
took, with the activity there and the flow; or the failure to return.
-/
def resumption (stop : Stop R E) (flow : ControlFlow (Located R)) :
    Except (Failure E) (Location × Activity × ControlFlow (Located R)) :=
  match stop with
  | .relex location => .ok (location, .idle, flow)
  | .finished located => .ok (located.location, .discarding, .break located)
  | .failed failure => .error failure

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

/--
Lexes the bytes of the slice from `index` on, and hands the batch over at the end. `flow` is
the consumer's finish, if it has finished on an earlier token of the slice. `sliceStart` is the
offset of the first byte of the slice.

When the consumer stops in a batch, the loop goes back to the end of the last token it took and
goes on from there with an empty batch. `committed` is the index of the byte where the loop
last went on so: every token of the batch starts at it or after it and has a byte, so a stop is
after it. A stop elsewhere breaks the consumer's contract and is reported as an internal error.
-/
def lexFrom (recover : Location → StateT H m Unit) (sliceStart : Nat) (slice : ByteSlice)
    (index committed : Nat) (core : Core) (batch : Array Lexeme) (flow : ControlFlow (Located R)) :
    StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core) := do
  if h : index < slice.size then
    let (outcome, core, batch) ← lexByte recover sliceStart core batch slice[index]
    match ← settle outcome core batch flow with
    | .proceed core batch flow =>
      lexFrom recover sliceStart slice (index + 1) committed core batch flow
    | .fail failure core => return (.error failure, core)
    | .stop stop core flow =>
      match resumption stop flow with
      | .error failure => return (.error failure, core)
      | .ok (location, activity, flow) =>
        let resumed := location.offset - sliceStart
        if hr : committed < resumed ∧ resumed ≤ slice.size then
          lexFrom recover sliceStart slice resumed resumed { core with location, activity } #[] flow
        else
          return (.error { cause := .internal .stoppedBeforeStart, location }, core)
  else
    match ← settleEnd core batch flow with
    | .proceed core _ flow => return (.ok flow, core)
    | .fail failure core => return (.error failure, core)
    | .stop stop core flow =>
      match resumption stop flow with
      | .error failure => return (.error failure, core)
      | .ok (location, activity, flow) =>
        let resumed := location.offset - sliceStart
        if hr : committed < resumed ∧ resumed ≤ slice.size then
          lexFrom recover sliceStart slice resumed resumed { core with location, activity } #[] flow
        else
          return (.error { cause := .internal .stoppedBeforeStart, location }, core)
termination_by (slice.size - committed, slice.size - index)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

/-- Lexes the slice, or discards it if the consumer has finished. -/
def lexSliceStep (recovers : Bool) (abandon recover : Location → StateT H m Unit)
    (slice : ByteSlice) (core : Core) :
    StateT H m (Except (LexError E) (ControlFlow (Located R)) × Core) := do
  let core ← match core.activity with
    -- the consumer failed after a whole token with nothing open: the recovery is made here,
    -- even if the slice is empty
    | .recovered => do
      recover core.location
      pure { core with activity := .idle }
    | _ => pure core
  match core.activity with
  -- the input has ended with the error, there is nothing to lex
  | .ended => return (.ok .continue, core)
  | _ =>
    let (result, core) ← lexFrom recover core.location.offset slice 0 0 core #[] .continue
    match result with
    | .ok flow => return (.ok flow, core)
    | .error failure =>
      let (err, core) ← failCall recovers abandon failure false core
      return (.error err, core)

end

/-! ## The lexer

The batched lexer is the naive lexer's type `V1Naive.Lexer` with the operations below in place
of its `lexSlice` and `lexAll`; the other operations are the naive lexer's: `new`,
`newRecovering`, `lexEof`, `PendingEof.lexEof`, `currentLocation` and `version`.
-/

private def afterError :
    {recovery : Recovery} → V1Naive.Lexer H recovery → V1Naive.Lexer.AfterError H recovery
  | .failFast, _ => ()
  | .recovering, lexer => lexer

/--
Lexes the given slice, sending the lexed tokens to the consumer.

If the token consumer returns `ControlFlow.break` on some token, the lexer passes it through,
adding the break location. Subsequent bytes are discarded until EOF, which resets the lexer.

If the token consumer returns `ControlFlow.continue` on all tokens, the lexer is ready for
further lexing.

If an error occurs, a lexer that stops at its first error is not given back. A recovering lexer
makes the consumer abandon its unfinished work and returns the error. `LexError.continuesFrom`
determines the location from which further lexing should be started for error recovery.
-/
def lexSlice [Monad m] [Consume H m R E] [LexRecovery recovery H m]
    (self : V1Naive.Lexer H recovery) (slice : ByteSlice) :
    m (Except (LexError E × V1Naive.Lexer.AfterError H recovery)
      (ControlFlow (Located R) × V1Naive.Lexer H recovery)) := do
  let step := lexSliceStep (recovery == .recovering) (LexRecovery.abandon recovery)
    (LexRecovery.recover recovery) slice
  let { handler, core } := self
  let ((result, core), handler) ← (step core).run handler
  let self : V1Naive.Lexer H recovery := { handler, core }
  return match result with
    | .ok flow => .ok (flow, self)
    | .error err => .error (err, afterError self)

/--
Lexes the whole input including EOF at the end.

If the token consumer returns `ControlFlow.break` on some token, the lexer passes it through,
adding the break location, and resets itself as if at the start of a new input.

If the token consumer returns `ControlFlow.continue` on all tokens including EOF, the lexer
resets itself after EOF and returns `ControlFlow.continue`.

If an error occurs, the lexer is not given back.
-/
def lexAll [Monad m] [Consume H m R E] (self : V1Naive.Lexer H) (input : ByteSlice) :
    m (Except (LexError E × V1Naive.Lexer.AfterError H .failFast)
      (ControlFlow (Located R) × V1Naive.Lexer H)) := do
  match ← lexSlice self input with
  | .ok (.break result, self) =>
    -- reset the lexer as if we are at the start of a new file
    return .ok (.break result, { self with core := self.core.reset })
  | .ok (.continue, self) => self.lexEof
  | .error err => return .error err

end BSmtLib.Proofs.Lexer.V2Batched

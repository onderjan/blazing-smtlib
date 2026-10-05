import BSmtLib.Lexer.CharClass
import BSmtLib.Lexer.Error
import BSmtLib.Lexer.Helpers
import BSmtLib.Lexer.Recovery
import BSmtLib.Token

namespace BSmtLib.Lexer

/-- Maximal number of tokens that can be batched. -/
def BATCH_CAPACITY : Nat := 256

/-- Why lexing stopped before the end of the slice. -/
inductive Stop (R : Type) where
  /-- The consumer requested lexing again from the stop location. -/
  | relex
  /-- The consumer finished with a result at the stop location. -/
  | finished (result : R)

structure Interrupted (R E : Type) where
  result : Except (LexErrorCause E) (Stop R)
  location : Location

/--
A lexing error with the effective failure location.

For a lexical error, the effective failure location is before the byte that
raised it, or the end of the input if the end raised it. For a consumer error,
it is after the last token the consumer has consumed.
-/
structure Failure (E : Type) where
  cause : LexErrorCause E
  location : Location

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
  batch : TokenBatch

structure _root_.BSmtLib.Lexer (H : Type) (recovery : Recovery := .failFast) where
  private mk ::
  /-- Consumer of produced tokens. -/
  private handler : H
  private core : LexerCore

/- LEAN: Rust's lexer methods take `&mut self` and return `Result<usize, Interrupted<..>>`,
using `?` to pass an interruption up. In Lean the same is a monad: `StateT LexerCore` holds
the lexer's fields as mutable state, `StateT H` the handler, and `ExceptT (Interrupted R E)`
is the `Err` that `throw` raises and that passes up through every `←` like `?`. `ExceptT` is
outermost so that the lexer's fields keep their changes when an interruption is thrown, as
in Rust. The handler is a separate state so that it can be handed to `consume` without
another reference to it remaining in the lexer's state, which would make the handler's
updates copy it. -/
abbrev InnerM (H : Type) (m : Type → Type) := StateT LexerCore (StateT H m)

abbrev LexM (H : Type) (m : Type → Type) (R E : Type) := ExceptT (Interrupted R E) (InnerM H m)

/-- The stream offset of `position` in the input. -/
@[inline]
def LexerCore.offsetAt (self : LexerCore) (position : USize) : Nat :=
  self.offset + (position - self.base).toNat

/-- Location of `position` in the input.

Every line feed before `position` must be marked before calling this. -/
@[inline]
def LexerCore.locationAt (self : LexerCore) (position : USize) : Location :=
  let offset := self.offsetAt position
  { offset, line := self.line, column := offset - self.lineStart }

/-- The current location: that of the next byte to be lexed. -/
@[inline]
def LexerCore.currentLocation (self : LexerCore) : Location :=
  self.locationAt self.base

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

/- LEAN: `getThe` and `modifyThe` name the state they access, as there are two. Reading the
state with `← getCore` gives a reference to it; the code below lets such references die before
the state is modified, so that it is modified in place and not copied. -/
@[inline]
private def getCore : LexM H m R E LexerCore :=
  getThe LexerCore

@[inline]
private def modifyCore (f : LexerCore → LexerCore) : LexM H m R E Unit :=
  modifyThe LexerCore f

@[inline]
private def setState (state : LexerState) : LexM H m R E Unit :=
  modifyCore fun c => { c with state }

/- LEAN: Rust's `C::CONSUMES_WHITESPACE_AND_COMMENTS`, read from the consumer's instance. -/
@[inline]
private def consumesWhitespaceAndComments : LexM H m R E Bool :=
  pure (Consume.consumesWhitespaceAndComments (H := H))

/- LEAN: the content buffer is taken out of the state before it is changed:
changing `c.tokenContent` while `c` still refers to it would find it shared and copy it,
together with its array. -/
/-- Changes the content buffer in place. -/
@[inline]
private def modifyContent (f : ContentBuffer → ContentBuffer) : LexM H m R E Unit :=
  modifyCore fun c =>
    let content := c.tokenContent
    let c := { c with tokenContent := ContentBuffer.empty }
    { c with tokenContent := f content }

/-- Changes the batch in place. -/
@[inline]
private def modifyBatch (f : TokenBatch → TokenBatch) : LexM H m R E Unit :=
  modifyCore fun c =>
    let batch := c.batch
    let c := { c with batch := default }
    { c with batch := f batch }

@[inline]
private def extendContent (input : Input) (start stop : USize) : LexM H m R E Unit :=
  modifyContent (·.extendFrom input.bytes start.toNat stop.toNat)

@[inline]
private def pushContent (c : UInt8) : LexM H m R E Unit :=
  modifyContent (·.push c)

@[inline]
private def startToken (position : USize) : LexM H m R E Unit := do
  -- update the token start to the computed location
  modifyCore fun c => { c with tokenStart := c.locationAt position }
  -- clear the token string
  modifyContent (·.clear)

@[inline]
private def markLineFeedAt (position : USize) : LexM H m R E Unit :=
  -- when lexing a run, this is used to mark a line feed
  -- the locations must only refer to positions after it afterwards
  modifyCore fun c => { c with line := c.line + 1, lineStart := c.offsetAt position + 1 }

/-- Fails with an error spanning up to `position` with effective failure at `failure`. -/
private def failWith (kind : LexicalErrorKind) (position failure : USize) : LexM H m R E α := do
  let c ← getCore
  let span := Span.newUnchecked c.tokenStart (c.locationAt position)
  -- no tokens have been consumed, as this is an error
  -- that occurred during lexing
  throw { result := .error (.lexical { kind, span }), location := c.locationAt failure }

/--
Fails with an error spanning the token up to `position`.

Used for errors detected mid-run, e.g. forbidden byte in a string
or a backslash in a quoted symbol.
-/
/- LEAN: Rust panics if `position` is zero, which no caller passes: an error detected at a
byte spans that byte. -/
private def failAt (kind : LexicalErrorKind) (position : USize) : LexM H m R E α :=
  -- the byte before the position raised the error
  failWith kind position (position - 1)

/-- Fails with an error spanning the token so far and, if it ended at a byte, that byte. -/
private def fail (kind : LexicalErrorKind) (tokenEnd : TokenEnd) : LexM H m R E α :=
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
private def expectDelimiter (next : UInt8) (position : USize) : LexM H m R E Unit := do
  unless isDelimiter next do
    failAt .missingDelimiter (position + 1)

/- LEAN: runs the consumer on the cursor. The consumer runs in `StateT H m`, which the `←` lifts
into the lexer's monad, where the consumer is the inner state. -/
private def callConsumer (cursor : BatchCursor) (h : cursor.HasNext) :
    LexM H m R E (Except E (ControlFlow R) × { c : BatchCursor // c.Consumed cursor }) := do
  let action : StateT H m (Except E (ControlFlow R) × { c : BatchCursor // c.Consumed cursor }) :=
    Consume.consume (H := H) cursor h
  action

/- LEAN: Rust's `flush_cursor` loops while the cursor is not empty; here the loop is the
recursion, which ends as every call of the consumer consumes a token, by the proof the
consumer returns. The interruption is returned rather than thrown, so that the caller can
take the batch back first. -/
/--
Hands the cursor over to the consumer until nothing remains in it or the consumer stops.

Returns the stop, if the consumer stopped, and the cursor as the consumer left it.
-/
private def flushCursor (cursor : BatchCursor) :
    LexM H m R E (Option (Interrupted R E) × BatchCursor) := do
  -- flush the cursor until nothing remains
  if h : cursor.HasNext then
    let (result, ⟨next, consumed⟩) ← callConsumer cursor h
    -- the stop takes effect after the consumed tokens
    let location := next.consumedEndOf consumed
    -- process the result
    match result with
    | .ok .continue =>
      if next.relexRequested then
        -- we need to stop and relex here
        return (some { result := .ok .relex, location }, next)
      else
        -- zero the number of consumed tokens in the cursor
        -- continue flushing until nothing remains
        have : next.resetConsumed.remaining < cursor.remaining := by
          rw [BatchCursor.remaining_resetConsumed]
          exact consumed.remaining_lt
        flushCursor next.resetConsumed
    | .ok (.break result) => return (some { result := .ok (.finished result), location }, next)
    | .error err => return (some { result := .error (.consumer err), location }, next)
  else
    -- everything was consumed without break or error
    return (none, cursor)
termination_by cursor.remaining

/- LEAN: Rust's `flush_cursor` takes a cursor over the lexer's arrays; here the batch itself
is handed to the consumer in the cursor, and taken back into the lexer state afterwards,
whatever the consumer decides, so that its storage is overwritten by the next batch. The
batch's array of contents is then set to `bytesAfter`, so that the batch does not keep a
reference to the lexer's content buffer, which would make the buffer's next change copy
it. -/
/-- Hands the batch over to the consumer and takes it back. -/
private def handOver (batch : TokenBatch) (bytesAfter : ByteArray) : LexM H m R E Unit := do
  let (stop, cursor) ← flushCursor (BatchCursor.new (← getCore).version batch)
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
  modifyCore fun c =>
    { c with version := cursor.version, batch := { cursor.intoBatch.clear with bytes := bytesAfter } }
  if let some interrupted := stop then
    throw interrupted

/-- Takes the batch out of the lexer state, leaving an empty one without storage. -/
@[inline]
private def takeBatch : LexM H m R E TokenBatch :=
  modifyGetThe LexerCore fun c => (c.batch, { c with batch := default })

private def flushBatch : LexM H m R E Unit := do
  -- the batch is spent once handed over, no matter what the handler decides
  if (← getCore).batch.len == 0 then
    return
  let batch ← takeBatch
  let bytes := batch.bytes
  handOver batch bytes

/--
Hands over a single token whose content is in the lexer's content buffer
(empty for the end of file), spanning from the token start to `end`.
-/
/- LEAN: Rust hands such a token over in a cursor of its own; here it goes in the batch,
which is empty after the flush, with the content buffer as its array of contents for the
one token. -/
private def handOverStored (ty : TokenCategory) («end» : Location) : LexM H m R E Unit := do
  -- flush the batch, then hand over this token
  flushBatch
  let batch ← takeBatch
  let bytes := batch.bytes
  let c ← getCore
  let batch := { batch with bytes := c.tokenContent.bytes }.pushLocated ty 0 c.tokenContent.len
    c.tokenStart «end»
  handOver batch bytes

/-- Sinks a token with the given content, ending at `tokenEnd`. -/
@[inline]
private def sinkSlice (ty : TokenCategory) (tokenEnd : TokenEnd) (content : Content) :
    LexM H m R E Unit := do
  -- the caller of this function is responsible
  -- for ensuring that the constructed token is valid
  match content with
  | .borrowed _ start stop =>
    -- this is borrowed content, so put it into the batch
    let c ← getCore
    let spanStart := c.tokenStart
    let spanEnd := c.locationAt tokenEnd.position
    modifyBatch (·.pushLocated ty start stop spanStart spanEnd)
    if (← getCore).batch.len == BATCH_CAPACITY then
      flushBatch
  | .stored =>
    -- this is in our own buffer, so we cannot put it into the batch
    -- as we need the buffer usable for the next token
    handOverStored ty ((← getCore).locationAt tokenEnd.position)

private def sinkEof : LexM H m R E Unit := do
  -- the end of file has no content, which the cleared content buffer gives
  handOverStored .endOfFile (← getCore).currentLocation

/--
Sinks a decimal token.

The token's own shape is checked first, then that `next`, the byte
at the end (if there is one), delimits it.
-/
@[inline]
private def finishDecimal (tokenEnd : TokenEnd) (content : Content) (next : Option UInt8) :
    LexM H m R E Unit := do
  -- decimals of the form 7. without any digit in fractional part are disallowed
  let last := content.last? (← getCore).tokenContent
  if last.isNone || last == some (byte! '.') then
    fail .fractionDigitExpected tokenEnd
  if let some next := next then
    expectDelimiter next tokenEnd.position
  sinkSlice .decimal tokenEnd content

@[inline]
private def finishNumeral (tokenEnd : TokenEnd) (content : Content) : LexM H m R E Unit :=
  sinkSlice .numeral tokenEnd content

/--
Sinks a hexadecimal/binary token.

The token's own shape is checked first, then that `next`, the byte
at the end (if there is one), delimits it.
-/
@[inline]
private def finishDigitRun (run : DigitRun) (tokenEnd : TokenEnd) (content : Content)
    (next : Option UInt8) : LexM H m R E Unit := do
  -- digit runs must not be empty
  if content.size (← getCore).tokenContent == 0 then
    fail run.emptyError tokenEnd
  if let some next := next then
    expectDelimiter next tokenEnd.position
  sinkSlice run.tokenType tokenEnd content

@[inline]
private def finishSimpleSymbol (tokenEnd : TokenEnd) (content : Content) : LexM H m R E Unit :=
  sinkSlice .unquotedSymbol tokenEnd content

/--
Sinks a keyword.

The token's own shape is checked first, then that `next`, the byte
at the end (if there is one), delimits it.
-/
@[inline]
private def finishKeyword (tokenEnd : TokenEnd) (content : Content) (next : Option UInt8) :
    LexM H m R E Unit := do
  -- ensure the keyword is not empty
  if content.size (← getCore).tokenContent == 0 then
    fail .forbiddenKeywordName tokenEnd
  if let some next := next then
    expectDelimiter next tokenEnd.position
  sinkSlice .keyword tokenEnd content

@[inline]
private def finishStringLiteral (tokenEnd : TokenEnd) (content : Content) : LexM H m R E Unit :=
  sinkSlice .string tokenEnd content

@[inline]
private def finishWhitespace (tokenEnd : TokenEnd) (content : Content) : LexM H m R E Unit :=
  sinkSlice .whitespace tokenEnd content

/- LEAN: Rust keeps the batch length, the line and the line start in locals of `lex_normal`.
Here the local is the batch itself, which the loop passes along; the line and the line start
stay in the lexer state, which the fast path only reads. While the loop holds the batch, the
lexer state has an empty batch, so the batch must be stored before anything else uses it:
the slow path, a flush, an error, or a return. The batch is a local of its own, not a field
of a structure of locals, so that it is not shared when it is changed. -/

/-- Puts the batch held by the loop back into the lexer state. -/
@[inline]
private def storeBatch (batch : TokenBatch) : LexM H m R E Unit :=
  modifyCore fun c => { c with batch }

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
private def pushFast (batch : TokenBatch) (offset : Nat) (base : USize)
    (ty : TokenCategory) (contentStart contentStop start «end» : USize) (emit : Bool) : LexM H m R E TokenBatch := do
  if !emit then
    return batch
  let c ← getCore
  let line := c.line
  let lineStart := c.lineStart
  let batch := batch.pushOnLine ty contentStart.toNat contentStop.toNat
    line lineStart (offset + (start - base).toNat) (offset + («end» - base).toNat)
  if batch.len == BATCH_CAPACITY then
    -- batch capacity reached, we need to flush the batch
    storeBatch batch
    flushBatch
    takeBatch
  else
    return batch

/--
Moves a fast-path symbol run that cannot be finished
in this slice to the stored path.

The token itself starts at `index`, its content either at `index`
(simple symbol) or `after` (quoted symbol, excludes pipe), and
the token continues at least to `runEndAt`, where it has been
left unfinished.
-/
private def storeUnfinishedSymbolRun (input : Input) (entry : UInt8) (index after runEndAt : USize) :
    LexM H m R E Unit := do
  startToken index
  if entry &&& FAST_PIPE != 0 then
    -- quoted symbol, skip the start pipe
    extendContent input after runEndAt
    setState .quotedSymbol
  else
    -- simple symbol, do not skip anything
    extendContent input index runEndAt
    setState .simpleSymbol

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
private def ContinuesWhitespace (input : Input) (position : USize) : Prop :=
  ∃ c, input.get? position = some c ∧ (c = byte! '\n' ∨ endsRun c RUN_NON_LF_WHITESPACE = false)

/-- The run ends after its start: the search has passed the start, or the byte where it continues
belongs to the run. -/
private theorem lt_whitespaceRunEnd {input : Input} {index start : USize} {c : UInt8}
    (hindex : index.toNat ≤ start.toNat)
    (hrun : index.toNat < start.toNat ∨ ContinuesWhitespace input start)
    (h : input.get? (runEnd input start RUN_NON_LF_WHITESPACE) = some c)
    (hc : ¬(c == byte! '\n') = true) :
    index.toNat < (runEnd input start RUN_NON_LF_WHITESPACE).toNat := by
  have hle := le_runEnd input start RUN_NON_LF_WHITESPACE
  rcases hrun with hlt | ⟨first, hfirst, hlf | hcontinues⟩
  · omega
  · -- the search stops at the line feed, where the byte is not one
    have : runEnd input start RUN_NON_LF_WHITESPACE ≠ start := by
      intro heq
      rw [heq, hfirst] at h
      cases h
      exact hc (by rw [hlf]; rfl)
    have : (runEnd input start RUN_NON_LF_WHITESPACE).toNat ≠ start.toNat :=
      fun heq => this (USize.toNat_inj.mp heq)
    omega
  · have := lt_runEnd RUN_NON_LF_WHITESPACE hfirst hcontinues
    omega

/- LEAN: the loop of `start_whitespace`, as a recursion on `«end»` that is shown to end.
`index` is where the run starts and `«end»` where the search for its end continues; the
search has passed `index` or the byte at `«end»` belongs to the run, so that the position
returned is after `index`, which `lexNormalFrom` is shown to end by. -/
private def startWhitespaceFrom (input : Input) (index «end» : USize)
    (hend : index.toNat ≤ «end».toNat ∧ «end».toNat ≤ input.stop.toNat)
    (hrun : index.toNat < «end».toNat ∨ ContinuesWhitespace input «end») :
    LexM H m R E { position : USize // index.toNat < position.toNat } := do
  -- find the first byte that is not whitespace other than a line feed
  let «end» := runEnd input «end» RUN_NON_LF_WHITESPACE
  -- the search goes on from where it was
  have : _ ≤ «end».toNat := le_runEnd input _ RUN_NON_LF_WHITESPACE
  match h : input.get? «end» with
  | some c =>
    if hc : c == byte! '\n' then
      -- the line feed is a part of the run, mark it and continue
      markLineFeedAt «end»
      have := Input.toNat_add_one_of_get? h
      startWhitespaceFrom input index («end» + 1) (by omega) (.inl (by omega))
    else
      -- the run has ended inside the slice
      finishWhitespace (.mkAtByte «end») (.borrow input index «end»)
      return ⟨«end», lt_whitespaceRunEnd hend.1 hrun h hc⟩
  | none =>
    -- we ran out of bytes, update the content and state
    extendContent input index input.stop
    setState .whitespace
    return ⟨input.stop, by
      rcases hrun with hlt | ⟨_, hfirst, _⟩
      · omega
      · have := Input.lt_stop_of_get? hfirst
        omega⟩
termination_by input.stop.toNat - «end».toNat
decreasing_by decreasing_position

/--
Lexes the whitespace run that starts at `index` of the slice,
to be handed over as a token.

Returns the position after the run. If the run ends inside the slice,
its token is sunk with borrowed content. Otherwise, the run is stored,
the state becomes `whitespace`, and the end of the slice is returned.
-/
private def startWhitespace (input : Input) (index : USize)
    (hrun : ContinuesWhitespace input index) :
    LexM H m R E { position : USize // index.toNat < position.toNat } := do
  startToken index
  have hindex : index.toNat ≤ input.stop.toNat := by
    have ⟨_, hfirst, _⟩ := hrun
    have := Input.lt_stop_of_get? hfirst
    omega
  startWhitespaceFrom input index index ⟨Nat.le_refl _, hindex⟩ (.inr hrun)

/- LEAN: the Rust function loops over the slice with `while let`; here the loop is the
recursion on `index`. Every arm that continues the loop in Rust calls `lexNormalFrom` again
at the new index, which is after `index`, with the locals loaded again after the slow path.
`offset` and `base` are the lexer's offset and base when the loop started, which stay the same
while the loop runs. The recursion is encoded as a well-founded one, which for a function this
long nests deeper than the default limit allows. -/
set_option maxRecDepth 2048 in
private def lexNormalFrom (input : Input) (offset : Nat) (base index : USize)
    (batch : TokenBatch) : LexM H m R E USize := do
  let some ⟨c, hc⟩ := (input.get? index).attach
    | do
      -- we have consumed every byte of the slice
      -- write the locals back before returning
      storeBatch batch
      return input.stop
  have := Input.toNat_add_one_of_get? hc
  -- A fast path handles the most common token types.
  -- It is determined by one table lookup. If the started token is not on
  -- the fast path, a slower path is taken, again looked up. Arms eagerly
  -- try to complete the token with the whole content borrowed from the slice,
  -- which resets the lexer back to the normal state, so the loop can continue.
  --
  -- Lexing only returns early if eager dispatch is not possible,
  -- typically due to running out of bytes in the slice.

  let after := index + 1
  -- Handle the parentheses first as they are numerous and
  -- need no special processing. The closing parenthesis is first
  -- as it forms more clusters.
  if c == byte! ')' then
    if (← getCore).recovers then
      -- saturate to avoid going below zero depth
      -- which would happen with too many closing parentheses
      modifyCore fun core => { core with lexedDepth := core.lexedDepth - 1 }
    let batch ← pushFast batch offset base .parenClose index after index after true
    return ← lexNormalFrom input offset base after batch
  if c == byte! '(' then
    if (← getCore).recovers then
      modifyCore fun core => { core with lexedDepth := core.lexedDepth + 1 }
    let batch ← pushFast batch offset base .parenOpen index after index after true
    return ← lexNormalFrom input offset base after batch
  -- Handle whitespace and symbols in a fast path.
  let fastEntry := fastFlags c
  if fastEntry &&& FAST_ON != 0 then
    -- Fast path, compute where the run ends and where the token ends.
    -- For quoted symbols, the token will end after the closing pipe.
    let runEndAt := runEnd input after (fastEntry &&& FAST_RUN_MASK)
    have : after.toNat ≤ runEndAt.toNat := le_runEnd input after _
    let isQuoted := fastEntry &&& FAST_PIPE != 0

    -- Check if we need to fall back to state-machine lexing
    -- if we have been asked to emit whitespace and are handling it.
    -- We need to fall back if we have overrun the slice or encountered
    -- a line-feed which needs to update the location line/column.
    let isWhitespace := fastEntry &&& RUN_NON_LF_WHITESPACE != 0
    let emitsWhitespace := (← consumesWhitespaceAndComments) && isWhitespace
    if hws : emitsWhitespace && (input.get? runEndAt).all (· == byte! '\n') then
      -- the whitespace token does not end on this line inside the slice
      storeBatch batch
      let ⟨index, hnext⟩ ← startWhitespace input index ⟨c, hc, .inr (not_endsRun_of_fastFlags (by
        simp only [emitsWhitespace, isWhitespace, fastEntry, Bool.and_eq_true] at hws
        exact hws.1.2))⟩
      if index == input.stop then
        -- we ran out of bytes inside the whitespace
        return index
      return ← lexNormalFrom input offset base index (← takeBatch)

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
      else fastEntry &&& RUN_SIMPLE_SYMBOL != 0
    if hunfinished : isUnfinished then
      -- write the locals back
      storeBatch batch
      storeUnfinishedSymbolRun input fastEntry index after runEndAt
      return runEndAt
    else
    let tokenEnd := if isQuoted then runEndAt + 1 else runEndAt
    have htokenEnd : runEndAt.toNat ≤ tokenEnd.toNat := by
      simp only [tokenEnd]
      split
      · rename_i hquoted
        have hpipe : input.get? runEndAt = some (byte! '|') := by
          simpa [isUnfinished, hquoted] using hunfinished
        rw [toNat_add_one_of_lt (Input.lt_stop_of_get? hpipe)]
        omega
      · omega

    -- No need to fall back, construct the token: the pipes delimit a quoted
    -- symbol but are not part of its content, any other fast token is its
    -- whole text. The token is on a single line as all fast-lex runs exclude
    -- newlines. Whitespace is only emitted if the consumer wants it.
    let (ty, contentStart, contentStop) :=
      if isQuoted then (TokenCategory.quotedSymbol, after, runEndAt)
      -- only emitted if the consumer takes whitespace
      else if emitsWhitespace then (TokenCategory.whitespace, index, tokenEnd)
      else (TokenCategory.unquotedSymbol, index, tokenEnd)
    let emit := fastEntry &&& FAST_EMIT != 0
    -- A token must be delimited by the byte after it,
    -- fall back to the state machine if the delimiter is not found.
    if emit then
      match input.get? tokenEnd with
      | some next =>
        -- the token ended inside the slice: the byte after it must delimit it
        if !isDelimiter next then
          storeBatch batch
          startToken index
          failAt .missingDelimiter (tokenEnd + 1)
      | none =>
        -- the token ended exactly at the slice end
        -- this must be a quoted symbol as the unquoted symbol
        -- has its token end inside the confirmed run
        -- the quoted symbol must wait for the delimiter
        storeBatch batch
        startToken index
        extendContent input contentStart contentStop
        setState .quotedSymbolClosed
        return tokenEnd
    -- whitespace needs no delimiter, it is emitted only if the consumer takes it
    let emit := emit || emitsWhitespace
    let batch ← pushFast batch offset base ty contentStart contentStop index tokenEnd emit
    -- Fast path done, continue normally after the token end.
    return ← lexNormalFrom input offset base tokenEnd batch

  -- The slow path will not use the locals, write them back.
  storeBatch batch

  -- Fast path was not taken, use the slow path.
  match hstart : startOf c with
  | .lineFeed =>
    if ← consumesWhitespaceAndComments then
      -- the line feed starts a whitespace token
      let ⟨index, hnext⟩ ← startWhitespace input index
        ⟨c, hc, .inl (eq_of_startOf_eq_lineFeed hstart)⟩
      if index == input.stop then
        return index
      lexNormalFrom input offset base index (← takeBatch)
    else
      -- line feeds must be marked for line offsets
      -- mark it and update the index
      markLineFeedAt index
      lexNormalFrom input offset base after (← takeBatch)
  | .comment =>
    -- a comment has been started
    -- process the run eagerly
    startToken index
    let «end» := runEnd input after RUN_COMMENT_PLAIN
    have : after.toNat ≤ «end».toNat := le_runEnd input after _
    match hbyte : input.get? «end» with
    | some c =>
      have := Input.toNat_add_one_of_get? hbyte
      if c == byte! '\n' then
        -- line feed, we need to mark it
        markLineFeedAt «end»
      -- otherwise a carriage return, which also ends the comment
      -- we have reached the end of the comment, which includes
      -- the byte that ended it but not its semicolon
      -- sink the content if it should be emitted
      if ← consumesWhitespaceAndComments then
        sinkSlice .comment (.mkAtByte («end» + 1)) (.borrow input after («end» + 1))
      -- update the index and continue the loop
      lexNormalFrom input offset base («end» + 1) (← takeBatch)
    | none =>
      -- we ran out of bytes while inside the comment
      -- extend the content if it should be emitted
      if ← consumesWhitespaceAndComments then
        extendContent input after «end»
      -- update the state and return
      setState .comment
      return «end»
  | .hash =>
    -- base selection
    startToken index
    let selected := (input.get? after).bind fun c =>
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
        setState .baseSelection
        return after
    -- the base has been selected, get a run of its digits
    let start := after + 1
    let afterEnd := runEnd input start run.flag
    have : start.toNat ≤ afterEnd.toNat := le_runEnd input start _
    have : start.toNat = after.toNat + 1 := by
      have ⟨_, hselection, _⟩ := Option.bind_eq_some_iff.mp hrun
      exact toNat_add_one_of_lt (Input.lt_stop_of_get? hselection)
    if afterEnd == input.stop then
      -- we ran out of bytes
      -- update the content and the state and return
      extendContent input start afterEnd
      setState run.state
      return afterEnd
    -- dispatch a token with borrowed content
    finishDigitRun run (.mkAtByte afterEnd) (.borrow input start afterEnd)
      (some (input.get afterEnd))
    -- update the index and continue the loop
    lexNormalFrom input offset base afterEnd (← takeBatch)
  | .quote =>
    -- starts a string literal
    startToken index
    if (← getCore).version == .v2_0 then
      -- SMT-LIB 2.0 has a different string-escape format
      -- than the subsequent versions, leave the fast path immediately
      setState .stringLiteral
      return after
    -- determine the run of content bytes
    let afterContentEnd := runEnd input after RUN_STRING_PLAIN
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
        have : after.toNat ≤ afterContentEnd.toNat := le_runEnd input after _
        simp only [closed] at hclosed
        split at hclosed
        · rename_i hquote
          have := Input.toNat_add_one_of_get? hquote
          split at hclosed
          · split at hclosed
            · split at hclosed
              · cases hclosed
                omega
              · cases hclosed
            · cases hclosed
          · cases hclosed
        · cases hclosed
      -- definitely closed by a quote not followed by another quote
      -- borrow the string literal content and produce a token
      expectDelimiter next afterQuote
      finishStringLiteral (.mkAtByte afterQuote) (.borrow input after afterContentEnd)
      -- the closing quote is not part of the content,
      -- but was also processed
      lexNormalFrom input offset base afterQuote (← takeBatch)
    | none =>
      -- we cannot borrow the content
      -- update the content and state and return
      extendContent input after afterContentEnd
      setState .stringLiteral
      return afterContentEnd
  | .colon =>
    -- starts a keyword
    startToken index
    -- get a run of simple-symbol bytes
    let afterEnd := runEnd input after RUN_SIMPLE_SYMBOL
    have : after.toNat ≤ afterEnd.toNat := le_runEnd input after _
    if afterEnd == input.stop then
      -- we ran out of bytes
      -- update the content and state and return
      extendContent input after afterEnd
      setState .keyword
      return afterEnd
    -- dispatch a token with borrowed content
    finishKeyword (.mkAtByte afterEnd) (.borrow input after afterEnd)
      (some (input.get afterEnd))
    -- update the index and continue the loop
    lexNormalFrom input offset base afterEnd (← takeBatch)
  | .digit =>
    startToken index
    -- determine the run of digits
    let afterEnd := runEnd input after RUN_DIGIT
    have : after.toNat ≤ afterEnd.toNat := le_runEnd input after _
    -- check that we are not in a leading zero condition,
    -- which is only possible if the first character was zero
    -- and there is a subsequent digit;
    -- it is possible we will not be able to decide it here
    -- if the slice ends with a single zero, so we need to handle that
    -- when lexing digit in the state `numeralOrDecimal`
    if c == byte! '0' && afterEnd > after then
      failAt .numeralLeadingZero (after + 1)
    match hnext : input.get? afterEnd with
    | some next =>
      if next == byte! '.' then
        -- a dot starts a fraction, try to do a subsequent run of fraction digits
        let afterFractionEnd := runEnd input (afterEnd + 1) RUN_DIGIT
        have : (afterEnd + 1).toNat ≤ afterFractionEnd.toNat :=
          le_runEnd input _ _
        have := Input.toNat_add_one_of_get? hnext
        if afterFractionEnd == input.stop then
          -- we ran out of bytes
          -- update the content and state and return
          extendContent input index afterFractionEnd
          setState .fraction
          return afterFractionEnd
        -- dispatch a decimal token with borrowed content
        finishDecimal (.mkAtByte afterFractionEnd) (.borrow input index afterFractionEnd)
          (some (input.get afterFractionEnd))
        -- update the index and continue the loop
        lexNormalFrom input offset base afterFractionEnd (← takeBatch)
      else
        -- the numeral is not actually a decimal and ends
        -- dispatch a numeral token with borrowed content
        expectDelimiter next afterEnd
        finishNumeral (.mkAtByte afterEnd) (.borrow input index afterEnd)
        -- update the index and continue the loop
        lexNormalFrom input offset base afterEnd (← takeBatch)
    | none =>
      -- we ran out of bytes
      -- update the content and state and return
      extendContent input index afterEnd
      setState .numeralOrDecimal
      return afterEnd
  | .other | .whitespace | .parenOpen | .parenClose | .symbol | .pipe =>
    -- can actually only be other (resulting in unexpected character),
    -- as the other arms have already been handled in the fast path.
    startToken index
    failAt .unexpectedCharacter after
termination_by input.stop.toNat - index.toNat
decreasing_by all_goals decreasing_position

private def lexNormal (input : Input) (start : USize) : LexM H m R E USize := do
  -- use locals for variables commonly used on the fast path
  let c ← getCore
  let offset := c.offset
  let base := c.base
  lexNormalFrom input offset base start (← takeBatch)

/- LEAN: each of the following steps lexes the input from `start`, where Rust's step gets the
rest of the slice; a position that is 0 in Rust is `start` here, and a step returns the
position up to which it has consumed the input, where Rust returns the number of bytes. -/

private def lexFractionFrom (input : Input) (start : USize) : LexM H m R E USize := do
  -- find the first byte in the remainder that is not a digit
  let «end» := runEnd input start RUN_DIGIT
  -- extend the token from slice
  extendContent input start «end»
  if «end» < input.stop then
    -- we have successfully consumed the fraction, finish the decimal
    finishDecimal (.mkAtByte «end») .stored (some (input.get «end»))
    setState .normal
  else
    -- we ran out of bytes for now
    setState .fraction
  return «end»

private def lexNumeralOrDecimal (input : Input) (start : USize) : LexM H m R E USize := do
  -- find the first byte that is not a digit
  let index := runEnd input start RUN_DIGIT

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

  match input.get? index with
  | some next =>
    if next == byte! '.' then
      -- decimal, the next character will start fraction
      -- add the dot and immediately start lexing the fraction after it
      pushContent (byte! '.')
      lexFractionFrom input (index + 1)
    else
      -- we have successfully consumed the numeral, finish it
      expectDelimiter next index
      finishNumeral (.mkAtByte index) .stored
      -- move back to normal lexer state, not consuming the current byte
      setState .normal
      return index
  | none =>
    -- we have run out of bytes for now
    return index

private def lexBaseSelection (input : Input) (start : USize) : LexM H m R E USize := do
  let c := input.get start
  if c == byte! 'x' then
    setState .hexadecimal
  else if c == byte! 'b' then
    setState .binary
  else
    failAt .baseSelectionExpected (start + 1)
  return start + 1

/-- Lexes a digit run, either hexadecimal or binary. -/
private def lexDigitRun (input : Input) (start : USize) (run : DigitRun) : LexM H m R E USize := do
  -- find the first byte that is not allowed in the run
  let index := runEnd input start run.flag
  -- extend the token from slice
  extendContent input start index
  if index < input.stop then
    -- we have successfully consumed the digit run, finish it
    finishDigitRun run (.mkAtByte index) .stored (some (input.get index))
    setState .normal
  return index

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
private def lexStringLiteralLegacy (input : Input) (consumed : USize) :
    LexM H m R E USize := do
  let some ⟨first, hfirst⟩ := (input.get? consumed).attach
    | return consumed
  have := Input.toNat_add_one_of_get? hfirst
  let mut consumed : { position : USize // consumed.toNat ≤ position.toNat } :=
    ⟨consumed, Nat.le_refl _⟩
  match (← getCore).state with
  | .stringLiteralDoubleQuote =>
    -- expect a delimiter and finish the previously ended token
    expectDelimiter first consumed
    finishStringLiteral (.mkAtByte consumed) .stored
    -- set lexer to normal state and return, not consuming the current byte
    setState .normal
    return consumed
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
    setState .stringLiteral
  | _ => pure ()

  -- find the first byte that does not belong to string nor quoted
  -- this means backslash and pipe end the run as well, so we can act on them
  let index := runEndAll input consumed (RUN_STRING_PLAIN ||| RUN_QUOTED_PLAIN)
  have : consumed.1.toNat ≤ index.toNat := le_runEndAll input _ _
  have := consumed.2

  let some ⟨c, hc⟩ := (input.get? index).attach
    | do
      -- extend the content with the rest
      extendContent input consumed input.stop
      -- we have nothing more to consume, return
      return input.stop

  let addRunEnding ←
    if c == byte! '\n' then do
      -- mark the line feed
      markLineFeedAt index
      -- it belongs to the string, add it and continue lexing
      pure true
    else if c == byte! '"' then do
      -- put the lexer in the double-quote state
      -- do not add the quote, it is not part of the content
      setState .stringLiteralDoubleQuote
      pure false
    else if c == byte! '\\' then do
      -- put the lexer in the backslash-escape state
      -- do not add the backslash yet
      -- it may or may not be part of the content
      -- depending on if it truly is a backslash escape or not
      setState .stringLiteralBackslashEscape
      pure false
    else if c == byte! '|' then
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
  have := Input.toNat_add_one_of_get? hc
  lexStringLiteralLegacy input (index + 1)
termination_by input.stop.toNat - consumed.toNat
decreasing_by decreasing_position

/-- Lexes the string literal. -/
private def lexStringLiteralFrom (input : Input) (consumed : USize) :
    LexM H m R E USize := do
  let some ⟨first, hfirst⟩ := (input.get? consumed).attach
    | return consumed
  have := Input.toNat_add_one_of_get? hfirst
  let mut consumed : { position : USize // consumed.toNat ≤ position.toNat } :=
    ⟨consumed, Nat.le_refl _⟩
  if (← getCore).state == .stringLiteralDoubleQuote then
    -- we need to react to the literal being closed by a previous double-quote
    -- look at the first byte
    if first != byte! '"' then
      -- the previous character was really a quote ending the string literal
      -- finish the previously ended token
      expectDelimiter first consumed
      finishStringLiteral (.mkAtByte consumed) .stored
      -- set lexer to normal state and return, not consuming the current byte
      setState .normal
      return consumed
    else
      -- this has been a double-quote escape
      -- consume the first byte
      consumed := ⟨consumed.1 + 1, by simp +zetaDelta only; omega⟩
      -- push a double-quote byte (just one, we encountered two)
      pushContent (byte! '"')
      -- return to string-literal state and continue lexing
      setState .stringLiteral

  -- find the first byte that is not a plain string byte
  let index := runEnd input consumed RUN_STRING_PLAIN
  have : consumed.1.toNat ≤ index.toNat := le_runEnd input _ _
  have := consumed.2

  match hc : input.get? index with
  | some c =>
    have := Input.toNat_add_one_of_get? hc
    if c == byte! '\n' then
      -- mark the line feed
      markLineFeedAt index
      -- extend with & consume the run including the line feed
      extendContent input consumed (index + 1)
      -- continue lexing
      lexStringLiteralFrom input (index + 1)
    else if c == byte! '"' then
      -- we have a double quote in string literal
      -- only extend the content with bytes before it
      extendContent input consumed index
      -- the quote may be followed by another double quote for escaping
      -- otherwise, it will end the string literal
      -- put the lexer in a special state to handle the next character
      setState .stringLiteralDoubleQuote
      -- consume the quote and everything before it, continue lexing
      lexStringLiteralFrom input (index + 1)
    else
      -- forbidden, not printable or whitespace
      failAt .forbiddenCharInString (index + 1)
  | none =>
    -- extend the content with the rest
    extendContent input consumed input.stop
    -- we have nothing more to consume, return
    return input.stop
termination_by input.stop.toNat - consumed.toNat
decreasing_by all_goals decreasing_position

/-- Lexes the string literal. -/
private def lexStringLiteral (input : Input) (start : USize) : LexM H m R E USize := do
  if (← getCore).version == .v2_0 then
    -- in 2.0 mode, the string literals are lexed differently,
    -- hand over to the legacy lexing function
    lexStringLiteralLegacy input start
  else
    lexStringLiteralFrom input start

private def lexSimpleSymbol (input : Input) (start : USize) : LexM H m R E USize := do
  -- find the first byte that is not a simple symbol
  let index := runEnd input start RUN_SIMPLE_SYMBOL
  -- extend the token from slice
  extendContent input start index
  if index < input.stop then
    -- we have successfully consumed the symbol, finish it
    expectDelimiter (input.get index) index
    finishSimpleSymbol (.mkAtByte index) .stored
    setState .normal
  return index

private def lexQuotedSymbol (input : Input) (consumed : USize) : LexM H m R E USize := do
  -- find the first byte that is not a quoted symbol
  let index := runEnd input consumed RUN_QUOTED_PLAIN
  have : consumed.toNat ≤ index.toNat := le_runEnd input _ _

  -- inspect the problematic byte
  match hc : input.get? index with
  | some c =>
    have := Input.toNat_add_one_of_get? hc
    let afterSlicePosition := index + 1
    if c == byte! '|' then
      -- end of quoted symbol, extend its content
      extendContent input consumed index
      -- the byte after the pipe must delimit the token before it is sunk
      match input.get? afterSlicePosition with
      | some next =>
        expectDelimiter next afterSlicePosition
        sinkSlice .quotedSymbol (.mkAtByte afterSlicePosition) .stored
        setState .normal
      | none =>
        -- we do not have the next byte available,
        -- move to the state expecting it to be a delimiter
        setState .quotedSymbolClosed
      -- consume the bytes including the pipe
      return afterSlicePosition
    else if c == byte! '\\' then
      -- backslash is forbidden in quoted symbols
      failAt .backslashInQuotedSymbol afterSlicePosition
    else if c == byte! '\n' then
      -- mark the line feed at the given position
      markLineFeedAt index
      -- prepare for the next run
      -- move everything including this LF to token content
      extendContent input consumed afterSlicePosition
      lexQuotedSymbol input afterSlicePosition
    else
      -- forbidden character
      failAt .forbiddenCharInQuotedSymbol afterSlicePosition
  | none =>
    -- we ran out of bytes before the token ended
    -- extend content and keep the quoted symbol state
    extendContent input consumed input.stop
    return input.stop
termination_by input.stop.toNat - consumed.toNat
decreasing_by decreasing_position

private def lexKeyword (input : Input) (start : USize) : LexM H m R E USize := do
  -- find the first byte that is not simple-symbol-like
  let index := runEnd input start RUN_SIMPLE_SYMBOL

  -- extend the token from slice
  extendContent input start index

  if index < input.stop then
    -- we have successfully consumed the keyword, finish it
    finishKeyword (.mkAtByte index) .stored (some (input.get index))
    setState .normal
  return index

private def lexQuotedSymbolClosed (input : Input) (start : USize) : LexM H m R E USize := do
  -- we expect a token delimiter to follow the closing pipe
  expectDelimiter (input.get start) start
  -- all good, produce the quoted symbol token
  sinkSlice .quotedSymbol (.mkAtByte start) .stored
  -- the delimiter is not consumed
  setState .normal
  return start

/- LEAN: the loop of `lex_whitespace` is the recursion on `start`, shown to end as
`lexNormalFrom` is. -/
private def lexWhitespace (input : Input) (start : USize) : LexM H m R E USize := do
  -- we know that the consumer is interested in the whitespace
  -- as it would otherwise be immediately discarded instead
  -- of the state change
  -- find the first byte that is not non-LF whitespace
  let index := runEnd input start RUN_NON_LF_WHITESPACE
  have : start.toNat ≤ index.toNat := le_runEnd input _ _
  -- inspect the problematic byte
  match hc : input.get? index with
  | some c =>
    have := Input.toNat_add_one_of_get? hc
    if c == byte! '\n' then
      -- mark the line feed at the given position
      markLineFeedAt index
      -- prepare for the next run
      -- extend the token content with everything including this LF
      extendContent input start (index + 1)
      lexWhitespace input (index + 1)
    else
      -- end of whitespace
      -- extend and finish the token
      extendContent input start index
      finishWhitespace (.mkAtByte index) .stored
      -- go back to normal state, consuming the whitespace
      setState .normal
      return index
  | none =>
    -- we ran out of bytes before the token ended
    -- extend the token content with everything
    -- keep the whitespace state
    extendContent input start input.stop
    return input.stop
termination_by input.stop.toNat - start.toNat
decreasing_by decreasing_position

private def lexComment (input : Input) (start : USize) : LexM H m R E USize := do
  -- run until comment end
  let index := runEnd input start RUN_COMMENT_PLAIN
  let some c := input.get? index
    | do
      -- the comment continues; if we are producing comments,
      -- extend the content from the whole slice
      if ← consumesWhitespaceAndComments then
        extendContent input start input.stop
      -- remain in comment state
      return input.stop

  -- the comment has ended, either by CR or LF
  -- if it ended by LF, we must mark it
  if c == byte! '\n' then
    markLineFeedAt index

  let afterCommentEnd := index + 1

  if ← consumesWhitespaceAndComments then
    -- we need to produce the comment token
    -- extend the comment content and finish the token
    extendContent input start afterCommentEnd
    sinkSlice .comment (.mkAtByte afterCommentEnd) .stored

  -- move back to the normal state and return
  setState .normal
  return afterCommentEnd

/--
Lexes the input from `start`, which is below its end, in the current state, returning the
position up to which the input was consumed.
-/
private def lexStep (input : Input) (start : USize) : LexM H m R E USize := do
  match (← getCore).state with
  | .normal => lexNormal input start
  | .numeralOrDecimal => lexNumeralOrDecimal input start
  | .fraction => lexFractionFrom input start
  | .baseSelection => lexBaseSelection input start
  | .hexadecimal => lexDigitRun input start HEXADECIMAL_RUN
  | .binary => lexDigitRun input start BINARY_RUN
  | .stringLiteral | .stringLiteralDoubleQuote | .stringLiteralBackslashEscape =>
    lexStringLiteral input start
  | .simpleSymbol => lexSimpleSymbol input start
  | .quotedSymbol => lexQuotedSymbol input start
  | .keyword => lexKeyword input start
  | .comment => lexComment input start
  | .whitespace => lexWhitespace input start
  | .quotedSymbolClosed => lexQuotedSymbolClosed input start

/--
Moves the lexer back to `location`, which the tokens handed over
so far end at, discarding whatever was lexed beyond it; `position` is its position in the
input.
-/
private def resumeAt (location : Location) (position : USize) : InnerM H m Unit :=
  -- the region after the location was lexed once already,
  -- restore all bookkeeping
  -- a stop inside an arm leaves it mid-token
  modifyThe LexerCore fun c =>
    { c with
      offset := location.offset
      base := position
      line := location.line
      lineStart := location.offset - location.column
      state := .normal
      tokenContent := c.tokenContent.clear }

/- LEAN: the loop of `lex_slice_inner`, `partial` as a relex request moves it back in the
slice. `position` is where the part of the input not lexed yet starts, the lexer's base, and
`fnResult` the result to return once the batch is handed over. The `.run` of an action in
`LexM` gives its interruption as a value, the counterpart of matching on the `Result` in
Rust. -/
private partial def lexSliceLoop (input : Input) (initialOffset : Nat) (position : USize)
    (fnResult : Except (Failure E) (ControlFlow R)) :
    InnerM H m (Except (Failure E) (ControlFlow R)) := do
  let failed := match fnResult with
    | .error _ => true
    | .ok _ => false
  /- LEAN: `none` stands for a batch handed over without an interruption, `some` for the
  position up to which a step consumed the input. -/
  let result : Except (Interrupted R E) (Option USize) ← if position ≥ input.stop || failed then do
      -- hand over the batch
      let flushed ← (flushBatch (m := m) (R := R) (E := E)).run
      pure (flushed.map fun () => none)
    else do
      let stepped ← (lexStep input position).run
      pure (stepped.map some)

  match result with
  | .ok none =>
    -- we are done
    return fnResult
  | .ok (some next) =>
    -- advance the offset by the number of consumed bytes
    -- the line positions are updated by the arm functions above
    modifyThe LexerCore fun c => { c with offset := c.offsetAt next, base := next }
    -- move after consumed bytes, continue consuming
    lexSliceLoop input initialOffset next fnResult
  | .error interrupted =>
    match interrupted.result with
    | .ok stop =>
      let location := interrupted.location
      -- every handed-over token is in this slice
      -- so the location must be equal or greater to initial offset
      -- compute this even for finished to assert the interrupted location
      if location.offset < initialOffset then
        return .error { cause := .internal .stoppedBeforeStart, location }
      let position := input.start + USize.ofNat (location.offset - initialOffset)
      resumeAt location position
      match stop with
      | .relex =>
        -- everything up to the position was already consumed
        -- continue from there
        lexSliceLoop input initialOffset position (.ok .continue)
      | .finished result =>
        -- the consumer is done: the batch was handed over,
        -- the rest of the slice stays unlexed
        -- the lexer discards it and everything fed until the end of the input
        return .ok (.break result)
    | .error cause =>
      -- make sure the tokens before the error get handed over
      lexSliceLoop input initialOffset position (.error { cause, location := interrupted.location })

private def lexSliceInner (input : Input) :
    InnerM H m (Except (Failure E) (ControlFlow R)) := do
  let initialOffset := (← getThe LexerCore).offset
  -- the slice starts at the lexer's offset,
  -- and the tokens borrowed from it have their contents in its array
  modifyThe LexerCore fun c =>
    let batch := c.batch
    let c := { c with batch := default }
    { c with base := input.start, batch := { batch with bytes := input.bytes } }
  lexSliceLoop input initialOffset input.start (.ok .continue)

/-- Resets the lexer to the initial state, including the location and version. -/
private def reset : InnerM H m Unit :=
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
      lineStart := 0 }

private def lexEofInner : InnerM H m (Except (Failure E) (ControlFlow R)) := do
  -- EOF is a token delimiter, we need to produce the token
  -- that waits for a delimiter if there is any
  -- there is no input at the end of the file, positions are relative to the offset
  modifyThe LexerCore fun c => { c with base := 0 }
  let pending : LexM H m R E Unit := do
    match (← getCore).state with
    | .normal =>
      -- nothing to do
      pure ()
    | .quotedSymbolClosed =>
      -- the end of the input is a token delimiter,
      -- produce the quoted symbol
      sinkSlice .quotedSymbol TokenEnd.EOF .stored
    | .fraction => finishDecimal TokenEnd.EOF .stored none
    | .numeralOrDecimal => finishNumeral TokenEnd.EOF .stored
    | .hexadecimal => finishDigitRun HEXADECIMAL_RUN TokenEnd.EOF .stored none
    | .binary => finishDigitRun BINARY_RUN TokenEnd.EOF .stored none
    | .baseSelection =>
      -- hash without selection following it
      fail .baseSelectionExpected TokenEnd.EOF
    | .stringLiteral | .stringLiteralBackslashEscape =>
      -- we are still within the string literal
      -- forbidden as the literal must be totally enclosed by double quotes
      fail .unclosedStringLiteral TokenEnd.EOF
    | .stringLiteralDoubleQuote =>
      -- string literal has ended by the previous character,
      -- a quote directly before the end of the file
      -- this works both for 2.0 and 2.5+
      finishStringLiteral TokenEnd.EOF .stored
    | .simpleSymbol => finishSimpleSymbol TokenEnd.EOF .stored
    | .keyword => finishKeyword TokenEnd.EOF .stored none
    | .quotedSymbol =>
      -- EOF forbidden as the symbol must be totally enclosed by pipes
      fail .unclosedQuotedSymbol TokenEnd.EOF
    | .whitespace =>
      -- we can only be in this state if the consumer wants the
      -- whitespace to be emitted, so sink it
      sinkSlice .whitespace TokenEnd.EOF .stored
    | .comment =>
      -- only produce the comment if the consumer wants it
      if ← consumesWhitespaceAndComments then
        sinkSlice .comment TokenEnd.EOF .stored
  let step : LexM H m R E Unit := do
    -- if we were told to relex, treat it as a normal continuation,
    -- as there is nothing to relex (we are at the end of input)
    tryCatch pending fun interrupted =>
      match interrupted.result with
      | .ok .relex => pure ()
      | _ => throw interrupted
    -- everything has been processed, start the EOF token and sink it
    startToken 0
    sinkEof

  match ← step.run with
  | .ok () =>
    -- everything processed, there was no break out
    -- the lexer will be reset outside, just continue
    return .ok .continue
  | .error interrupted =>
    match interrupted.result with
    | .error cause => return .error { cause, location := interrupted.location }
    | .ok .relex =>
      -- we were asked to relex, but the file is ending anyway, nothing to relex
      return .ok .continue
    | .ok (.finished result) =>
      -- the consumer is done with the input
      -- the lexer will be reset outside
      return .ok (.break result)

/-- Executes an inner lexer step, adding the break location to its result. -/
private def executeStep (step : InnerM H m (Except (Failure E) (ControlFlow R))) :
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
private def failCall (abandon : Location → StateT H m Unit) (failure : Failure E) (atEnd : Bool) :
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
      | .internal _ => .plain

  -- start recovering from the given failure location
  -- there is no slice being lexed, so its position is zero
  resumeAt failure.location 0
  abandon failure.location
  modifyThe LexerCore fun c => { c with recoveryState := some skip }
  return { cause := failure.cause, continuesFrom := some failure.location }

/-- What skipping goes through, see `skipBytes`. -/
private structure Skipping where
  skip : RecoveryState
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
private def skipBytes (bytes : ByteSlice) (legacy : Bool) (offset index : Nat)
    (skipping : Skipping) : Option Nat × Skipping :=
  if h : index < bytes.size then
    let c := bytes[index]
    -- the state after the byte, or the position where the recovery was made
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

Returns the position in the slice where the recovery was made,
or returns `none` if it has not yet been done.
-/
private def skipSlice (slice : ByteSlice) (skip : RecoveryState) : InnerM H m (Option Nat) := do
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
      lineStart := skipping.lineStart }
    return some position
  | (none, skipping) =>
    -- we ran out of bytes, update the offset and what is being skipped
    set { c with
      offset := c.offset + slice.size
      consumedDepth := skipping.depth
      line := skipping.line
      lineStart := skipping.lineStart
      recoveryState := some skipping.skip }
    return none

/- LEAN: Rust finds the last line feed with `rposition` and counts the line feeds in a second
pass; here one pass does both. -/
/-- The number of line feeds in the bytes, and the position after the last one, if any. -/
private def countLineFeeds (bytes : ByteSlice) : Nat × Option Nat :=
  let rec loop (i count : Nat) (afterLast : Option Nat) : Nat × Option Nat :=
    if h : i < bytes.size then
      if bytes[i] == byte! '\n' then loop (i + 1) (count + 1) (some (i + 1))
      else loop (i + 1) count afterLast
    else
      (count, afterLast)
  termination_by bytes.size - i
  loop 0 0 none

/-- Discards the bytes while keeping the location correct. -/
private def discardBytes (bytes : ByteSlice) : InnerM H m Unit :=
  -- the line feeds must be counted for the location to stay correct
  -- if there is a line feed, the line starts after the last one
  modifyThe LexerCore fun c =>
    let c := match countLineFeeds bytes with
      | (lineFeeds, some afterLast) =>
        { c with line := c.line + lineFeeds, lineStart := c.offset + afterLast }
      | (_, none) => c
    { c with offset := c.offset + bytes.size }

/- LEAN: the consumer's recovery methods are passed in, those of `LexRecovery`; they are only
called by a recovering lexer. -/
/-- Lexes the slice, or discards it if the consumer has finished. -/
private def lexSliceStep (abandon recover : Location → StateT H m Unit) (slice : ByteSlice) :
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
  let location := (← getThe LexerCore).currentLocation
  -- call inner lexing and fail on error
  let result ← match Input.ofSlice? slice with
    | some input => executeStep (lexSliceInner input)
    | none => pure (.error { cause := .internal .sliceTooLarge, location })
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
private def lexEofStep (abandon recover : Location → StateT H m Unit) :
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
      batch := TokenBatch.empty BATCH_CAPACITY } }

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
private def run [Monad m] (self : Lexer H recovery) (step : InnerM H m α) :
    m (α × Lexer H recovery) := do
  let { handler, core } := self
  let ((result, core), handler) ← (step.run core).run handler
  return (result, { handler, core })

end BSmtLib.Lexer

namespace BSmtLib

/- LEAN: what Rust's `&mut self` leaves usable after a call that failed: the type of the
recovering lexer, and nothing for a lexer that stops at its first error, whose further calls
panic in Rust. -/
/--
What a lexer call that failed gives back: nothing for a lexer that stops
at its first error, which cannot be used again, and the lexer itself for a
recovering one, from which the rest of the input is to be fed.
-/
def Lexer.AfterError (H : Type) : Recovery → Type
  | .failFast => Unit
  | .recovering => Lexer H .recovering

/--
A recovering lexer whose end of the input raised an error.

The input has ended, so only the end of the input can be lexed again,
which completes the recovery.
-/
structure Lexer.PendingEof (H : Type) where
  private mk ::
  private lexer : Lexer H .recovering

/- LEAN: what Rust's `&mut self` leaves usable after `lex_eof` failed. Rust panics on a
non-empty slice fed to a recovering lexer whose end of the input failed and continues. -/
/--
What a recovering lexer gives back after its end of the input failed: the
lexer, if the error is final, or the lexer that can only lex the end of the
input again, if the error continues at the end.
-/
inductive Lexer.AfterEof (H : Type) where
  | lexer (lexer : Lexer H .recovering)
  | pending (pending : Lexer.PendingEof H)

/--
What a lexer gives back after its end of the input failed: nothing for a
lexer that stops at its first error, and what remains of a recovering one.
-/
def Lexer.AfterEofError (H : Type) : Recovery → Type
  | .failFast => Unit
  | .recovering => Lexer.AfterEof H

namespace Lexer

private def afterError : {recovery : Recovery} → Lexer H recovery → AfterError H recovery
  | .failFast, _ => ()
  | .recovering, lexer => lexer

private def afterEofError : {recovery : Recovery} → Lexer H recovery → (continues : Bool) →
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

end BSmtLib

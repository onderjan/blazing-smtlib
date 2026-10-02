import BlazingSmtlib.Read.Lexer.CharClass
import BlazingSmtlib.Read.Lexer.Error
import BlazingSmtlib.Read.Lexer.Helpers
import BlazingSmtlib.Token

namespace BlazingSmtlib.Read.Lexer

open BlazingSmtlib BlazingSmtlib.Token

/-- Maximal number of tokens that can be batched. -/
def BATCH_CAPACITY : Nat := 256

/-- Why lexing stopped before the end of the slice. -/
inductive Stop (R : Type) where
  /-- The handler requested lexing again from the stop location. -/
  | relex
  /-- The handler finished with a result at the stop location. -/
  | finished (result : R)

structure Interrupted (R E : Type) where
  result : Except (LexError E) (Stop R)
  location : SmtLocation

/- LEAN: a default value is needed for the functions marked `partial` in the lexer's monad; it
cannot be derived without one for the handler's result type. -/
instance : Inhabited (Interrupted R E) := ⟨{ result := .ok .relex, location := default }⟩

/- LEAN: the fields of the Rust `Lexer` except the handler, which the lexer's monad keeps
separately (see `LexM`). The lexer states are documented at `LexerState` in Rust. The
batch lives here instead of in a local of `lex_slice_inner`, so that its storage is reused
from one slice to the next; it is empty whenever lexing returns. -/
structure LexerCore where
  /-- The SMT-LIB version the lexer currently operates under. -/
  version : SmtVersion
  /-- The initial SMT-LIB version the lexer will reset to. -/
  initialVersion : SmtVersion
  /-- Current lexer state. -/
  state : LexerState
  /-- Location of the start of the currently-processed token. -/
  tokenStart : SmtLocation
  /-- The currently-built string content of the currently-processed token. -/
  tokenContent : ContentBuffer
  /--
  Offset of the start of the byte being processed during lexing.

  It only advances after byte consumption.
  -/
  offset : Nat
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

structure Lexer (H : Type) where
  private mk ::
  /-- Handler of produced tokens. -/
  private handler : H
  private core : LexerCore

/- LEAN: Rust's lexer methods take `&mut self` and return `Result<usize, Interrupted<..>>`,
using `?` to pass an interruption up. In Lean the same is a monad: `StateT LexerCore` holds
the lexer's fields as mutable state, `StateT H` the handler, and `ExceptT (Interrupted R E)`
is the `Err` that `throw` raises and that passes up through every `←` like `?`. `ExceptT` is
outermost so that the lexer's fields keep their changes when an interruption is thrown, as
in Rust. The handler is a separate state so that it can be handed to `handleTokens` without
another reference to it remaining in the lexer's state, which would make the handler's
updates copy it. -/
abbrev InnerM (H : Type) (m : Type → Type) := StateT LexerCore (StateT H m)

abbrev LexM (H : Type) (m : Type → Type) (R E : Type) := ExceptT (Interrupted R E) (InnerM H m)

/-- Location of `position` in the current slice.

Every line feed before `position` must be marked before calling this. -/
@[inline]
def LexerCore.locationAt (self : LexerCore) (position : Nat) : SmtLocation :=
  let offset := self.offset + position
  { offset, line := self.line, column := offset - self.lineStart }

/-- The byte at `index` of the slice, if any. -/
@[inline]
private def byteAt? (slice : ByteSlice) (index : Nat) : Option UInt8 :=
  if index < sliceSize slice then some (sliceGet slice index) else none

/-- Whether the byte is an ASCII digit. -/
@[inline]
private def isAsciiDigit (c : UInt8) : Bool :=
  byte! '0' ≤ c && c ≤ byte! '9'

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [TokenHandler H m R E]

/- LEAN: `getThe` and `modifyThe` name the state they access, as there are two. Reading the
state with `← core` gives a reference to it; the code below lets such references die before
the state is modified, so that it is modified in place and not copied. -/
@[inline]
private def core : LexM H m R E LexerCore :=
  getThe LexerCore

@[inline]
private def modifyCore (f : LexerCore → LexerCore) : LexM H m R E Unit :=
  modifyThe LexerCore f

@[inline]
private def setState (state : LexerState) : LexM H m R E Unit :=
  modifyCore fun c => { c with state }

/- LEAN: the content buffer and the batch are taken out of the state before they are changed:
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
private def extendContent (slice : ByteSlice) : LexM H m R E Unit :=
  modifyContent (·.extendFromSlice slice)

@[inline]
private def pushContent (c : UInt8) : LexM H m R E Unit :=
  modifyContent (·.push c)

@[inline]
private def startToken (position : Nat) : LexM H m R E Unit := do
  -- update the token start to the computed location
  modifyCore fun c => { c with tokenStart := c.locationAt position }
  -- clear the token string
  modifyContent (·.clear)

@[inline]
private def markLineFeedAt (position : Nat) : LexM H m R E Unit :=
  -- when lexing a run, this is used to mark a line feed
  -- the locations must only refer to positions after it afterwards
  modifyCore fun c => { c with line := c.line + 1, lineStart := c.offset + position + 1 }

/--
Fails with an error spanning the token up to `position`.

Used for errors detected mid-run, e.g. forbidden byte in a string
or a backslash in a quoted symbol.
-/
private def failAt (kind : LexerErrorKind) (position : Nat) : LexM H m R E α := do
  let c ← core
  let «end» := c.locationAt position
  let span := SmtSpan.newUnchecked c.tokenStart «end»
  -- no tokens have been consumed, as this is an error
  -- that occurred during lexing
  throw { result := .error (.lexer { kind, span }), location := «end» }

/-- Fails with an error spanning the token so far and, if it ended at a byte, that byte. -/
private def fail (kind : LexerErrorKind) (tokenEnd : TokenEnd) : LexM H m R E α :=
  failAt kind (tokenEnd.position + if tokenEnd.atByte then 1 else 0)

/- LEAN: raises what is a panic in Rust, see `InternalError`. -/
/-- Fails with an internal error at the current location. -/
private def failInternal (error : InternalError) : LexM H m R E α := do
  throw { result := .error (.internal error), location := (← core).locationAt 0 }

/--
Checks that `next`, the byte at `position` right after a token,
delimits it.

Called before the token is handed over, so that a token without its
delimiter never reaches the handler; the error spans the token and
the offending byte.
-/
@[inline]
private def expectDelimiter (next : UInt8) (position : Nat) : LexM H m R E Unit := do
  unless isDelimiter next do
    failAt .missingDelimiter (position + 1)

/- LEAN: runs the handler on the cursor. `handleTokens.run.run cursor` unwraps the handler's
monad down to a `StateT H m` action, which the `←` lifts into the lexer's monad, where the
handler is the inner state. -/
private def callHandler (cursor : TokenCursor) :
    LexM H m R E (Except E (ControlFlow R) × TokenCursor) := do
  let action : StateT H m (Except E (ControlFlow R) × TokenCursor) :=
    (TokenHandler.handleTokens (H := H)).run.run cursor
  action

/- LEAN: Rust's `flush_cursor` takes a cursor over the lexer's arrays; here the batch itself
is handed to the handler in the cursor, and taken back into the lexer state afterwards,
whatever the handler decides, so that its storage is overwritten by the next batch. The
batch's array of contents is then set to `bytesAfter`, so that the batch does not keep a
reference to the lexer's content buffer, which would make the buffer's next change copy
it. -/
/-- Hands the non-empty batch over to the handler and takes it back. -/
private def handOver (batch : TokenBatch) (bytesAfter : ByteArray) : LexM H m R E Unit := do
  let cursor := TokenCursor.new (← core).version batch
  -- where lexing continues if the handler stops before the first token
  -- relex request empties the cursor, so we need to remember it here
  let some first := cursor.get 0
    | failInternal .emptyBatch
  let firstStart := (cursor.span first).start

  -- flush the cursor
  let (result, cursor) ← callHandler cursor

  -- the stop takes effect after the consumed tokens
  let location := match cursor.lastConsumed with
    -- nothing was taken, lex again from the first token
    | none => firstStart
    -- at least one token was taken, lex again after it
    | some token => (cursor.span token).end
  let relexRequested := cursor.relexRequested
  let isEmpty := cursor.isEmpty
  -- set our version to the cursor-requested version, and take the batch back
  modifyCore fun c =>
    { c with version := cursor.version, batch := { cursor.intoBatch.clear with bytes := bytesAfter } }

  -- process the result
  let result : Except (LexError E) (Stop R) ← match result with
    | .ok .continue =>
      if relexRequested then
        pure (.ok .relex)
      else
        -- ensure the cursor has been fully consumed
        if !isEmpty then
          failInternal .tokensNotConsumed
        return
    | .ok (.break result) =>
      if relexRequested then
        failInternal .finishedAndRelexed
      pure (.ok (.finished result))
    | .error err => pure (.error (.handler err))
  throw { result, location }

/-- Takes the batch out of the lexer state, leaving an empty one without storage. -/
@[inline]
private def takeBatch : LexM H m R E TokenBatch :=
  modifyGetThe LexerCore fun c => (c.batch, { c with batch := default })

private def flushBatch : LexM H m R E Unit := do
  -- the batch is spent once handed over, no matter what the handler decides
  if (← core).batch.len == 0 then
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
private def handOverStored (ty : TokenType) («end» : SmtLocation) : LexM H m R E Unit := do
  -- flush the batch, then hand over this token
  flushBatch
  let batch ← takeBatch
  let bytes := batch.bytes
  let c ← core
  let batch := { batch with bytes := c.tokenContent.bytes }.pushLocated ty 0 c.tokenContent.len
    c.tokenStart «end»
  handOver batch bytes

/-- Sinks a token with the given content, ending at `tokenEnd`. -/
@[inline]
private def sinkSlice (ty : TokenType) (tokenEnd : TokenEnd) (content : Content) :
    LexM H m R E Unit := do
  -- the caller of this function is responsible
  -- for ensuring that the constructed token is valid
  match content with
  | .borrowed _ start stop =>
    -- this is borrowed content, so put it into the batch
    let c ← core
    let spanStart := c.tokenStart
    let spanEnd := c.locationAt tokenEnd.position
    modifyBatch (·.pushLocated ty start stop spanStart spanEnd)
    if (← core).batch.len == BATCH_CAPACITY then
      flushBatch
  | .stored =>
    -- this is in our own buffer, so we cannot put it into the batch
    -- as we need the buffer usable for the next token
    handOverStored ty ((← core).locationAt tokenEnd.position)

private def sinkEof : LexM H m R E Unit := do
  -- the end of file has no content, which the cleared content buffer gives
  handOverStored .endOfFile ((← core).locationAt 0)

/--
Sinks a decimal token.

The token's own shape is checked first, then that `next`, the byte
at the end (if there is one), delimits it.
-/
@[inline]
private def finishDecimal (tokenEnd : TokenEnd) (content : Content) (next : Option UInt8) :
    LexM H m R E Unit := do
  -- decimals of the form 7. without any digit in fractional part are disallowed
  let last := content.last? (← core).tokenContent
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
  if content.size (← core).tokenContent == 0 then
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
  if content.size (← core).tokenContent == 0 then
    fail .forbiddenKeywordName tokenEnd
  if let some next := next then
    expectDelimiter next tokenEnd.position
  sinkSlice .keyword tokenEnd content

@[inline]
private def finishStringLiteral (tokenEnd : TokenEnd) (content : Content) : LexM H m R E Unit :=
  sinkSlice .string tokenEnd content

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

The content is from `contentStart` to `contentStop` in the slice, and the span is on the
current line, over `start` to `end` in the slice.
-/
/- LEAN: Rust writes the entry even when it is not emitted, as the next token overwrites it;
here a token that is not emitted is not written. -/
@[inline]
private def pushFast (batch : TokenBatch) (offset : Nat) (slice : ByteSlice) (ty : TokenType)
    (contentStart contentStop start «end» : Nat) (emit : Bool) : LexM H m R E TokenBatch := do
  if !emit then
    return batch
  let c ← core
  let line := c.line
  let lineStart := c.lineStart
  let batch := batch.pushOnLine ty (slice.start + contentStart) (slice.start + contentStop)
    line lineStart (offset + start) (offset + «end»)
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
private def storeUnfinishedSymbolRun (slice : ByteSlice) (entry : UInt8) (index after runEndAt : Nat) :
    LexM H m R E Unit := do
  startToken index
  if entry &&& FAST_PIPE != 0 then
    -- quoted symbol, skip the start pipe
    extendContent (slice.slice after runEndAt)
    setState .quotedSymbol
  else
    -- simple symbol, do not skip anything
    extendContent (slice.slice index runEndAt)
    setState .simpleSymbol

/- LEAN: the Rust function loops over the slice with `while let`; here the loop is the
recursion on `index`, and `partial` because Lean is not shown that every arm advances it.
Every arm that continues the loop in Rust calls `lexNormalFrom` again at the new index,
with the locals loaded again after the slow path. `offset` is the lexer's offset when
the loop started, which stays the same while the loop runs. -/
private partial def lexNormalFrom (slice : ByteSlice) (offset index : Nat) (batch : TokenBatch) :
    LexM H m R E Nat := do
  let some c := byteAt? slice index
    | do
      -- we have consumed every byte of the slice
      -- write the locals back before returning
      storeBatch batch
      return sliceSize slice
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
    let batch ← pushFast batch offset slice .parenClose index after index after true
    return ← lexNormalFrom slice offset after batch
  if c == byte! '(' then
    let batch ← pushFast batch offset slice .parenOpen index after index after true
    return ← lexNormalFrom slice offset after batch
  -- Handle whitespace and symbols in a fast path.
  let fastEntry := fastFlags c
  if fastEntry &&& FAST_ON != 0 then
    -- Fast path, compute where the run ends and where the token ends.
    -- For quoted symbols, the token will end after the closing pipe.
    let runEndAt := runEnd slice after (fastEntry &&& FAST_RUN_MASK)
    let isQuoted := fastEntry &&& FAST_PIPE != 0

    -- We might need to fall back to state-machine lexing if the token
    -- we have found is not properly finished.
    -- This can only happen if we are processing a quoted symbol
    -- and the expected pipe after the end of the run is not there,
    -- or if we are processing a simple symbol and we overrun the slice.
    -- Parentheses have trivially zero-length runs and whitespace
    -- can be split as it is discarded.
    if runEndAt == sliceSize slice || isQuoted then
      let isUnfinished :=
        if isQuoted then byteAt? slice runEndAt != some (byte! '|')
        else fastEntry &&& RUN_SIMPLE_SYMBOL != 0
      if isUnfinished then
        -- write the locals back
        storeBatch batch
        storeUnfinishedSymbolRun slice fastEntry index after runEndAt
        return runEndAt
    let tokenEnd := if isQuoted then runEndAt + 1 else runEndAt

    -- No need to fall back, construct the token: the pipes delimit a quoted
    -- symbol but are not part of its content, any other fast token is its
    -- whole text. The token is on a single line as all fast-lex runs exclude
    -- newlines. Whitespace is not emitted.
    let (ty, contentStart, contentStop) :=
      if isQuoted then (TokenType.quotedSymbol, after, runEndAt)
      else (TokenType.unquotedSymbol, index, tokenEnd)
    let emit := fastEntry &&& FAST_EMIT != 0
    -- A token must be delimited by the byte after it,
    -- fall back to the state machine if the delimiter is not found.
    if emit then
      match byteAt? slice tokenEnd with
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
        extendContent (slice.slice contentStart contentStop)
        setState .quotedSymbolClosed
        return tokenEnd
    let batch ← pushFast batch offset slice ty contentStart contentStop index tokenEnd emit
    -- Fast path done, continue normally after the token end.
    return ← lexNormalFrom slice offset tokenEnd batch

  -- The slow path will not use the locals, write them back.
  storeBatch batch

  -- Fast path was not taken, use the slow path.
  match START[c.toNat]! with
  | .lineFeed =>
    -- line feeds must be marked for line offsets
    -- mark it and update the index
    markLineFeedAt index
    lexNormalFrom slice offset after (← takeBatch)
  | .comment =>
    -- a comment has been started
    -- process the run eagerly
    startToken index
    let «end» := runEnd slice after RUN_COMMENT_PLAIN
    match byteAt? slice «end» with
    | some c =>
      if c == byte! '\n' then
        -- line feed, we need to mark it
        markLineFeedAt «end»
      -- otherwise a carriage return, which also ends the comment
      -- we have reached the end of the comment
      -- update the index and continue the loop
      lexNormalFrom slice offset («end» + 1) (← takeBatch)
    | none =>
      -- we ran out of bytes
      -- update the state and return
      setState .comment
      return «end»
  | .hash =>
    -- base selection
    startToken index
    let selected := (byteAt? slice after).bind fun c =>
      if c == byte! 'x' then some HEXADECIMAL_RUN
      else if c == byte! 'b' then some BINARY_RUN
      else none
    let some run := selected
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
    let afterEnd := runEnd slice start run.flag
    if afterEnd == sliceSize slice then
      -- we ran out of bytes
      -- update the content and the state and return
      extendContent (slice.slice start afterEnd)
      setState run.state
      return afterEnd
    -- dispatch a token with borrowed content
    finishDigitRun run (.mkAtByte afterEnd) (.borrow slice start afterEnd)
      (some (sliceGet slice afterEnd))
    -- update the index and continue the loop
    lexNormalFrom slice offset afterEnd (← takeBatch)
  | .quote =>
    -- starts a string literal
    startToken index
    if (← core).version == .v2_0 then
      -- SMT-LIB 2.0 has a different string-escape format
      -- than the subsequent versions, leave the fast path immediately
      setState .stringLiteral
      return after
    -- determine the run of content bytes
    let afterContentEnd := runEnd slice after RUN_STRING_PLAIN
    -- we can only eagerly borrow if the content is ended by a closing quote
    -- that is definitely not followed by another closing quote
    -- (we cannot borrow a string containing an escape)
    match byteAt? slice afterContentEnd, byteAt? slice (afterContentEnd + 1) with
    | some quote, some next =>
      if quote == byte! '"' && next != byte! '"' then
        -- definitely closed by a quote not followed by another quote
        -- borrow the string literal content and produce a token
        expectDelimiter next (afterContentEnd + 1)
        finishStringLiteral (.mkAtByte (afterContentEnd + 1))
          (.borrow slice after afterContentEnd)
        -- the closing quote is not part of the content,
        -- but was also processed
        lexNormalFrom slice offset (afterContentEnd + 1) (← takeBatch)
      else
        extendContent (slice.slice after afterContentEnd)
        setState .stringLiteral
        return afterContentEnd
    | _, _ =>
      -- we cannot borrow the content
      -- update the content and state and return
      extendContent (slice.slice after afterContentEnd)
      setState .stringLiteral
      return afterContentEnd
  | .colon =>
    -- starts a keyword
    startToken index
    -- we require that the keyword does not start with a digit
    -- (also non-empty, but that is checked after finishing)
    if (byteAt? slice after).any isAsciiDigit then
      failAt .forbiddenKeywordName (after + 1)
    -- get a run of simple-symbol bytes
    let afterEnd := runEnd slice after RUN_SIMPLE_SYMBOL
    if afterEnd == sliceSize slice then
      -- we ran out of bytes
      -- update the content and state and return
      extendContent (slice.slice after afterEnd)
      setState .keyword
      return afterEnd
    -- dispatch a token with borrowed content
    finishKeyword (.mkAtByte afterEnd) (.borrow slice after afterEnd)
      (some (sliceGet slice afterEnd))
    -- update the index and continue the loop
    lexNormalFrom slice offset afterEnd (← takeBatch)
  | .digit =>
    startToken index
    -- determine the run of digits
    let afterEnd := runEnd slice after RUN_DIGIT
    -- check that we are not in a leading zero condition,
    -- which is only possible if the first character was zero
    -- and there is a subsequent digit;
    -- it is possible we will not be able to decide it here
    -- if the slice ends with a single zero, so we need to handle that
    -- when lexing digit in the state `numeralOrDecimal`
    if c == byte! '0' && afterEnd > after then
      failAt .numeralLeadingZero (after + 1)
    match byteAt? slice afterEnd with
    | some next =>
      if next == byte! '.' then
        -- a dot starts a fraction, try to do a subsequent run of fraction digits
        let afterFractionEnd := runEnd slice (afterEnd + 1) RUN_DIGIT
        if afterFractionEnd == sliceSize slice then
          -- we ran out of bytes
          -- update the content and state and return
          extendContent (slice.slice index afterFractionEnd)
          setState .fraction
          return afterFractionEnd
        -- dispatch a decimal token with borrowed content
        finishDecimal (.mkAtByte afterFractionEnd) (.borrow slice index afterFractionEnd)
          (some (sliceGet slice afterFractionEnd))
        -- update the index and continue the loop
        lexNormalFrom slice offset afterFractionEnd (← takeBatch)
      else
        -- the numeral is not actually a decimal and ends
        -- dispatch a numeral token with borrowed content
        expectDelimiter next afterEnd
        finishNumeral (.mkAtByte afterEnd) (.borrow slice index afterEnd)
        -- update the index and continue the loop
        lexNormalFrom slice offset afterEnd (← takeBatch)
    | none =>
      -- we ran out of bytes
      -- update the content and state and return
      extendContent (slice.slice index afterEnd)
      setState .numeralOrDecimal
      return afterEnd
  | .other | .whitespace | .parenOpen | .parenClose | .symbol | .pipe =>
    -- can actually only be other (resulting in unexpected character),
    -- as the other arms have already been handled in the fast path.
    startToken index
    failAt .unexpectedCharacter after

private def lexNormal (slice : ByteSlice) : LexM H m R E Nat := do
  -- use locals for variables commonly used on the fast path
  let offset := (← core).offset
  lexNormalFrom slice offset 0 (← takeBatch)

private def lexFractionFrom (slice : ByteSlice) (start : Nat) : LexM H m R E Nat := do
  -- find the first byte in the remainder that is not a digit
  let «end» := runEnd slice start RUN_DIGIT
  -- extend the token from slice
  extendContent (slice.slice start «end»)
  if «end» < sliceSize slice then
    -- we have successfully consumed the fraction, finish the decimal
    finishDecimal (.mkAtByte «end») .stored (some (sliceGet slice «end»))
    setState .normal
  else
    -- we ran out of bytes for now
    setState .fraction
  return «end»

private def lexNumeralOrDecimal (slice : ByteSlice) : LexM H m R E Nat := do
  -- find the first byte that is not a digit
  let index := runEnd slice 0 RUN_DIGIT

  -- check that we are not in a leading zero condition
  -- this could not have been done when starting the numeral/decimal
  -- since just a single '0' is allowed

  -- as we emplace the first digit in the normal state,
  -- it suffices for the leading zero condition that
  -- 1. at least one additional digit has been consumed
  -- 2. the content lexed previously is exactly "0"
  let content := (← core).tokenContent
  let isZero := content.len == 1 && content.bytes.get! 0 == byte! '0'
  if index > 0 && isZero then
    failAt .numeralLeadingZero 1

  -- extend the token from slice
  extendContent (slice.slice 0 index)

  match byteAt? slice index with
  | some next =>
    if next == byte! '.' then
      -- decimal, the next character will start fraction
      -- add the dot and immediately start lexing the fraction after it
      pushContent (byte! '.')
      lexFractionFrom slice (index + 1)
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

private def lexBaseSelection (slice : ByteSlice) : LexM H m R E Nat := do
  let c := sliceGet slice 0
  if c == byte! 'x' then
    setState .hexadecimal
  else if c == byte! 'b' then
    setState .binary
  else
    failAt .baseSelectionExpected 1
  return 1

/-- Lexes a digit run, either hexadecimal or binary. -/
private def lexDigitRun (slice : ByteSlice) (run : DigitRun) : LexM H m R E Nat := do
  -- find the first byte that is not allowed in the run
  let index := runEnd slice 0 run.flag
  -- extend the token from slice
  extendContent (slice.slice 0 index)
  if index < sliceSize slice then
    -- we have successfully consumed the digit run, finish it
    finishDigitRun run (.mkAtByte index) .stored (some (sliceGet slice index))
    setState .normal
  return index

/- LEAN: the Rust loops keep the rest of the slice and the number of bytes consumed from it;
here the loops keep the position `consumed` in the whole slice, so a position in the rest
in Rust is `consumed` plus it here. The loops are `partial` for the reason given at
`lexNormal`. -/

/--
Lexes the string literal in the legacy 2.0 mode.

The legacy 2.0 mode has two backslash escapes, \" and \\.
There are no other escapes.
-/
private partial def lexStringLiteralLegacy (slice : ByteSlice) (consumed : Nat) :
    LexM H m R E Nat := do
  let some first := byteAt? slice consumed
    | return consumed
  let mut consumed := consumed
  match (← core).state with
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
      consumed := consumed + 1
    else
      -- not a backslash escape: the backslash belongs to the content,
      -- and the byte after it is lexed like any other
      pushContent (byte! '\\')
    -- continue parsing the string literal
    setState .stringLiteral
  | _ => pure ()

  -- find the first byte that does not belong to string nor quoted
  -- this means backslash and pipe end the run as well, so we can act on them
  let index := runEndAll slice consumed (RUN_STRING_PLAIN ||| RUN_QUOTED_PLAIN)

  let some c := byteAt? slice index
    | do
      -- extend the content with the rest
      extendContent (slice.slice consumed (sliceSize slice))
      -- we have nothing more to consume, return
      return sliceSize slice

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
  extendContent (slice.slice consumed index)
  if addRunEnding then
    -- add the byte to the content
    pushContent c
  -- consume the run-ending byte and everything before it
  lexStringLiteralLegacy slice (index + 1)

/-- Lexes the string literal. -/
private partial def lexStringLiteralFrom (slice : ByteSlice) (consumed : Nat) :
    LexM H m R E Nat := do
  let some first := byteAt? slice consumed
    | return consumed
  let mut consumed := consumed
  if (← core).state == .stringLiteralDoubleQuote then
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
      consumed := consumed + 1
      -- push a double-quote byte (just one, we encountered two)
      pushContent (byte! '"')
      -- return to string-literal state and continue lexing
      setState .stringLiteral

  -- find the first byte that is not a plain string byte
  let index := runEnd slice consumed RUN_STRING_PLAIN

  match byteAt? slice index with
  | some c =>
    if c == byte! '\n' then
      -- mark the line feed
      markLineFeedAt index
      -- extend with & consume the run including the line feed
      extendContent (slice.slice consumed (index + 1))
      -- continue lexing
      lexStringLiteralFrom slice (index + 1)
    else if c == byte! '"' then
      -- we have a double quote in string literal
      -- only extend the content with bytes before it
      extendContent (slice.slice consumed index)
      -- the quote may be followed by another double quote for escaping
      -- otherwise, it will end the string literal
      -- put the lexer in a special state to handle the next character
      setState .stringLiteralDoubleQuote
      -- consume the quote and everything before it, continue lexing
      lexStringLiteralFrom slice (index + 1)
    else
      -- forbidden, not printable or whitespace
      failAt .forbiddenCharInString (index + 1)
  | none =>
    -- extend the content with the rest
    extendContent (slice.slice consumed (sliceSize slice))
    -- we have nothing more to consume, return
    return sliceSize slice

/-- Lexes the string literal. -/
private def lexStringLiteral (slice : ByteSlice) : LexM H m R E Nat := do
  if (← core).version == .v2_0 then
    -- in 2.0 mode, the string literals are lexed differently,
    -- hand over to the legacy lexing function
    lexStringLiteralLegacy slice 0
  else
    lexStringLiteralFrom slice 0

private def lexSimpleSymbol (slice : ByteSlice) : LexM H m R E Nat := do
  -- find the first byte that is not a simple symbol
  let index := runEnd slice 0 RUN_SIMPLE_SYMBOL
  -- extend the token from slice
  extendContent (slice.slice 0 index)
  if index < sliceSize slice then
    -- we have successfully consumed the symbol, finish it
    expectDelimiter (sliceGet slice index) index
    finishSimpleSymbol (.mkAtByte index) .stored
    setState .normal
  return index

private partial def lexQuotedSymbol (slice : ByteSlice) (consumed : Nat) : LexM H m R E Nat := do
  -- find the first byte that is not a quoted symbol
  let index := runEnd slice consumed RUN_QUOTED_PLAIN
  let afterSlicePosition := index + 1

  -- inspect the problematic byte
  match byteAt? slice index with
  | some c =>
    if c == byte! '|' then
      -- end of quoted symbol, extend its content
      extendContent (slice.slice consumed index)
      -- the byte after the pipe must delimit the token before it is sunk
      match byteAt? slice (index + 1) with
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
      extendContent (slice.slice consumed (index + 1))
      lexQuotedSymbol slice (index + 1)
    else
      -- forbidden character
      failAt .forbiddenCharInQuotedSymbol afterSlicePosition
  | none =>
    -- we ran out of bytes before the token ended
    -- extend content and keep the quoted symbol state
    extendContent (slice.slice consumed (sliceSize slice))
    return sliceSize slice

private def lexKeyword (slice : ByteSlice) : LexM H m R E Nat := do
  -- test that the keyword does not start with a digit
  if (← core).tokenContent.isEmpty && isAsciiDigit (sliceGet slice 0) then
    failAt .forbiddenKeywordName 1

  -- find the first byte that is not simple-symbol-like
  let index := runEnd slice 0 RUN_SIMPLE_SYMBOL

  -- extend the token from slice
  extendContent (slice.slice 0 index)

  if index < sliceSize slice then
    -- we have successfully consumed the keyword, finish it
    finishKeyword (.mkAtByte index) .stored (some (sliceGet slice index))
    setState .normal
  return index

private def lexQuotedSymbolClosed (slice : ByteSlice) : LexM H m R E Nat := do
  -- we expect a token delimiter to follow the closing pipe
  expectDelimiter (sliceGet slice 0) 0
  -- all good, produce the quoted symbol token
  sinkSlice .quotedSymbol (.mkAtByte 0) .stored
  -- the delimiter is not consumed
  setState .normal
  return 0

private def lexComment (slice : ByteSlice) : LexM H m R E Nat := do
  -- run until comment end
  let index := runEnd slice 0 RUN_COMMENT_PLAIN
  let some c := byteAt? slice index
    -- the comment continues, just consume the whole slice
    -- and remain in comment state
    | return sliceSize slice

  -- the comment has ended, either by CR or LF
  -- if it ended by LF, we must mark it
  if c == byte! '\n' then
    markLineFeedAt index

  -- move back to the normal state
  setState .normal

  -- return, consuming up to comment end including it
  return index + 1

/-- Lexes the non-empty slice in the current state, returning the number of consumed bytes. -/
private def lexStep (rest : ByteSlice) : LexM H m R E Nat := do
  match (← core).state with
  | .normal => lexNormal rest
  | .numeralOrDecimal => lexNumeralOrDecimal rest
  | .fraction => lexFractionFrom rest 0
  | .baseSelection => lexBaseSelection rest
  | .hexadecimal => lexDigitRun rest HEXADECIMAL_RUN
  | .binary => lexDigitRun rest BINARY_RUN
  | .stringLiteral | .stringLiteralDoubleQuote | .stringLiteralBackslashEscape =>
    lexStringLiteral rest
  | .simpleSymbol => lexSimpleSymbol rest
  | .quotedSymbol => lexQuotedSymbol rest 0
  | .keyword => lexKeyword rest
  | .comment => lexComment rest
  | .quotedSymbolClosed => lexQuotedSymbolClosed rest
  | .failed => failInternal .lexedAfterError

/--
Moves the lexer back to `location`, which the tokens handed over
so far end at, discarding whatever was lexed beyond it.
-/
private def resumeAt (location : SmtLocation) : InnerM H m Unit :=
  -- the region after the location was lexed once already,
  -- restore all bookkeeping
  -- a stop inside an arm leaves it mid-token
  modifyThe LexerCore fun c =>
    { c with
      offset := location.offset
      line := location.line
      lineStart := location.offset - location.column
      state := .normal
      tokenContent := c.tokenContent.clear }

/- LEAN: the loop of `lex_slice_inner`, `partial` as a relex request moves it back in the
slice. `rest` is the part of `slice` not lexed yet, and `fnResult` the result to return once
the batch is handed over. The `.run` of an action in `LexM` gives its interruption as a
value, the counterpart of matching on the `Result` in Rust. -/
private partial def lexSliceLoop (slice : ByteSlice) (initialOffset : Nat) (rest : ByteSlice)
    (fnResult : Except (LexError E) (ControlFlow R)) :
    InnerM H m (Except (LexError E) (ControlFlow R)) := do
  let failed := match fnResult with
    | .error _ => true
    | .ok _ => false
  /- LEAN: `none` stands for a batch handed over without an interruption, `some` for the
  number of bytes a step consumed. -/
  let result : Except (Interrupted R E) (Option Nat) ← if sliceSize rest == 0 || failed then do
      -- hand over the batch
      let flushed ← (flushBatch (m := m) (R := R) (E := E)).run
      pure (flushed.map fun () => none)
    else do
      let stepped ← (lexStep rest).run
      pure (stepped.map some)

  match result with
  | .ok none =>
    -- we are done
    return fnResult
  | .ok (some consumed) =>
    -- advance the offset by the number of consumed bytes
    -- the line positions are updated by the arm functions above
    modifyThe LexerCore fun c => { c with offset := c.offset + consumed }
    -- move after consumed bytes, continue consuming
    lexSliceLoop slice initialOffset (rest.slice consumed) fnResult
  | .error interrupted =>
    match interrupted.result with
    | .ok stop =>
      let location := interrupted.location
      resumeAt location
      -- every handed-over token is in this slice
      -- so the location must be equal or greater to initial offset
      -- compute this even for finished to assert the interrupted location
      if location.offset < initialOffset then
        return .error (.internal .stoppedBeforeStart)
      let index := location.offset - initialOffset
      match stop with
      | .relex =>
        -- everything up to the index was already consumed
        -- continue from there
        lexSliceLoop slice initialOffset (slice.slice index) (.ok .continue)
      | .finished result =>
        -- the handler is done: the batch was handed over,
        -- the rest of the slice stays unlexed
        -- the lexer will be reset as a consequence of the break result
        return .ok (.break result)
    | .error err =>
      -- make sure the tokens before the error get handed over
      lexSliceLoop slice initialOffset rest (.error err)

private def lexSliceInner (slice : ByteSlice) :
    InnerM H m (Except (LexError E) (ControlFlow R)) := do
  let initialOffset := (← getThe LexerCore).offset
  -- the tokens borrowed from this slice have their contents in its array
  modifyThe LexerCore fun c => { c with batch := { c.batch with bytes := slice.byteArray } }
  lexSliceLoop slice initialOffset slice (.ok .continue)

/-- Resets the lexer to the initial state, including the location and version. -/
private def reset : InnerM H m Unit :=
  modifyThe LexerCore fun c =>
    { c with
      version := c.initialVersion
      state := .normal
      tokenStart := SmtLocation.initial
      tokenContent := c.tokenContent.clear
      offset := 0
      line := 0
      lineStart := 0 }

private def lexEofInner : InnerM H m (Except (LexError E) (ControlFlow R)) := do
  -- EOF is a token delimiter, we need to produce the token
  -- that waits for a delimiter if there is any
  let step : LexM H m R E Unit := do
    match (← core).state with
    | .normal | .comment =>
      -- nothing to do, we accept EOF even in comments
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
    | .failed => failInternal .lexedAfterError
    -- everything has been processed, start the EOF token and sink it
    startToken 0
    sinkEof

  match ← step.run with
  | .ok () =>
    -- everything processed, but there was no break out
    -- we need manually reset the lexer and return continue
    reset
    return .ok .continue
  | .error interrupted =>
    match interrupted.result with
    | .error err => return .error err
    | .ok .relex => return .error (.internal .relexAtEndOfFile)
    | .ok (.finished result) =>
      -- the handler is done with the input
      -- the lexer will be reset as a consequence of the break result
      return .ok (.break result)

/-- Executes an inner lexer step and updates the lexer according to the result. -/
private def executeStep (step : InnerM H m (Except (LexError E) (ControlFlow R))) :
    InnerM H m (Except (LexError E) (ControlFlow (SmtLocated R))) := do
  match ← step with
  | .ok .continue => return .ok .continue
  | .ok (.break result) =>
    -- get the break location, then reset the lexer
    let location := (← getThe LexerCore).locationAt 0
    reset
    return .ok (.break { value := result, location })
  | .error err =>
    -- set the lexer to failed state
    modifyThe LexerCore fun c => { c with state := .failed }
    return .error err

end

namespace Lexer

/-- Constructs the lexer. -/
def new (handler : H) (version : SmtVersion) : Lexer H :=
  { handler,
    core := {
      version
      initialVersion := version
      state := .normal
      tokenStart := SmtLocation.initial
      tokenContent := ContentBuffer.empty
      offset := 0
      line := 0
      lineStart := 0
      batch := TokenBatch.empty BATCH_CAPACITY } }

def currentLocation (self : Lexer H) : SmtLocation :=
  self.core.locationAt 0

/- LEAN: takes the lexer apart so that the handler and the fields are each held once, runs
the step on them, and puts the lexer together again; Rust does the same through
`&mut self`. -/
@[inline]
private def run [Monad m] (self : Lexer H) (step : InnerM H m α) : m (α × Lexer H) := do
  let { handler, core } := self
  let ((result, core), handler) ← (step.run core).run handler
  return (result, { handler, core })

/- LEAN: the Rust methods take `&mut self`; these take the lexer and return it updated along
with the result. If the caller does not keep the old lexer, it is updated in place. -/

/--
Lexes the given slice, sending the lexed tokens to the handler.

If the token handler returns `ControlFlow.break` on some token,
the lexer passes it through, adding the break location,
and resets itself.

If the token handler returns `ControlFlow.continue` on all tokens,
the lexer is ready for further lexing.

If an error occurs, the lexer moves into a failure state;
all further lexing calls fail with an internal error.
-/
def lexSlice [Monad m] [TokenHandler H m R E] (self : Lexer H) (slice : ByteSlice) :
    m (Except (LexError E) (ControlFlow (SmtLocated R)) × Lexer H) :=
  -- call inner lexing and fail on error
  self.run (executeStep (lexSliceInner slice))

/--
Lexes end-of-file, sending the lexed tokens to the handler.

If the token handler returns `ControlFlow.break` on the EOF token,
the lexer passes it through, adding the break location,
and resets itself.

If the token handler returns `ControlFlow.continue` on the EOF token,
the lexer resets itself and returns `ControlFlow.continue`.

If an error occurs, the lexer moves into a failure state;
all further lexing calls fail with an internal error.
-/
def lexEof [Monad m] [TokenHandler H m R E] (self : Lexer H) :
    m (Except (LexError E) (ControlFlow (SmtLocated R)) × Lexer H) :=
  -- call inner EOF lexing and fail on error
  self.run (executeStep lexEofInner)

/--
Lexes the whole input including EOF at the end.

If the token handler returns `ControlFlow.break` on some token,
the lexer passes it through, adding the break location,
and resets itself.

If the token handler returns `ControlFlow.continue` on all tokens
including EOF, the lexer resets itself after EOF
and returns `ControlFlow.continue`.

If an error occurs, the lexer moves into a failure state;
all further lexing calls fail with an internal error.
-/
def lexAll [Monad m] [TokenHandler H m R E] (self : Lexer H) (input : ByteSlice) :
    m (Except (LexError E) (ControlFlow (SmtLocated R)) × Lexer H) := do
  let (result, self) ← self.lexSlice input
  match result with
  | .ok .continue => self.lexEof
  | _ => return (result, self)

end Lexer

end BlazingSmtlib.Read.Lexer

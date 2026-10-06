import BSmtLib.Proofs.Lexer.V3Runs

/-!
The lexer with fast paths: the fourth of the chain of lexers that leads from the specification
to the library's lexer.

It is the lexer over runs `V3Runs` with one change: the fast paths of the library's lexer, taken
where no token is in progress (`lexIdle`). A parenthesis is a token at once. Whitespace other
than a line feed, a quoted symbol, and a simple symbol that does not start with a digit are
lexed by a single run of their bytes, without the naive lexer's step `start`. Where such a run
does not finish its token, the lexer takes the path of the lexer over runs from the token's first
byte instead: for whitespace that the consumer takes and that does not end on its line inside
the slice, for a quoted symbol whose run is not ended by its closing pipe, and for a simple
symbol that runs to the end of the slice.

Everything else is the lexer over runs', which is the batched lexer's.
-/

namespace BSmtLib.Proofs.Lexer.V4FastPaths

open V1Naive V2Batched V3Runs

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

/--
Lexes from the byte at `i`, with no token in progress, by a fast path if there is one for the
byte, and by the lexer over runs' `V3Runs.lexIdle` otherwise. The token's delimiter is not
lexed.
-/
def lexIdle : IdleStep H m R E := fun sliceStart slice i h core batch hfits => do
  let c := slice[i]
  let location := core.location
  have hle : core.frontier ≤ location.offset := core.frontier_le
  have hlast := hfits.2
  -- the parentheses first: each is a token by itself
  if c == byte! ')' || c == byte! '(' then
    let category := if c == byte! ')' then TokenCategory.parenClose else .parenOpen
    let l : Lexeme :=
      { category, content := ByteArray.empty.push c, start := location,
        «end» := location.afterColumn }
    let ⟨(outcome, core, batch), hfits, _⟩ ← emit sliceStart
      { core with activity := .idle, location := l.end, startedBefore := trivial } batch l hfits.1
      hfits.3 (show _ ≤ location.offset by omega)
      (show location.offset < location.offset + 1 by omega)
      (Nat.le_refl _)
    return ⟨(outcome, core, batch, ⟨i + 1, by omega⟩), hfits⟩
  let whitespace := Consume.consumesWhitespaceAndComments (H := H)
  let quoted := c == byte! '|'
  let isSpace := isWhitespaceRun c
  -- whitespace, quoted symbols and simple symbols that do not start with a digit are fast
  if !(quoted || isSpace || (isSymbolByte c && !isDigit c)) then
    return ← V3Runs.lexIdle sliceStart slice i h core batch hfits
  let runEnd := V3Runs.runEnd slice
    (if quoted then isQuotedRun else if isSpace then isWhitespaceRun else isSymbolByte) (i + 1)
  have : i + 1 ≤ runEnd := le_runEnd _ _ _
  let next := slice[runEnd]?
  -- whitespace that the consumer takes and that does not end on its line inside the slice
  if whitespace && isSpace && (next == none || next == some (byte! '\n')) then
    return ← V3Runs.lexIdle sliceStart slice i h core batch hfits
  -- a quoted symbol not closed by the byte that ends its run, or a simple symbol that runs to
  -- the end of the slice
  if (quoted && next != some (byte! '|')) || (!quoted && !isSpace && next == none) then
    return ← V3Runs.lexIdle sliceStart slice i h core batch hfits
  -- the token is complete: its end is after the closing pipe of a quoted symbol, and at the end
  -- of the run otherwise; it is on one line, as no run takes a line feed
  let tokenEnd := runEnd + if quoted then 1 else 0
  let atEnd := afterColumns location (tokenEnd - i)
  have hend : location.offset < atEnd.offset := by
    show location.offset < location.offset + (tokenEnd - i)
    have : runEnd ≤ tokenEnd := Nat.le_add_right _ _
    omega
  if isSpace && !whitespace then
    -- whitespace that the consumer does not take is passed over
    return ⟨(.next, { core with activity := .idle, location := atEnd, startedBefore := trivial },
      batch, ⟨tokenEnd, by omega⟩), hfits.mono (show core.frontier ≤ atEnd.offset by omega)⟩
  -- the pipes are not a part of the content of a quoted symbol
  let content := if quoted then bytesOf slice (i + 1) runEnd else bytesOf slice i tokenEnd
  if !isSpace then
    -- a symbol must be delimited by the byte after it
    match slice[tokenEnd]? with
    | some after =>
      if !isDelimiter after then
        let failure := failAtByte .missingDelimiter location atEnd
        let failure := { cause := .lexical failure.error, location := failure.location }
        return ⟨(.failed failure, core, batch, ⟨tokenEnd, by omega⟩), hfits⟩
    | none =>
      -- the quoted symbol has ended with the slice: it waits for its delimiter
      let p : Pending := { mode := .quotedSymbolClosed, start := location, content }
      return ⟨(.next, { core with activity := .token p, location := atEnd, startedBefore := hend },
        batch, ⟨tokenEnd, by omega⟩), hfits.mono (show core.frontier ≤ location.offset from hle)⟩
  let category :=
    if quoted then TokenCategory.quotedSymbol
    else if isSpace then .whitespace
    else .unquotedSymbol
  let l : Lexeme := { category, content, start := location, «end» := atEnd }
  let ⟨(outcome, core, batch), hfits, _⟩ ← emit sliceStart
    { core with activity := .idle, location := atEnd, startedBefore := trivial } batch l hfits.1
    hfits.3 (show _ ≤ location.offset by omega) hend (Nat.le_refl _)
  return ⟨(outcome, core, batch, ⟨tokenEnd, by omega⟩), hfits⟩

end

/-! ## The lexer

The lexer with fast paths is the naive lexer's type `V1Naive.Lexer` with the operations below in
place of its `lexSlice` and `lexAll`; the other operations are the naive lexer's: `new`,
`newRecovering`, `lexEof`, `PendingEof.lexEof`, `currentLocation` and `version`.
-/

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
      (ControlFlow (Located R) × V1Naive.Lexer H recovery)) :=
  lexSliceWith lexIdle self slice

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

end BSmtLib.Proofs.Lexer.V4FastPaths

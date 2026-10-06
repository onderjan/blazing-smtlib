import BSmtLib.Proofs.Lexer.V2Batched

/-!
The lexer over runs: the third of the chain of lexers that leads from the specification to the
library's lexer.

It is the batched lexer `V2Batched` with one change: how the bytes of a token are stepped. The
batched lexer feeds a token one byte at a time to the naive lexer's step `advance`; this lexer
lexes a token in one go, in a loop over runs of bytes (`run`): it finds where the run of bytes
that the token takes as they are ends, and acts on the byte that ends it. This is how the
library's lexer lexes a token on its paths without the fast paths of `V4FastPaths`.

Everything else is the batched lexer's: the state, which is the naive lexer's, the start of a
token by the naive lexer's step `start`, the hand-overs and batches (`V2Batched.emit`), the
going back after a stop of the consumer, the recovery, and the lexing of the end of the input,
which is the naive lexer's. A token left unfinished at the end of a slice is in the same state
as in the batched lexer.
-/

namespace BSmtLib.Proofs.Lexer.V3Runs

open V1Naive V2Batched

/-! ## Runs -/

/-- The index of the first byte from `i` on that does not pass `p`, the size of the slice if
none. -/
def runEnd (slice : ByteSlice) (p : UInt8 → Bool) (i : Nat) : Nat :=
  if h : i < slice.size then
    if p slice[i] then runEnd slice p (i + 1) else i
  else
    i
termination_by slice.size - i

theorem le_runEnd (slice : ByteSlice) (p : UInt8 → Bool) (i : Nat) : i ≤ runEnd slice p i := by
  fun_induction runEnd slice p i <;> omega

/-- The bytes of the slice from `i` to `j`. -/
def bytesOf (slice : ByteSlice) (i j : Nat) : ByteArray :=
  (slice.slice i j).toByteArray

/-- The location `n` bytes after `location`, none of which is a line feed. -/
def afterColumns (location : Location) (n : Nat) : Location :=
  { offset := location.offset + n, line := location.line, column := location.column + n }

/-- Whether the byte is a part of a quoted symbol that is not acted on: any byte of its content
but the line feed. -/
def isQuotedRun (c : UInt8) : Bool :=
  isTextByte c && c != byte! '|' && c != byte! '\\' && c != byte! '\n'

/-- Whether the byte is a part of a string from version 2.5 on that is not acted on: any byte
of its content but the quote and the line feed. -/
def isStringRun (c : UInt8) : Bool :=
  isTextByte c && c != byte! '"' && c != byte! '\n'

/-- Whether the byte is a part of a string under version 2.0 that is not acted on: any byte of
its content but the quote, the backslash and the line feed. -/
def isLegacyStringRun (c : UInt8) : Bool :=
  isTextByte c && c != byte! '"' && c != byte! '\\' && c != byte! '\n'

/-- Whether the byte is a part of a comment that is not acted on: any byte but a line break. -/
def isCommentRun (c : UInt8) : Bool :=
  c != byte! '\n' && c != byte! '\r'

/-- Whether the byte is a part of whitespace that is not acted on: whitespace but the line
feed. -/
def isWhitespaceRun (c : UInt8) : Bool :=
  isWhitespace c && c != byte! '\n'

/-! ## The token in one go -/

/--
What lexing the token in progress from the byte at `i` on gives, in a slice of `size` bytes:
the counterpart of `V1Naive.Advanced` for a run of bytes, with the index where lexing goes on.
-/
inductive Ran (size i : Nat) where
  /-- The slice has ended inside the token; `location` is that of its end. -/
  | pending (p : Pending) (location : Location)
  /-- The token has ended with the byte before `next`, and the consumer does not take it: a
  comment. `location` is that of the byte at `next`. -/
  | idle (next : Nat) (location : Location) (after : i < next)
  /-- The token has ended with the byte before `next`: the line break that ends a comment. -/
  | tokenWith (lexeme : Lexeme) (next : Nat) (after : i < next)
  /-- The token has ended before the byte at `next`, which delimits it. -/
  | tokenBefore (lexeme : Lexeme) (next : Nat) (after : i ≤ next) (inside : next < size)
  | error (failure : LexFailure)

/-- What lexing the token from a later byte gives, as seen from the byte at `i`. -/
def Ran.lift (h : i ≤ i') : Ran size i' → Ran size i
  | .pending p location => .pending p location
  | .idle next location after => .idle next location (by omega)
  | .tokenWith l next after => .tokenWith l next (by omega)
  | .tokenBefore l next after inside => .tokenBefore l next (by omega) inside
  | .error failure => .error failure

/--
The token `p`, with the content `content`, ends before the byte `c` at `j`, at `location`; the
byte must delimit it.
-/
def delimited (p : Pending) (category : TokenCategory) (content : ByteArray) (j : Nat)
    (location : Location) (c : UInt8) (after : i ≤ j) (inside : j < size) : Ran size i :=
  if isDelimiter c then
    .tokenBefore { category, content, start := p.start, «end» := location } j after inside
  else
    .error (failAtByte .missingDelimiter p.start location)

/--
Lexes the token in progress `p` from the byte at `i` of the slice on, at `location`, to its end
or to the end of the slice. `whitespace` says whether the consumer takes whitespace and
comments.

Each mode takes the run of bytes that it keeps in, as `advance` would one by one, and acts on
the byte that ends the run.
-/
def run (whitespace : Bool) (slice : ByteSlice) (p : Pending) (i : Nat) (location : Location) :
    Ran slice.size i :=
  match p.mode with
  | .numeral zero =>
    let j := runEnd slice isDigit i
    have hj : i ≤ j := le_runEnd slice isDigit i
    -- a numeral other than 0 does not start with 0
    if zero && i < j then
      .error (failAtByte .numeralLeadingZero p.start location)
    else
      let content := p.content ++ bytesOf slice i j
      let at_ := afterColumns location (j - i)
      if h : j < slice.size then
        let c := slice[j]
        if c == byte! '.' then
          let p := { p with mode := .fraction false, content := content.push c }
          (run whitespace slice p (j + 1) (at_.afterByte c)).lift (by omega)
        else
          delimited p .numeral content j at_ c hj h
      else
        .pending { p with mode := .numeral (zero && j == i), content } at_
  | .fraction digits =>
    let j := runEnd slice isDigit i
    have hj : i ≤ j := le_runEnd slice isDigit i
    let content := p.content ++ bytesOf slice i j
    let digits := digits || i < j
    let at_ := afterColumns location (j - i)
    if h : j < slice.size then
      if !digits then .error (failAtByte .fractionDigitExpected p.start at_)
      else delimited p .decimal content j at_ slice[j] hj h
    else
      .pending { p with mode := .fraction digits, content } at_
  | .hash =>
    if h : i < slice.size then
      let c := slice[i]
      if c == byte! 'x' then
        (run whitespace slice { p with mode := .digits .hexadecimal } (i + 1)
          (location.afterByte c)).lift (by omega)
      else if c == byte! 'b' then
        (run whitespace slice { p with mode := .digits .binary } (i + 1)
          (location.afterByte c)).lift (by omega)
      else
        .error (failAtByte .baseSelectionExpected p.start location)
    else
      .pending p location
  | .digits radix =>
    let j := runEnd slice radix.allows i
    have hj : i ≤ j := le_runEnd slice radix.allows i
    let content := p.content ++ bytesOf slice i j
    let at_ := afterColumns location (j - i)
    if h : j < slice.size then
      if content.isEmpty then .error (failAtByte radix.emptyError p.start at_)
      else delimited p radix.category content j at_ slice[j] hj h
    else
      .pending { p with content } at_
  | .keyword =>
    let j := runEnd slice isSymbolByte i
    have hj : i ≤ j := le_runEnd slice isSymbolByte i
    let content := p.content ++ bytesOf slice i j
    let at_ := afterColumns location (j - i)
    if h : j < slice.size then
      if content.isEmpty then .error (failAtByte .forbiddenKeywordName p.start at_)
      else delimited p .keyword content j at_ slice[j] hj h
    else
      .pending { p with content } at_
  | .simpleSymbol =>
    let j := runEnd slice isSymbolByte i
    have hj : i ≤ j := le_runEnd slice isSymbolByte i
    let content := p.content ++ bytesOf slice i j
    let at_ := afterColumns location (j - i)
    if h : j < slice.size then
      delimited p .unquotedSymbol content j at_ slice[j] hj h
    else
      .pending { p with content } at_
  | .quotedSymbol =>
    let j := runEnd slice isQuotedRun i
    have hj : i ≤ j := le_runEnd slice isQuotedRun i
    let content := p.content ++ bytesOf slice i j
    let at_ := afterColumns location (j - i)
    if h : j < slice.size then
      let c := slice[j]
      if c == byte! '|' then
        (run whitespace slice { p with mode := .quotedSymbolClosed, content } (j + 1)
          (at_.afterByte c)).lift (by omega)
      else if c == byte! '\\' then
        .error (failAtByte .backslashInQuotedSymbol p.start at_)
      else if c == byte! '\n' then
        -- the line feed is a part of the content, and the run goes on after it
        (run whitespace slice { p with content := content.push c } (j + 1)
          (at_.afterByte c)).lift (by omega)
      else
        .error (failAtByte .forbiddenCharInQuotedSymbol p.start at_)
    else
      .pending { p with content } at_
  | .quotedSymbolClosed =>
    if h : i < slice.size then
      delimited p .quotedSymbol p.content i location slice[i] (Nat.le_refl _) h
    else
      .pending p location
  | .string =>
    let j := runEnd slice isStringRun i
    have hj : i ≤ j := le_runEnd slice isStringRun i
    let content := p.content ++ bytesOf slice i j
    let at_ := afterColumns location (j - i)
    if h : j < slice.size then
      let c := slice[j]
      if c == byte! '"' then
        (run whitespace slice { p with mode := .stringQuote, content } (j + 1)
          (at_.afterByte c)).lift (by omega)
      else if c == byte! '\n' then
        (run whitespace slice { p with content := content.push c } (j + 1)
          (at_.afterByte c)).lift (by omega)
      else
        .error (failAtByte .forbiddenCharInString p.start at_)
    else
      .pending { p with content } at_
  | .stringQuote =>
    if h : i < slice.size then
      let c := slice[i]
      -- a second quote is a quote in the content, anything else ends the string
      if c == byte! '"' then
        (run whitespace slice { p with mode := .string, content := p.content.push c } (i + 1)
          (location.afterByte c)).lift (by omega)
      else
        delimited p .string p.content i location c (Nat.le_refl _) h
    else
      .pending p location
  | .legacyString =>
    let j := runEnd slice isLegacyStringRun i
    have hj : i ≤ j := le_runEnd slice isLegacyStringRun i
    let content := p.content ++ bytesOf slice i j
    let at_ := afterColumns location (j - i)
    if h : j < slice.size then
      let c := slice[j]
      if c == byte! '"' then
        (run whitespace slice { p with mode := .legacyQuote, content } (j + 1)
          (at_.afterByte c)).lift (by omega)
      else if c == byte! '\\' then
        (run whitespace slice { p with mode := .legacyEscape, content } (j + 1)
          (at_.afterByte c)).lift (by omega)
      else if c == byte! '\n' then
        (run whitespace slice { p with content := content.push c } (j + 1)
          (at_.afterByte c)).lift (by omega)
      else
        .error (failAtByte .forbiddenCharInString p.start at_)
    else
      .pending { p with content } at_
  | .legacyEscape =>
    if h : i < slice.size then
      let c := slice[i]
      if c == byte! '"' || c == byte! '\\' then
        -- an escape: only the escaped byte is in the content
        (run whitespace slice { p with mode := .legacyString, content := p.content.push c } (i + 1)
          (location.afterByte c)).lift (by omega)
      else if isTextByte c then
        -- not an escape: the backslash is in the content, and so is the byte, which is neither
        -- a quote nor a backslash
        let content := (p.content.push (byte! '\\')).push c
        (run whitespace slice { p with mode := .legacyString, content } (i + 1)
          (location.afterByte c)).lift (by omega)
      else
        .error (failAtByte .forbiddenCharInString p.start location)
    else
      .pending p location
  | .legacyQuote =>
    if h : i < slice.size then
      delimited p .string p.content i location slice[i] (Nat.le_refl _) h
    else
      .pending p location
  | .comment =>
    let j := runEnd slice isCommentRun i
    have hj : i ≤ j := le_runEnd slice isCommentRun i
    let content := p.content ++ bytesOf slice i j
    let at_ := afterColumns location (j - i)
    if h : j < slice.size then
      let c := slice[j]
      -- the line break ends the comment and is the last byte of its content
      if whitespace then
        .tokenWith
          { category := .comment, content := content.push c, start := p.start,
            «end» := at_.afterByte c } (j + 1) (by omega)
      else
        .idle (j + 1) (at_.afterByte c) (by omega)
    else
      .pending { p with content } at_
  | .whitespace =>
    let j := runEnd slice isWhitespaceRun i
    have hj : i ≤ j := le_runEnd slice isWhitespaceRun i
    let content := p.content ++ bytesOf slice i j
    let at_ := afterColumns location (j - i)
    if h : j < slice.size then
      let c := slice[j]
      if c == byte! '\n' then
        (run whitespace slice { p with content := content.push c } (j + 1)
          (at_.afterByte c)).lift (by omega)
      else
        .tokenBefore { category := .whitespace, content, start := p.start, «end» := at_ } j hj h
    else
      .pending { p with content } at_
termination_by slice.size - i

/-! ## Where the lexemes are

The token that `run` lexes starts where the token in progress starts, and ends at or after the
location where the run started: what the hand-overs need to put the lexeme into a batch (see
`TokenBatch.ordered`).
-/

/-- What lexing the token `p` from `location` on gives, as far as where it is goes. -/
abbrev Ran.Spec (p : Pending) (location : Location) : Ran size i → Prop
  | .pending p' location' => p'.start = p.start ∧ location.offset ≤ location'.offset
  | .idle _ location' _ => location.offset ≤ location'.offset
  | .tokenWith l _ _ => l.start = p.start ∧ location.offset < l.end.offset
  | .tokenBefore l _ _ _ => l.start = p.start ∧ location.offset ≤ l.end.offset
  | .error _ => True

theorem Ran.spec_lift {p : Pending} {location : Location} {h : i ≤ i'} {r : Ran size i'}
    (hr : r.Spec p location) : (r.lift h).Spec p location := by
  cases r <;> exact hr

/-- A token lexed on from a later location is where the token lexed from the earlier one is. -/
theorem Ran.Spec.weaken {p p' : Pending} {location location' : Location} {r : Ran size i}
    (hr : r.Spec p' location') (hp : p'.start = p.start) (hl : location.offset ≤ location'.offset) :
    r.Spec p location := by
  cases r with
  | pending q l => exact ⟨hr.1.trans hp, Nat.le_trans hl hr.2⟩
  | idle _ l _ => exact Nat.le_trans hl hr
  | tokenWith l _ _ => exact ⟨hr.1.trans hp, Nat.lt_of_le_of_lt hl hr.2⟩
  | tokenBefore l _ _ _ => exact ⟨hr.1.trans hp, Nat.le_trans hl hr.2⟩
  | error _ => trivial

theorem afterColumns_offset (location : Location) (n : Nat) :
    (afterColumns location n).offset = location.offset + n :=
  rfl

theorem delimited_spec {p : Pending} {category : TokenCategory} {content : ByteArray} {j : Nat}
    {location at_ : Location} {c : UInt8} {after : i ≤ j} {inside : j < size}
    (h : location.offset ≤ at_.offset) :
    (delimited (size := size) p category content j at_ c after inside).Spec p location := by
  unfold delimited
  split
  · exact ⟨rfl, h⟩
  · trivial

theorem run_spec (whitespace : Bool) (slice : ByteSlice) (p : Pending) (i : Nat)
    (location : Location) : (run whitespace slice p i location).Spec p location := by
  fun_induction run whitespace slice p i location
  all_goals first
    | trivial
    | exact delimited_spec (Nat.le_refl _)
    | (apply delimited_spec; simp +zetaDelta only [afterColumns_offset]; omega)
    | (simp +zetaDelta only [Ran.Spec, afterColumns_offset, afterByte_offset]; omega)
    | (refine ⟨rfl, ?_⟩; simp +zetaDelta only [afterColumns_offset, afterByte_offset]; omega)
    | (refine ⟨rfl, ?_⟩; omega)
    | (apply Ran.spec_lift
       apply Ran.Spec.weaken ‹_› rfl
       simp +zetaDelta only [afterColumns_offset, afterByte_offset]; omega)

/-- `run`, with where the token it lexes is. -/
def runS (whitespace : Bool) (slice : ByteSlice) (p : Pending) (i : Nat) (location : Location) :
    {r : Ran slice.size i // r.Spec p location} :=
  ⟨run whitespace slice p i location, run_spec whitespace slice p i location⟩

/-! ## Lexing a slice -/

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

/--
How the lexer lexes from the byte at `i` with no token in progress: it gives back the outcome
and the index where lexing goes on, past `i`. `sliceStart` is the offset that lexing of the
slice last went on from (see `V2Batched.handedAlone`). The fast paths of `V4FastPaths` are such
a step. The batch fits the lexer state, and comes back fitting it (`V2Batched.Fits`).
-/
abbrev IdleStep (H : Type) (m : Type → Type) (R E : Type) :=
  (sliceStart : Nat) → (slice : ByteSlice) → (i : Nat) → i < slice.size → (core : Core) →
    (batch : Array Lexeme) → Fits sliceStart core batch →
    StateT H m {r : Outcome R E sliceStart × Core × Array Lexeme × { n // i < n } //
      Fits sliceStart r.2.1 r.2.2.1}

/--
Lexes from the byte at `i`, with no token in progress: starts the token with the naive lexer's
`start`, and lexes the rest of it with `run`. The token's delimiter is not lexed.
-/
def lexIdle : IdleStep H m R E := fun sliceStart slice i h core batch hfits => do
  let c := slice[i]
  let whitespace := Consume.consumesWhitespaceAndComments (H := H)
  let after := core.location.afterByte c
  have hle : core.frontier ≤ core.location.offset := core.frontier_le
  have hafter : core.location.offset < after.offset := by
    simp only [after, afterByte_offset]; omega
  have hlast := hfits.2
  match startS core.version whitespace core.location c with
  | ⟨.idle, _⟩ =>
    return ⟨(.next, { core with activity := .idle, location := after, startedBefore := trivial },
      batch, ⟨i + 1, by omega⟩), hfits.mono (show core.frontier ≤ after.offset by omega)⟩
  | ⟨.token l, hl⟩ =>
    have hl : l.Valid ∧ l.start = core.location ∧ l.end = core.location.afterByte c := hl
    let ⟨(outcome, core, batch), hfits, _⟩ ← emit sliceStart
      { core with activity := .idle, location := after, startedBefore := trivial } batch l hfits.1
      hfits.3 (by rw [hl.2.1]; omega) (by rw [hl.2.1, hl.2.2]; exact hafter)
      (Nat.le_of_eq (by rw [hl.2.2]; try rfl))
    return ⟨(outcome, core, batch, ⟨i + 1, by omega⟩), hfits⟩
  | ⟨.error failure, _⟩ =>
    let failure := { cause := .lexical failure.error, location := failure.location }
    return ⟨(.failed failure, core, batch, ⟨i + 1, by omega⟩), hfits⟩
  | ⟨.pending p, hp⟩ =>
    have hp : p.start = core.location := hp
    match runS whitespace slice p (i + 1) after with
    | ⟨.pending p' location, hspec⟩ =>
      have hspec : p'.start = p.start ∧ after.offset ≤ location.offset := hspec
      return ⟨(.next, { core with
          activity := .token p', location
          startedBefore := show p'.start.offset < location.offset by
            rw [hspec.1, hp]; omega },
        batch, ⟨slice.size, h⟩),
        hfits.mono (show core.frontier ≤ p'.start.offset by rw [hspec.1, hp]; exact hle)⟩
    | ⟨.idle next location hn, hspec⟩ =>
      have hspec : after.offset ≤ location.offset := hspec
      return ⟨(.next, { core with activity := .idle, location, startedBefore := trivial }, batch,
        ⟨next, by omega⟩), hfits.mono (show core.frontier ≤ location.offset by omega)⟩
    | ⟨.tokenWith l next hn, hspec⟩ =>
      have hspec : l.start = p.start ∧ after.offset < l.end.offset := hspec
      let core := { core with activity := .idle, location := l.end, startedBefore := trivial }
      let ⟨(outcome, core, batch), hfits, _⟩ ← emit sliceStart core batch l hfits.1 hfits.3
        (by rw [hspec.1, hp]; omega) (by rw [hspec.1, hp]; omega) (Nat.le_refl _)
      return ⟨(outcome, core, batch, ⟨next, by omega⟩), hfits⟩
    | ⟨.tokenBefore l next hn _, hspec⟩ =>
      have hspec : l.start = p.start ∧ after.offset ≤ l.end.offset := hspec
      -- the delimiter is lexed next; if the consumer has finished, it is the first byte
      -- discarded
      let core := { core with activity := .idle, location := l.end, startedBefore := trivial }
      let ⟨(outcome, core, batch), hfits, _⟩ ← emit sliceStart core batch l hfits.1 hfits.3
        (by rw [hspec.1, hp]; omega) (by rw [hspec.1, hp]; omega) (Nat.le_refl _)
      return ⟨(outcome, core, batch, ⟨next, by omega⟩), hfits⟩
    | ⟨.error failure, _⟩ =>
      let failure := { cause := .lexical failure.error, location := failure.location }
      return ⟨(.failed failure, core, batch, ⟨i + 1, by omega⟩), hfits⟩

/--
Lexes the token in progress `p` from the byte at `i` on with `run`. If the token ends before a
byte, lexing goes on at that byte with `idle`, as the naive lexer lexes the delimiter right
after the token.
-/
def lexToken (idle : IdleStep H m R E) (sliceStart : Nat) (slice : ByteSlice) (i : Nat)
    (h : i < slice.size) (core : Core) (batch : Array Lexeme) (p : Pending)
    (ha : core.activity = .token p) (hfits : Fits sliceStart core batch) :
    StateT H m {r : Outcome R E sliceStart × Core × Array Lexeme × { n // i < n } //
      Fits sliceStart r.2.1 r.2.2.1} := do
  let whitespace := Consume.consumesWhitespaceAndComments (H := H)
  have hp : p.start.offset < core.location.offset := core.started ha
  have hfront : core.frontier = p.start.offset := by unfold Core.frontier; rw [ha]
  have hlast := hfits.2
  match runS whitespace slice p i core.location with
  | ⟨.pending p' location, hspec⟩ =>
    have hspec : p'.start = p.start ∧ core.location.offset ≤ location.offset := hspec
    return ⟨(.next, { core with
        activity := .token p', location
        startedBefore := show p'.start.offset < location.offset by rw [hspec.1]; omega },
      batch, ⟨slice.size, h⟩),
      hfits.mono (show core.frontier ≤ p'.start.offset by rw [hspec.1]; omega)⟩
  | ⟨.idle next location hn, hspec⟩ =>
    have hspec : core.location.offset ≤ location.offset := hspec
    return ⟨(.next, { core with activity := .idle, location, startedBefore := trivial }, batch,
      ⟨next, hn⟩), hfits.mono (show core.frontier ≤ location.offset by omega)⟩
  | ⟨.tokenWith l next hn, hspec⟩ =>
    have hspec : l.start = p.start ∧ core.location.offset < l.end.offset := hspec
    let ⟨(outcome, core, batch), hfits, _⟩ ← emit sliceStart
      { core with activity := .idle, location := l.end, startedBefore := trivial } batch l hfits.1
      hfits.3 (by rw [hspec.1]; omega) (by rw [hspec.1]; omega) (Nat.le_refl _)
    return ⟨(outcome, core, batch, ⟨next, hn⟩), hfits⟩
  | ⟨.tokenBefore l next hn inside, hspec⟩ =>
    have hspec : l.start = p.start ∧ core.location.offset ≤ l.end.offset := hspec
    let ⟨(outcome, core, batch), hfits, _⟩ ← emit sliceStart
      { core with activity := .idle, location := l.end, startedBefore := trivial } batch l hfits.1
      hfits.3 (by rw [hspec.1]; omega) (by rw [hspec.1]; omega) (Nat.le_refl _)
    match outcome with
    -- the byte is lexed under the version the consumer has left in force
    | .next =>
      let ⟨(outcome, core, batch, ⟨n, hn'⟩), hfits⟩ ←
        idle sliceStart slice next inside core batch hfits
      return ⟨(outcome, core, batch, ⟨n, by omega⟩), hfits⟩
    -- the consumer has finished on the token alone: the byte is the first one discarded
    | .finished located =>
      have hmono : core.frontier ≤ (core.location.afterByte slice[next]).offset := by
        have := core.frontier_le
        rw [afterByte_offset]
        omega
      let core := { core with
        location := core.location.afterByte slice[next], activity := .discarding
        startedBefore := trivial }
      return ⟨(.finished located, core, batch, ⟨next + 1, by omega⟩), hfits.mono hmono⟩
    | outcome => return ⟨(outcome, core, batch, ⟨next + 1, by omega⟩), hfits⟩
  | ⟨.error failure, _⟩ =>
    let failure := { cause := .lexical failure.error, location := failure.location }
    return ⟨(.failed failure, core, batch, ⟨i + 1, by omega⟩), hfits⟩

/--
Lexes from the byte at `i` on, as the batched lexer's `lexByte` does at that byte, except that
a token is lexed in one go: with `idle` where no token is in progress, and with `lexToken`
where one is. Skipping and discarding go one byte at a time, by `V2Batched.lexByte`.
-/
def lexAt (idle : IdleStep H m R E) (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (i : Nat) (h : i < slice.size) (core : Core) (batch : Array Lexeme)
    (hfits : Fits sliceStart core batch) :
    StateT H m {r : Outcome R E sliceStart × Core × Array Lexeme × { n // i < n } //
      Fits sliceStart r.2.1 r.2.2.1} := do
  let byte : StateT H m
      {r : Outcome R E sliceStart × Core × Array Lexeme × { n // i < n } //
        Fits sliceStart r.2.1 r.2.2.1} := do
    let ⟨(outcome, core, batch), hfits⟩ ←
      V2Batched.lexByte recover sliceStart core batch slice[i] hfits
    return ⟨(outcome, core, batch, ⟨i + 1, by omega⟩), hfits⟩
  have hidle : ∀ (core' : Core), core'.location = core.location →
      (∀ p, core'.activity ≠ .token p) → Fits sliceStart core' batch := fun core' hl hn =>
    hfits.mono (by rw [Core.frontier_of_not_token hn, hl]; exact core.frontier_le)
  match withEq core.activity with
  | ⟨.idle, _⟩ => idle sliceStart slice i h core batch hfits
  | ⟨.token p, ha⟩ => lexToken idle sliceStart slice i h core batch p ha hfits
  | ⟨.recovered, _⟩ =>
    -- the consumer is told of a recovery before any token
    recover core.location
    idle sliceStart slice i h { core with activity := .idle, startedBefore := trivial } batch
      (hidle _ rfl fun _ h => nomatch h)
  | ⟨.skipping skip, _⟩ =>
    if scan (core.version == .v2_0) skip core.depth slice[i] == .before then
      recover core.location
      idle sliceStart slice i h { core with activity := .idle, startedBefore := trivial } batch
        (hidle _ rfl fun _ h => nomatch h)
    else
      byte
  | ⟨.discarding, _⟩ | ⟨.ended, _⟩ => byte

/--
Lexes the slice from `index` on and hands the batch over at the end, as the batched lexer's
`lexFrom` does, except that it steps by `lexAt`.
-/
def lexFrom (idle : IdleStep H m R E) (recover : Location → StateT H m Unit) (sliceStart : Nat)
    (slice : ByteSlice) (index committed : Nat) (core : Core) (batch : Array Lexeme)
    (flow : ControlFlow (Located R)) (hfits : Fits (sliceStart + committed) core batch) :
    StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core) := do
  if h : index < slice.size then
    let ⟨(outcome, core, batch, ⟨next, _hn⟩), hfits⟩ ←
      lexAt idle recover (sliceStart + committed) slice index h core batch hfits
    match ← settle outcome core batch flow hfits with
    | .proceed core batch flow hfits =>
      lexFrom idle recover sliceStart slice next committed core batch flow hfits
    | .fail failure core => return (.error failure, core)
    | .stop stop core flow =>
      match withEq (resumption stop flow) with
      | ⟨.error failure, _⟩ => return (.error failure, core)
      | ⟨.ok (location, activity, flow), hres⟩ =>
        let resumed := location.offset - sliceStart
        let core := { core with location, activity, startedBefore := resumption_startsBefore hres }
        if _hr : resumed < slice.size then
          lexFrom idle recover sliceStart slice resumed resumed core #[] flow (fits_empty _ _)
        else
          -- the location is at the end of the slice, where nothing is left to lex
          return (.ok flow, core)
  else
    match ← settleEnd core batch flow hfits with
    | .proceed core _ flow _ => return (.ok flow, core)
    | .fail failure core => return (.error failure, core)
    | .stop stop core flow =>
      match withEq (resumption stop flow) with
      | ⟨.error failure, _⟩ => return (.error failure, core)
      | ⟨.ok (location, activity, flow), hres⟩ =>
        let resumed := location.offset - sliceStart
        let core := { core with location, activity, startedBefore := resumption_startsBefore hres }
        if _hr : resumed < slice.size then
          lexFrom idle recover sliceStart slice resumed resumed core #[] flow (fits_empty _ _)
        else
          -- the location is at the end of the slice, where nothing is left to lex
          return (.ok flow, core)
termination_by (slice.size - committed, slice.size - index)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · have := resumption_after hres
    exact Prod.Lex.left _ _ (by omega)
  · have := resumption_after hres
    exact Prod.Lex.left _ _ (by omega)

/-- Lexes the slice, or discards it if the consumer has finished, as the batched lexer's
`lexSliceStep` does, except that it lexes by `lexFrom` with `idle`. -/
def lexSliceStep (idle : IdleStep H m R E) (recovers : Bool)
    (abandon recover : Location → StateT H m Unit) (slice : ByteSlice) (core : Core) :
    StateT H m (Except (LexError E) (ControlFlow (Located R)) × Core) := do
  let core ← match core.activity with
    -- the consumer failed after a whole token with nothing open: the recovery is made here,
    -- even if the slice is empty
    | .recovered => do
      recover core.location
      pure { core with activity := .idle, startedBefore := trivial }
    | _ => pure core
  match core.activity with
  -- the input has ended with the error, there is nothing to lex
  | .ended => return (.ok .continue, core)
  | _ =>
    let (result, core) ← lexFrom idle recover core.location.offset slice 0 0 core #[] .continue
      (fits_empty _ _)
    match result with
    | .ok flow => return (.ok flow, core)
    | .error failure =>
      let (err, core) ← failCall recovers abandon failure false core
      return (.error err, core)

end

/-! ## The lexer

The lexer over runs is the naive lexer's type `V1Naive.Lexer` with the operations below in place
of its `lexSlice` and `lexAll`; the other operations are the naive lexer's: `new`,
`newRecovering`, `lexEof`, `PendingEof.lexEof`, `currentLocation` and `version`.
-/

private def afterError :
    {recovery : Recovery} → V1Naive.Lexer H recovery → V1Naive.Lexer.AfterError H recovery
  | .failFast, _ => ()
  | .recovering, lexer => lexer

/--
Lexes the given slice with `idle` where no token is in progress, sending the lexed tokens to the
consumer; see `lexSlice`.
-/
def lexSliceWith [Monad m] [Consume H m R E] [LexRecovery recovery H m]
    (idle : IdleStep H m R E) (self : V1Naive.Lexer H recovery) (slice : ByteSlice) :
    m (Except (LexError E × V1Naive.Lexer.AfterError H recovery)
      (ControlFlow (Located R) × V1Naive.Lexer H recovery)) := do
  let step := lexSliceStep idle (recovery == .recovering) (LexRecovery.abandon recovery)
    (LexRecovery.recover recovery) slice
  let { handler, core } := self
  let ((result, core), handler) ← (step core).run handler
  let self : V1Naive.Lexer H recovery := { handler, core }
  return match result with
    | .ok flow => .ok (flow, self)
    | .error err => .error (err, afterError self)

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

end BSmtLib.Proofs.Lexer.V3Runs

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
is lexed under `version` in a slice that lexing last went on from at the offset `sliceStart`:
the first byte of the slice, or the end of the last token the consumer took before it asked to
relex, before which no token lexed after it starts.

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

/-- A lexeme that is not handed over alone starts at or after the offset lexing went on from. -/
theorem le_start_of_not_handedAlone {version : Version} {sliceStart : Nat} {l : Lexeme}
    (h : ¬ handedAlone version sliceStart l = true) : sliceStart ≤ l.start.offset := by
  unfold handedAlone at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h
  exact Nat.le_of_not_lt h.1

/--
Whether the lexemes are in input order after the offset `after`: each has a byte unless it is
the end of file, and starts at or after the end of the one before it, the first one at or after
`after`.
-/
def Ordered : Nat → List Lexeme → Prop
  | _, [] => True
  | after, l :: ls => after ≤ l.start.offset ∧ l.Valid ∧ Ordered l.end.offset ls

/-- The offset where the last of the lexemes ends, `after` if there are none. -/
def lastEnd : Nat → List Lexeme → Nat
  | after, [] => after
  | _, l :: ls => lastEnd l.end.offset ls

theorem ordered_append {after : Nat} {ls : List Lexeme} {l : Lexeme} (h : Ordered after ls)
    (hl : lastEnd after ls ≤ l.start.offset) (hv : l.Valid) : Ordered after (ls ++ [l]) := by
  induction ls generalizing after with
  | nil => exact ⟨hl, hv, trivial⟩
  | cons l' ls ih => exact ⟨h.1, h.2.1, ih h.2.2 hl⟩

theorem lastEnd_append (after : Nat) (ls : List Lexeme) (l : Lexeme) :
    lastEnd after (ls ++ [l]) = l.end.offset := by
  induction ls generalizing after with
  | nil => rfl
  | cons l' ls ih => exact ih _

/-- Appends the lexemes, in order after the end of the last token, to the batch, with their
contents one after the other. -/
def pushLexemes (batch : TokenBatch) : (ls : List Lexeme) → Ordered batch.lastEnd ls → TokenBatch
  | [], _ => batch
  | l :: ls, ⟨hstart, hvalid, hrest⟩ =>
    let start := batch.bytes.size
    let pushed := ({ batch with bytes := batch.bytes ++ l.content } : TokenBatch).pushLocated
      l.category start (start + l.content.size) l.start l.end hstart hvalid
    pushLexemes pushed ls ((TokenBatch.lastEnd_pushLocated ..).symm ▸ hrest)

/-- The batch of the lexemes, in order, with their contents one after the other. -/
def toTokenBatch (lexemes : Array Lexeme) (h : Ordered 0 lexemes.toList) : TokenBatch :=
  pushLexemes (TokenBatch.empty lexemes.size) lexemes.toList h

/-- Whether every one of the lexemes ends after the offset. -/
def EndsAfter (floor : Nat) (ls : List Lexeme) : Prop :=
  ∀ l ∈ ls, floor < l.end.offset

theorem endsAfter_pushLexemes {floor : Nat} {batch : TokenBatch} (hb : batch.EndsAfter floor) :
    {ls : List Lexeme} → (h : Ordered batch.lastEnd ls) → EndsAfter floor ls →
      (pushLexemes batch ls h).EndsAfter floor
  | [], _, _ => hb
  | l :: ls, ⟨_, _, _⟩, hls => by
    simp only [pushLexemes]
    have hb' : ({ batch with bytes := batch.bytes ++ l.content } : TokenBatch).EndsAfter floor :=
      hb
    exact endsAfter_pushLexemes
      (TokenBatch.endsAfter_pushLocated hb' (hls l List.mem_cons_self))
      _ fun l' hl' => hls l' (List.mem_cons_of_mem _ hl')

/-- The batch of lexemes that end after the offset ends after it. -/
theorem endsAfter_toTokenBatch {floor : Nat} {lexemes : Array Lexeme}
    (h : Ordered 0 lexemes.toList) (ha : EndsAfter floor lexemes.toList) :
    (toTokenBatch lexemes h).EndsAfter floor :=
  endsAfter_pushLexemes (batch := TokenBatch.empty lexemes.size)
    (fun _ h => absurd h (Nat.not_lt_zero _)) h ha

/-- The batch of the lexer state: its lexemes are in order, end at or before the frontier of
the state, and end after `floor`, the offset that lexing of the slice last went on from. -/
structure Fits (floor : Nat) (core : Core) (batch : Array Lexeme) : Prop where
  ordered : Ordered 0 batch.toList
  ended : lastEnd 0 batch.toList ≤ core.frontier
  after : EndsAfter floor batch.toList

theorem fits_empty (floor : Nat) (core : Core) : Fits floor core #[] :=
  ⟨trivial, Nat.zero_le _, fun _ h => nomatch h⟩

/-- A batch fits a state whose frontier is further on. -/
theorem Fits.mono {floor : Nat} {core core' : Core} {batch : Array Lexeme}
    (h : Fits floor core batch) (hf : core.frontier ≤ core'.frontier) : Fits floor core' batch :=
  ⟨h.1, Nat.le_trans h.2 hf, h.3⟩

/-- Why the consumer stopped in a batch whose tokens end after `floor`: at the end of a token it
took, which is after `floor`. -/
inductive Stop (R E : Type) (floor : Nat) where
  /-- It switched the version so that the rest is to be lexed again from the location. -/
  | relex (location : Location) (after : floor < location.offset)
  /-- It finished, at the location of the value; the rest of the input is discarded. -/
  | finished (located : Located R) (after : floor < located.location.offset)
  | failed (failure : Failure E)

/-- What lexing a byte leaves to the loop over the slice, whose batch ends after `floor`. -/
inductive Outcome (R E : Type) (floor : Nat) where
  /-- Lexing goes on with the next byte. -/
  | next
  /-- The consumer finished on a token handed over alone; the input is discarded from the next
  byte on. -/
  | finished (located : Located R)
  /-- The consumer stopped in a batch. -/
  | stopped (stop : Stop R E floor)
  /-- The byte raised a lexical error, or the consumer failed on a token handed over alone. -/
  | failed (failure : Failure E)

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

/- As in the naive lexer, the functions below thread the lexer state `Core` and the batch
through by hand, while the consumer is the state of the monad `StateT H m`. The batch comes
back with the proof that it fits the state (`Fits`). -/

/--
Hands the cursor over to the consumer until nothing remains in it or the consumer stops.

Returns the stop, if the consumer stopped, and the cursor as the consumer left it. A stop takes
effect at the end of the last token the consumer took, which is after `floor`, as every token of
the cursor ends after it.
-/
def handOverCursor {floor : Nat} (cursor : BatchCursor) (hfloor : cursor.EndsAfter floor) :
    StateT H m (Option (Stop R E floor) × BatchCursor) := do
  if h : cursor.HasNext then
    let (answer, ⟨next, consumed⟩) ← Consume.consume (H := H) cursor h
    let location := next.consumedEndOf consumed
    have after : floor < location.offset := consumed.lt_consumedEndOf hfloor
    match answer with
    | .ok .continue =>
      if next.relexRequested then
        return (some (.relex location after), next)
      else
        -- the tokens left are handed over again
        have : next.resetConsumed.remaining < cursor.remaining := by
          rw [BatchCursor.remaining_resetConsumed]
          exact consumed.remaining_lt
        handOverCursor next.resetConsumed
          (BatchCursor.endsAfter_resetConsumed (consumed.follows.endsAfter hfloor))
    | .ok (.break value) => return (some (.finished { value, location } after), next)
    | .error err => return (some (.failed { cause := .consumer err, location }), next)
  else
    return (none, cursor)
termination_by cursor.remaining

/--
Hands the batch over under the version in force, if it has a token. The version on the cursor
the consumer leaves is in force from then on, and the tokens it took count for the parentheses
open.
-/
def flush {floor : Nat} (core : Core) (batch : Array Lexeme) (h : Ordered 0 batch.toList)
    (hafter : EndsAfter floor batch.toList) : StateT H m (Option (Stop R E floor) × Core) := do
  let (stop, cursor) ← handOverCursor (BatchCursor.new core.version (toTokenBatch batch h))
    (BatchCursor.endsAfter_new (endsAfter_toTokenBatch h hafter) _)
  return (stop, { core with
    version := cursor.version
    depth := cursor.foldConsumedCategories core.depth depthAfter })

/--
The lexer state that a hand-over gives back, from the state `core` handed in and the state
`after` it left: the location and the activity are those handed in, but for a consumer that
finished on a token alone, after which the input is discarded.
-/
def fixCore {floor : Nat} (core : Core) (outcome : Outcome R E floor) (after : Core) : Core :=
  { after with
    location := core.location
    activity := match outcome with
      | .finished _ => .discarding
      | _ => core.activity
    startedBefore := by cases outcome <;> first | trivial | exact core.startedBefore }

theorem fixCore_fixCore {floor : Nat} (core : Core) (outcome : Outcome R E floor)
    (after : Core) :
    fixCore core outcome (fixCore core outcome after) = fixCore core outcome after :=
  rfl

theorem fixCore_self {floor : Nat} (core : Core) :
    fixCore (R := R) (E := E) (floor := floor) core .next core = core :=
  rfl

/-- What a hand-over that leaves an empty batch gives back. -/
def handedOver {floor : Nat} (core : Core) (outcome : Outcome R E floor) (after : Core) :
    {r : Outcome R E floor × Core × Array Lexeme //
      Fits floor r.2.1 r.2.2 ∧ r.2.1 = fixCore core r.1 r.2.1} :=
  ⟨(outcome, fixCore core outcome after, #[]), fits_empty _ _,
    (fixCore_fixCore core outcome after).symm⟩

/--
Hands the lexeme over: alone, after the batch, if `handedAlone` says so, or in the batch,
which is handed over when it is full. `sliceStart` is the offset that lexing of the slice last
went on from, which the tokens of the batch end after. The lexeme starts at or after the end of
the batch, has a byte, and ends at or before the frontier of the state. The state given back is
the one handed in, as `fixCore` gives it.
-/
/- The state given back is written with the location and the activity that the hand-overs
leave, as `fixCore` gives them, so that its type says so. -/
def emit (sliceStart : Nat) (core : Core) (batch : Array Lexeme) (l : Lexeme)
    (h : Ordered 0 batch.toList) (hafter : EndsAfter sliceStart batch.toList)
    (hstart : lastEnd 0 batch.toList ≤ l.start.offset) (hl : l.start.offset < l.end.offset)
    (hend : l.end.offset ≤ core.frontier) :
    StateT H m
      {r : Outcome R E sliceStart × Core × Array Lexeme //
        Fits sliceStart r.2.1 r.2.2 ∧ r.2.1 = fixCore core r.1 r.2.1} :=
    do
  if halone : handedAlone core.version sliceStart l then
    let (stop, after) ← flush core batch h hafter
    if let some stop := stop then
      return handedOver core (.stopped stop) after
    -- the naive lexer's hand-over of a token alone; its version applies from the next byte on,
    -- which is not lexed yet
    let (result, after) ← handOverAt after l (.inl hl)
    return match result with
      | .ok none => handedOver core .next after
      | .ok (some located) => handedOver core (.finished located) after
      | .error failure => handedOver core (.failed failure) after
  else
    have hpush : Ordered 0 (batch.push l).toList := by
      rw [Array.toList_push]
      exact ordered_append h hstart (.inl hl)
    have hpushAfter : EndsAfter sliceStart (batch.push l).toList := by
      rw [Array.toList_push]
      intro l' hl'
      rcases List.mem_append.mp hl' with hl' | hl'
      · exact hafter l' hl'
      · rw [List.mem_singleton.mp hl']
        exact Nat.lt_of_le_of_lt (le_start_of_not_handedAlone halone) hl
    let batch := batch.push l
    if batch.size < batchCapacity then
      return ⟨(.next, core, batch), ⟨hpush, by
        show lastEnd 0 (batch.toList) ≤ _
        simp only [batch, Array.toList_push, lastEnd_append]
        exact hend, hpushAfter⟩, (fixCore_self _).symm⟩
    let (stop, after) ← flush core batch hpush hpushAfter
    return match stop with
      | some stop => handedOver core (.stopped stop) after
      | none => handedOver core .next after

/-- Lexes the byte `c` with no token in progress. -/
def lexStart (sliceStart : Nat) (core : Core) (batch : Array Lexeme) (c : UInt8)
    (hfits : Fits sliceStart core batch) :
    StateT H m
      {r : Outcome R E sliceStart × Core × Array Lexeme // Fits sliceStart r.2.1 r.2.2} := do
  let whitespace := Consume.consumesWhitespaceAndComments (H := H)
  let after := core.location.afterByte c
  have hle : core.frontier ≤ core.location.offset := core.frontier_le
  have hafter : core.location.offset < after.offset := by
    simp only [after, afterByte_offset]; omega
  have hlast := hfits.2
  match startS core.version whitespace core.location c with
  | ⟨.idle, _⟩ =>
    return ⟨(.next, { core with activity := .idle, location := after, startedBefore := trivial },
      batch), hfits.mono (show core.frontier ≤ after.offset by omega)⟩
  | ⟨.pending p, hp⟩ =>
    have hp : p.start = core.location := hp
    return ⟨(.next, { core with
        activity := .token p, location := after
        startedBefore := by
          show p.start.offset < after.offset
          rw [hp]; exact hafter },
      batch), hfits.mono (show core.frontier ≤ p.start.offset by rw [hp]; exact hle)⟩
  | ⟨.token l, hl⟩ =>
    have hl : l.Valid ∧ l.start = core.location ∧ l.end = core.location.afterByte c := hl
    let ⟨r, hfits, _⟩ ← emit sliceStart
      { core with activity := .idle, location := after, startedBefore := trivial }
      batch l hfits.1 hfits.3 (by rw [hl.2.1]; omega) (by rw [hl.2.1, hl.2.2]; exact hafter)
      (Nat.le_of_eq (by rw [hl.2.2]; try rfl))
    return ⟨r, hfits⟩
  | ⟨.error failure, _⟩ =>
    return ⟨(.failed { cause := .lexical failure.error, location := failure.location }, core,
      batch), hfits⟩

/--
Lexes the byte `c`, at the lexer's location, as the naive lexer's `lexByte` does, except that
the tokens go through `emit`.

`recover` is the consumer's call at the end of a recovery.
-/
def lexByte (recover : Location → StateT H m Unit) (sliceStart : Nat) (core : Core)
    (batch : Array Lexeme) (c : UInt8) (hfits : Fits sliceStart core batch) :
    StateT H m
      {r : Outcome R E sliceStart × Core × Array Lexeme // Fits sliceStart r.2.1 r.2.2} := do
  let location := core.location
  have hle : core.frontier ≤ location.offset := core.frontier_le
  have hafter : location.offset < (location.afterByte c).offset := by
    rw [afterByte_offset]; omega
  have hlast := hfits.2
  match withEq core.activity with
  | ⟨.discarding, _⟩ =>
    return ⟨(.next, { core with
        location := location.afterByte c, activity := .discarding, startedBefore := trivial },
      batch), hfits.mono (show core.frontier ≤ (location.afterByte c).offset by omega)⟩
  -- only the end of the input can follow, there is nothing to lex
  | ⟨.ended, _⟩ => return ⟨(.next, core, batch), hfits⟩
  | ⟨.recovered, _⟩ =>
    -- the consumer is told of a recovery before any token
    recover location
    lexStart sliceStart { core with activity := .idle, startedBefore := trivial } batch c
      (hfits.mono (show core.frontier ≤ location.offset from hle))
  | ⟨.skipping skip, _⟩ =>
    match scan (core.version == .v2_0) skip core.depth c with
    | .skip skip depth =>
      have hmono : core.frontier ≤ (location.afterByte c).offset := by omega
      let core := { core with
        location := location.afterByte c, activity := .skipping skip, depth
        startedBefore := trivial }
      return ⟨(.next, core, batch), hfits.mono
        (by rw [Core.frontier_of_not_token (core := core) fun _ h => nomatch h]; exact hmono)⟩
    | .before =>
      recover location
      lexStart sliceStart { core with activity := .idle, startedBefore := trivial } batch c
        (hfits.mono (show core.frontier ≤ location.offset from hle))
    | .after =>
      let location' := location.afterByte c
      recover location'
      return ⟨(.next, { core with
          location := location', activity := .idle, depth := 0, startedBefore := trivial },
        batch), hfits.mono (show core.frontier ≤ (location.afterByte c).offset by omega)⟩
  | ⟨.idle, _⟩ => lexStart sliceStart core batch c hfits
  | ⟨.token p, ha⟩ =>
    let whitespace := Consume.consumesWhitespaceAndComments (H := H)
    let after := location.afterByte c
    have hp : p.start.offset < location.offset := core.started ha
    have hfront : core.frontier ≤ p.start.offset :=
      Nat.le_of_eq (by unfold Core.frontier; rw [ha])
    match advanceS whitespace p location c with
    | ⟨.pending p', h⟩ =>
      have h : p'.start = p.start := h
      return ⟨(.next, { core with
          activity := .token p', location := after
          startedBefore := by
            show p'.start.offset < (location.afterByte c).offset
            rw [h]; omega },
        batch), hfits.mono (show core.frontier ≤ p'.start.offset by rw [h]; exact hfront)⟩
    | ⟨.idle, _⟩ =>
      return ⟨(.next, { core with activity := .idle, location := after, startedBefore := trivial },
        batch), hfits.mono (show core.frontier ≤ (location.afterByte c).offset by omega)⟩
    | ⟨.tokenWith l, h⟩ =>
      have h : l.start = p.start ∧ l.end = location.afterByte c := h
      let ⟨r, hfits, _⟩ ← emit sliceStart
        { core with activity := .idle, location := after, startedBefore := trivial }
        batch l hfits.1 hfits.3 (by rw [h.1]; omega) (by rw [h.1, h.2]; omega)
        (Nat.le_of_eq (by rw [h.2]; try rfl))
      return ⟨r, hfits⟩
    | ⟨.tokenBefore l, h⟩ =>
      have h : l.start = p.start ∧ l.end = location := h
      let ⟨(outcome, core, batch), hfits, hfix⟩ ←
        emit sliceStart { core with activity := .idle, startedBefore := trivial } batch l hfits.1
          hfits.3 (by rw [h.1]; omega) (by rw [h.1, h.2]; exact hp)
          (Nat.le_of_eq (by rw [h.2]; try rfl))
      match outcome with
      -- the byte is lexed under the version the consumer has left in force
      | .next => lexStart sliceStart core batch c hfits
      -- the consumer has finished on the token alone: the byte is the first one discarded
      | .finished located =>
        have hloc : core.location = location := (congrArg Core.location hfix :)
        return ⟨(.finished located, { core with
            location := after, activity := .discarding, startedBefore := trivial }, batch),
          hfits.mono (show core.frontier ≤ (location.afterByte c).offset by
            have := core.frontier_le
            rw [hloc] at this
            omega)⟩
      | outcome => return ⟨(outcome, core, batch), hfits⟩
    | ⟨.error failure, _⟩ =>
      let failure := { cause := .lexical failure.error, location := failure.location }
      return ⟨(.failed failure, core, batch), hfits⟩

/-- What the loop over the slice does next, with the batch ending after `floor`. -/
inductive Next (R E : Type) (floor : Nat) where
  /-- Lexing goes on with the next byte, or ends at the end of the slice. -/
  | proceed (core : Core) (batch : Array Lexeme) (flow : ControlFlow (Located R))
    (fits : Fits floor core batch)
  /-- The consumer stopped in a batch. -/
  | stop (stop : Stop R E floor) (core : Core) (flow : ControlFlow (Located R))
  | fail (failure : Failure E) (core : Core)

/--
What the loop does after the outcome of a byte: a lexical error hands the batch before it over
first, and is reported only if the consumer takes the batch whole.
-/
def settle {floor : Nat} (outcome : Outcome R E floor) (core : Core) (batch : Array Lexeme)
    (flow : ControlFlow (Located R)) (hfits : Fits floor core batch) :
    StateT H m (Next R E floor) := do
  match outcome with
  | .next => return .proceed core batch flow hfits
  | .finished located => return .proceed core batch (.break located) hfits
  | .stopped stop => return .stop stop core flow
  | .failed failure =>
    let (stop, core) ← flush core batch hfits.1 hfits.3
    return match stop with
      | none => .fail failure core
      | some stop => .stop stop core flow

/-- What the loop does at the end of the slice: it hands the batch over. -/
def settleEnd {floor : Nat} (core : Core) (batch : Array Lexeme)
    (flow : ControlFlow (Located R)) (hfits : Fits floor core batch) :
    StateT H m (Next R E floor) := do
  let (stop, core) ← flush core batch hfits.1 hfits.3
  return match stop with
    | none => .proceed core #[] flow (fits_empty _ _)
    | some stop => .stop stop core flow

end

/--
Where lexing goes on after the consumer stopped in a batch: at the end of the last token it
took, with the activity there and the flow; or the failure to return.
-/
def resumption {floor : Nat} (stop : Stop R E floor) (flow : ControlFlow (Located R)) :
    Except (Failure E) (Location × Activity × ControlFlow (Located R)) :=
  match stop with
  | .relex location _ => .ok (location, .idle, flow)
  | .finished located _ => .ok (located.location, .discarding, .break located)
  | .failed failure => .error failure

/-- The activity to resume with is not a token in progress. -/
theorem resumption_startsBefore {floor : Nat} {stop : Stop R E floor}
    {flow : ControlFlow (Located R)} {location : Location} {activity : Activity}
    {flow' : ControlFlow (Located R)} (h : resumption stop flow = .ok (location, activity, flow')) :
    activity.StartsBefore location := by
  unfold resumption at h
  split at h <;> cases h <;> trivial

/-- The location to resume at is after the floor of the stop. -/
theorem resumption_after {floor : Nat} {stop : Stop R E floor} {flow : ControlFlow (Located R)}
    {location : Location} {activity : Activity} {flow' : ControlFlow (Located R)}
    (h : resumption stop flow = .ok (location, activity, flow')) : floor < location.offset := by
  unfold resumption at h
  split at h <;> cases h <;> assumption

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [Consume H m R E]

/--
Lexes the bytes of the slice from `index` on, and hands the batch over at the end. `flow` is
the consumer's finish, if it has finished on an earlier token of the slice. `sliceStart` is the
offset of the first byte of the slice.

When the consumer stops in a batch, the loop goes back to the end of the last token it took and
goes on from there with an empty batch, or ends there at the end of the slice. `committed` is
the index of the byte where the loop last went on so: every token of the batch ends after it
(`Fits`), as it starts at or after it and has a byte, so a stop is after it (`Stop`).
-/
def lexFrom (recover : Location → StateT H m Unit) (sliceStart : Nat) (slice : ByteSlice)
    (index committed : Nat) (core : Core) (batch : Array Lexeme) (flow : ControlFlow (Located R))
    (hfits : Fits (sliceStart + committed) core batch) :
    StateT H m (Except (Failure E) (ControlFlow (Located R)) × Core) := do
  if h : index < slice.size then
    let ⟨(outcome, core, batch), hfits⟩ ←
      lexByte recover (sliceStart + committed) core batch slice[index] hfits
    match ← settle outcome core batch flow hfits with
    | .proceed core batch flow hfits =>
      lexFrom recover sliceStart slice (index + 1) committed core batch flow hfits
    | .fail failure core => return (.error failure, core)
    | .stop stop core flow =>
      match withEq (resumption stop flow) with
      | ⟨.error failure, _⟩ => return (.error failure, core)
      | ⟨.ok (location, activity, flow), hres⟩ =>
        let resumed := location.offset - sliceStart
        let core := { core with location, activity, startedBefore := resumption_startsBefore hres }
        if hr : resumed < slice.size then
          lexFrom recover sliceStart slice resumed resumed core #[] flow (fits_empty _ _)
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
        if hr : resumed < slice.size then
          lexFrom recover sliceStart slice resumed resumed core #[] flow (fits_empty _ _)
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

/-- Lexes the slice, or discards it if the consumer has finished. -/
def lexSliceStep (recovers : Bool) (abandon recover : Location → StateT H m Unit)
    (slice : ByteSlice) (core : Core) :
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
    let (result, core) ← lexFrom recover core.location.offset slice 0 0 core #[] .continue
      (fits_empty _ _)
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

import BSmtLib.Facts.Proofs.Lexer.VNaive

/-!
# The naive lexer's pure run for every consumer

`VNaive.Run` states the naive lexer's pure run for a consumer that does not take whitespace and
comments. This module states it for both kinds of consumers, by a flag `ws` that says whether
the consumer takes them (`byteStepW`, `lexBytesW`, `endStepW`), and proves of it:

- with the flag off, it is the run of `VNaive.Run` (`byteStepW_false`, `lexBytesW_false`,
  `endStepW_false`);
- it is the same from any location, with the locations of its lexemes moved by where it starts
  (`lexBytesW_shift`, `endStepW_shift`);
- with the flag on, it finishes the same lexemes as with the flag off, and the lexemes of
  whitespace and comments among them (`lexBytesW_layout`, `endStepW_layout`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.Pure

open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Lexer.VNaive.Facts BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Lexer.Error BSmtLib.Lexer.Internal.VNaive

/-! ## The pure run with whitespace and comments -/

/-- The byte `c` at `location` with no token in progress, for a consumer that takes whitespace
and comments if `ws`: the state after it and the lexemes it finishes, or none on an error. -/
def startStepW (version : Token.Version) (ws : Bool) (location : Span.Location) (c : UInt8) :
    Option (St × List Lexeme) :=
  match start version ws location c with
  | .idle => some (.idle, [])
  | .pending p => some (.token p, [])
  | .token l => some (.idle, [l])
  | .error _ => none

/-- The byte `c` at `location` in the state, for a consumer that takes whitespace and comments
if `ws`: the state after it and the lexemes it finishes, or none on an error. A byte that
delimits a token is lexed again with no token in progress. -/
def byteStepW (version : Token.Version) (ws : Bool) : St → Span.Location → UInt8 → Option
    (St × List Lexeme)
  | .idle, location, c => startStepW version ws location c
  | .token p, location, c =>
    match advance ws p location c with
    | .pending p => some (.token p, [])
    | .idle => some (.idle, [])
    | .tokenWith l => some (.idle, [l])
    | .tokenBefore l => (startStepW version ws location c).map fun (st, ls) => (st, l :: ls)
    | .error _ => none

/-- The lexemes that the byte `c` at `location` finishes in the state before the pure step
fails at it. -/
def failedBeforeW (ws : Bool) : St → Span.Location → UInt8 → List Lexeme
  | .idle, _, _ => []
  | .token p, location, c =>
    match advance ws p location c with
    | .tokenBefore l => [l]
    | _ => []

/-- The bytes from the state at `location`: the state and the location after them and the
lexemes they finish, or on an error, the lexemes finished before it. -/
def lexBytesW (version : Token.Version) (ws : Bool) : St → Span.Location → List UInt8 →
    Except (List Lexeme) (St × Span.Location × List Lexeme)
  | st, location, [] => .ok (st, location, [])
  | st, location, c :: cs =>
    match byteStepW version ws st location c with
    | none => .error (failedBeforeW ws st location c)
    | some (st', ls) => withBefore ls (lexBytesW version ws st' (location.afterByte c) cs)

/-- The end of the input in the state at `location`: the lexemes it finishes, the end-of-file
one last, or none on an error. -/
def endStepW (ws : Bool) : St → Span.Location → Option (List Lexeme)
  | .idle, location => some [eofLexeme location]
  | .token p, location =>
    match finish ws p location with
    | .none => some [eofLexeme location]
    | .token l => some [l, eofLexeme location]
    | .error _ => none

theorem startStepW_false (version : Token.Version) : startStepW version false = startStep version
    := rfl

theorem byteStepW_false (version : Token.Version) : byteStepW version false = byteStep version := by
  funext st location c
  cases st <;> rfl

theorem failedBeforeW_false : failedBeforeW false = failedBefore := by
  funext st location c
  cases st <;> rfl

theorem lexBytesW_false (version : Token.Version) : lexBytesW version false = lexBytes version := by
  funext st location bytes
  induction bytes generalizing st location with
  | nil => rfl
  | cons c bytes ih =>
    simp only [lexBytesW, lexBytes, byteStepW_false, failedBeforeW_false]
    cases byteStep version st location c with
    | none => rfl
    | some r => simp only [ih]

theorem endStepW_false : endStepW false = endStep := by
  funext st location
  cases st <;> rfl

theorem lexBytesW_append (version : Token.Version) (ws : Bool) (st : St) (location : Span.Location)
    (a b : List UInt8) :
    lexBytesW version ws st location (a ++ b) =
      match lexBytesW version ws st location a with
      | .ok (st', location', ls) => withBefore ls (lexBytesW version ws st' location' b)
      | .error ls => .error ls := by
  induction a generalizing st location with
  | nil =>
    simp only [List.nil_append, lexBytesW, withBefore_nil]
  | cons c a ih =>
    simp only [List.cons_append, lexBytesW]
    cases byteStepW version ws st location c with
    | none => rfl
    | some r =>
      obtain ⟨st', ls⟩ := r
      simp only [ih]
      cases lexBytesW version ws st' (location.afterByte c) a with
      | error ls' => rfl
      | ok r' =>
        obtain ⟨st'', location'', ls'⟩ := r'
        exact withBefore_withBefore ls ls' _

/-! ## Moving the run -/

/-- The location, located from the start of what follows the location `base`, as located from
the start of the input. -/
def locShift (base location : Span.Location) : Span.Location :=
  { offset := base.offset + location.offset
    line := base.line + location.line
    column := if location.line = 0 then base.column + location.column else location.column }

theorem locShift_initial (base : Span.Location) : locShift base Span.Location.initial = base := by
  simp [locShift, Span.Location.initial]

theorem locShift_afterColumn (base location : Span.Location) :
    (locShift base location).afterColumn = locShift base location.afterColumn := by
  by_cases h : location.line = 0 <;>
    simp [locShift, Span.Location.afterColumn, h, Nat.add_assoc]

theorem locShift_afterByte (base location : Span.Location) (c : UInt8) :
    (locShift base location).afterByte c = locShift base (location.afterByte c) := by
  unfold Span.Location.afterByte
  split
  · simp [locShift, Nat.add_assoc]
  · exact locShift_afterColumn base location

theorem advanceLoc_shift (base location : Span.Location) (bytes : List UInt8) :
    advanceLoc (locShift base location) bytes = locShift base (advanceLoc location bytes) := by
  induction bytes generalizing location with
  | nil => rfl
  | cons c bytes ih =>
    simp only [advanceLoc, List.foldl_cons] at ih ⊢
    rw [locShift_afterByte, ih]

/-- The location after `a ++ b` is the location after `b`, moved by the location after `a`. -/
theorem locAfter_append_shift (a b : List UInt8) :
    locAfter (a ++ b) = locShift (locAfter a) (locAfter b) := by
  rw [locAfter_append]
  show advanceLoc (locAfter a) b = locShift (locAfter a) (advanceLoc Span.Location.initial b)
  rw [← advanceLoc_shift, locShift_initial]

theorem locAfter_offset' (bytes : List UInt8) : (locAfter bytes).offset = bytes.length := by
  rw [← List.reverse_reverse bytes]
  generalize bytes.reverse = rs
  induction rs with
  | nil => rfl
  | cons c rs ih =>
    rw [List.reverse_cons, locAfter_concat, afterByte_offset, ih]
    simp

/-- A location moved by the location after `before` is, in the spec's form, the spec's location
read after `before`. -/
theorem toLocation_shift (before : List UInt8) (location : Span.Location) :
    toLocation (locShift (locAfter before) location) = (toLocation location).after before := by
  have h := toLocation_locAfter before
  have h1 := congrArg BSmtLibSpec.Lexer.Location.line h
  have h2 := congrArg BSmtLibSpec.Lexer.Location.column h
  simp only [toLocation] at h1 h2
  simp only [toLocation, locShift, BSmtLibSpec.Lexer.Location.after, locAfter_offset',
    BSmtLibSpec.Lexer.Location.mk.injEq]
  rw [← h1, ← h2]
  exact ⟨trivial, rfl, rfl⟩

/-- The failure, moved. -/
def LexFailure.shift (base : Span.Location) (f : LexFailure) : LexFailure :=
  { f with
    span := Span.newUnchecked (locShift base f.span.start) (locShift base f.span.end)
    location := locShift base f.location }

/-- The token in progress, moved. -/
def Pending.shift (base : Span.Location) (p : Pending) : Pending :=
  { p with start := locShift base p.start }

/-- The lexeme, moved. -/
def Lexeme.shift (base : Span.Location) (l : Lexeme) : Lexeme :=
  { l with start := locShift base l.start, «end» := locShift base l.end }

/-- What `start` gives, moved. -/
def Started.shift (base : Span.Location) : Started → Started
  | .idle => .idle
  | .pending p => .pending ((Pending.shift base p))
  | .token l => .token ((Lexeme.shift base l))
  | .error f => .error ((LexFailure.shift base f))

/-- What `advance` gives, moved. -/
def Advanced.shift (base : Span.Location) : Advanced → Advanced
  | .pending p => .pending ((Pending.shift base p))
  | .idle => .idle
  | .tokenWith l => .tokenWith ((Lexeme.shift base l))
  | .tokenBefore l => .tokenBefore ((Lexeme.shift base l))
  | .error f => .error ((LexFailure.shift base f))

/-- What `finish` gives, moved. -/
def Finished.shift (base : Span.Location) : Finished → Finished
  | .none => .none
  | .token l => .token ((Lexeme.shift base l))
  | .error f => .error ((LexFailure.shift base f))

/-- The state, moved. -/
def St.shift (base : Span.Location) : St → St
  | .idle => .idle
  | .token p => .token ((Pending.shift base p))

theorem failAtByte_shift (kind : LexicalErrorKind) (base start location : Span.Location) :
    failAtByte kind (locShift base start) (locShift base location) =
      (LexFailure.shift base (failAtByte kind start location)) := by
  simp only [failAtByte, LexFailure.shift, locShift_afterColumn]
  rfl

theorem failAtEnd_shift (kind : LexicalErrorKind) (base start location : Span.Location) :
    failAtEnd kind (locShift base start) (locShift base location) =
      (LexFailure.shift base (failAtEnd kind start location)) := by
  simp only [failAtEnd, LexFailure.shift]
  rfl

theorem start_shift (version : Token.Version) (ws : Bool) (base location : Span.Location)
    (c : UInt8) :
    start version ws (locShift base location) c = (Started.shift base
        (start version ws location c)) := by
  unfold start
  dsimp only
  repeat' (split <;> rename_i h <;> (try simp only [h, ite_true, ite_false, Bool.false_eq_true]))
  all_goals first
    | rfl
    | simp only [Started.shift, Lexeme.shift, locShift_afterByte, failAtByte_shift]

theorem legacyStringByte_shift (base : Span.Location) (p : Pending) (location : Span.Location)
    (c : UInt8) :
    legacyStringByte ((Pending.shift base p)) (locShift base location) c =
      (Advanced.shift base (legacyStringByte p location c)) := by
  unfold legacyStringByte
  dsimp only [Pending.shift]
  repeat' (split <;> rename_i h <;> (try simp only [h, ite_true, ite_false, Bool.false_eq_true]))
  all_goals first
    | rfl
    | simp only [Advanced.shift, failAtByte_shift]

theorem legacyStringByte_shift' (base : Span.Location) (mode : Mode) (start : Span.Location)
    (content : ByteArray) (location : Span.Location) (c : UInt8) :
    legacyStringByte { mode, start := locShift base start, content } (locShift base location) c =
      (Advanced.shift base (legacyStringByte { mode, start, content } location c)) :=
  legacyStringByte_shift base { mode, start, content } location c

theorem advance_shift (ws : Bool) (base : Span.Location) (p : Pending) (location : Span.Location)
    (c : UInt8) :
    advance ws ((Pending.shift base p)) (locShift base location) c =
      (Advanced.shift base (advance ws p location c)) := by
  unfold advance
  dsimp only [Pending.shift]
  split
  all_goals
    repeat' (split <;> rename_i h <;> (try simp only [h, ite_true, ite_false, Bool.false_eq_true]))
  all_goals first
    | rfl
    | exact legacyStringByte_shift' base _ _ _ location c
    | simp only [Advanced.shift, Lexeme.shift, failAtByte_shift, locShift_afterByte]

theorem finish_shift (ws : Bool) (base : Span.Location) (p : Pending) (location : Span.Location) :
    finish ws ((Pending.shift base p)) (locShift base location) =
        (Finished.shift base (finish ws p location)) := by
  unfold finish
  dsimp only [Pending.shift]
  split
  all_goals
    repeat' (split <;> rename_i h <;> (try simp only [h, ite_true, ite_false, Bool.false_eq_true]))
  all_goals first
    | rfl
    | simp only [Finished.shift, Lexeme.shift, failAtEnd_shift]

/-- The outcome of a pure step, moved. -/
def shiftStep (base : Span.Location) : Option (St × List Lexeme) → Option (St × List Lexeme) :=
  Option.map fun (st, ls) => ((St.shift base st), ls.map (Lexeme.shift base))

theorem startStepW_shift (version : Token.Version) (ws : Bool) (base location : Span.Location)
    (c : UInt8) :
    startStepW version ws (locShift base location) c =
      shiftStep base (startStepW version ws location c) := by
  unfold startStepW
  rw [start_shift]
  cases start version ws location c <;> rfl

theorem byteStepW_shift (version : Token.Version) (ws : Bool) (base : Span.Location) (st : St)
    (location : Span.Location) (c : UInt8) :
    byteStepW version ws ((St.shift base st)) (locShift base location) c =
      shiftStep base (byteStepW version ws st location c) := by
  cases st with
  | idle => exact startStepW_shift version ws base location c
  | token p =>
    simp only [byteStepW, St.shift]
    rw [advance_shift]
    cases advance ws p location c with
    | tokenBefore l =>
      simp only [Advanced.shift, startStepW_shift, shiftStep]
      cases startStepW version ws location c <;> rfl
    | _ => rfl

theorem failedBeforeW_shift (ws : Bool) (base : Span.Location) (st : St) (location : Span.Location)
    (c : UInt8) :
    failedBeforeW ws ((St.shift base st)) (locShift base location) c =
      (failedBeforeW ws st location c).map (Lexeme.shift base) := by
  cases st with
  | idle => rfl
  | token p =>
    simp only [failedBeforeW, St.shift]
    rw [advance_shift]
    cases advance ws p location c <;> rfl

/-- The outcome of a pure run, moved. -/
def shiftRun (base : Span.Location) :
    Except (List Lexeme) (St × Span.Location × List Lexeme) →
      Except (List Lexeme) (St × Span.Location × List Lexeme)
  | .ok (st, location, ls) =>
    .ok ((St.shift base st), locShift base location, ls.map (Lexeme.shift base))
  | .error ls => .error (ls.map (Lexeme.shift base))

theorem shiftRun_withBefore (base : Span.Location) (ls : List Lexeme)
    (e : Except (List Lexeme) (St × Span.Location × List Lexeme)) :
    shiftRun base (withBefore ls e) =
      withBefore (ls.map (Lexeme.shift base)) (shiftRun base e) := by
  cases e with
  | ok r => obtain ⟨st, location, ls'⟩ := r; simp [withBefore, shiftRun]
  | error ls' => simp [withBefore, shiftRun]

theorem lexBytesW_shift (version : Token.Version) (ws : Bool) (base : Span.Location)
    (bytes : List UInt8) :
    ∀ (st : St) (location : Span.Location),
      lexBytesW version ws ((St.shift base st)) (locShift base location) bytes =
        shiftRun base (lexBytesW version ws st location bytes) := by
  induction bytes with
  | nil => intro st location; rfl
  | cons c bytes ih =>
    intro st location
    simp only [lexBytesW]
    rw [byteStepW_shift]
    cases byteStepW version ws st location c with
    | none => simp [shiftStep, shiftRun, failedBeforeW_shift]
    | some r =>
      obtain ⟨st', ls⟩ := r
      simp only [shiftStep, Option.map_some]
      rw [locShift_afterByte, ih, shiftRun_withBefore]

theorem endStepW_shift (ws : Bool) (base : Span.Location) (st : St) (location : Span.Location) :
    endStepW ws ((St.shift base st)) (locShift base location) =
      (endStepW ws st location).map (List.map (Lexeme.shift base)) := by
  cases st with
  | idle => rfl
  | token p =>
    simp only [endStepW, St.shift]
    rw [finish_shift]
    cases finish ws p location <;> rfl

end BSmtLib.Facts.Proofs.Lexer.Consumers.Pure

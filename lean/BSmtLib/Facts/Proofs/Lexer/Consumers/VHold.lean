module

public import BSmtLib.Facts.Proofs.Lexer.Consumers.VSession
import all BSmtLib.Lexer.Error
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Span
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor

@[expose] public section

/-!
# The run from a lexer state, and the naive lexer while it holds a result

The run from any state of the pure run (`streamFromSt`), how a byte steps it, and how it relates
for the two kinds of consumers (`streamFromSt_plain`) and to what the pure run hands over
(`fedRun`) from a boundary (`segment_stream`). While the naive lexer holds a result, the first
lexeme the run finishes is trailing input, and the end of the input returns the result (`hold`);
while it discards, it drops the bytes (`vBytes_discarding`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.VHold

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Layout BSmtLib.Facts.Proofs.Lexer.Consumers.Pure
open BSmtLib.Facts.Proofs.Lexer.Consumers.Stream BSmtLib.Facts.Proofs.Lexer.Consumers.VEnd
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSession BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps
open BSmtLib.Facts.Proofs.Lexer.VNaive.Facts BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Facts.Proofs.Lexer.VNaive.Streaming BSmtLib.Lexer.Error BSmtLib.Lexer.Internal.VNaive

/-- The run from the state at the location over the bytes, and then, if the input has ended,
the end of the input: the lexemes it finishes, and whether it fails. -/
def streamFromSt (version : Version) (ws ended : Bool) (st : St) (location : Span.Location)
    (bytes : List UInt8) : List Lexeme × Bool :=
  match lexBytesW version ws st location bytes with
  | .error ls => (ls, true)
  | .ok (st', location', ls) =>
    if ended then
      match endStepW ws st' location' with
      | some ls' => (ls ++ ls', false)
      | none => (ls, true)
    else (ls, false)

theorem streamFrom_eq (version : Version) (ws ended : Bool) (location : Span.Location)
    (bytes : List UInt8) :
    streamFrom version ws ended location bytes =
      streamFromSt version ws ended .idle location bytes :=
  rfl

theorem streamFromSt_nil (version : Version) (ws ended : Bool) (st : St)
    (location : Span.Location) :
    streamFromSt version ws ended st location [] =
      if ended then
        match endStepW ws st location with
        | some ls => (ls, false)
        | none => ([], true)
      else ([], false) := by
  simp only [streamFromSt, lexBytesW, List.nil_append]

theorem streamFromSt_cons_some {version : Version} {ws ended : Bool} {st st' : St}
    {location : Span.Location} {b : UInt8} {bytes : List UInt8} {ls : List Lexeme}
    (h : byteStepW version ws st location b = some (st', ls)) :
    streamFromSt version ws ended st location (b :: bytes) =
      (ls ++ (streamFromSt version ws ended st' (location.afterByte b) bytes).1,
        (streamFromSt version ws ended st' (location.afterByte b) bytes).2) := by
  simp only [streamFromSt, lexBytesW, h]
  cases lexBytesW version ws st' (location.afterByte b) bytes with
  | error ls' => rfl
  | ok r =>
    obtain ⟨st'', location', ls'⟩ := r
    simp only [withBefore]
    cases ended with
    | false => rfl
    | true =>
      simp only [ite_true]
      cases endStepW ws st'' location' <;> simp [List.append_assoc]

theorem streamFromSt_cons_none {version : Version} {ws ended : Bool} {st : St}
    {location : Span.Location} {b : UInt8} {bytes : List UInt8}
    (h : byteStepW version ws st location b = none) :
    streamFromSt version ws ended st location (b :: bytes) =
      (failedBeforeW ws st location b, true) := by
  simp only [streamFromSt, lexBytesW, h]

/-- A byte that ends the token in progress before it: the run hands the token over and goes on
with nothing in progress at the byte. -/
theorem streamFromSt_tokenBefore {version : Version} {ws ended : Bool} {p : Pending}
    {location : Span.Location} {b : UInt8} {bytes : List UInt8} {l : Lexeme}
    (hadv : advance ws p location b = .tokenBefore l) :
    streamFromSt version ws ended (.token p) location (b :: bytes) =
      (l :: (streamFromSt version ws ended .idle location (b :: bytes)).1,
        (streamFromSt version ws ended .idle location (b :: bytes)).2) := by
  cases hs : startStepW version ws location b with
  | none =>
    rw [streamFromSt_cons_none (st := .token p) (by simp [byteStepW, hadv, hs]),
      streamFromSt_cons_none (st := .idle) (by simp [byteStepW, hs])]
    simp [failedBeforeW, hadv]
  | some r =>
    obtain ⟨st', ls⟩ := r
    rw [streamFromSt_cons_some (st := .token p) (st' := st') (ls := l :: ls)
        (by simp [byteStepW, hadv, hs]),
      streamFromSt_cons_some (st := .idle) (st' := st') (ls := ls) (by simp [byteStepW, hs])]
    simp

/-! ## The errors of the pure step are not trailing input -/

theorem start_error_kind {version : Version} {ws : Bool} {location : Span.Location}
    {c : UInt8}
    {f : LexFailure} (h : start version ws location c = .error f) :
    (f.kind == .unexpectedTrailingToken) = false := by
  simp only [start] at h
  repeat' split at h
  all_goals cases h
  all_goals (simp only [failAtByte]; decide)

theorem advance_error_kind {ws : Bool} {p : Pending} {location : Span.Location} {c : UInt8}
    {f : LexFailure} (h : advance ws p location c = .error f) :
    (f.kind == .unexpectedTrailingToken) = false := by
  simp only [advance, legacyStringByte] at h
  repeat' split at h
  all_goals cases h
  all_goals first
    | (simp only [failAtByte]; decide)
    | (cases ‹Radix› <;> simp only [failAtByte, Radix.emptyError] <;> decide)

theorem finish_error_kind {ws : Bool} {p : Pending} {location : Span.Location} {f : LexFailure}
    (h : finish ws p location = .error f) :
    (f.kind == .unexpectedTrailingToken) = false := by
  simp only [finish] at h
  repeat' split at h
  all_goals cases h
  all_goals first
    | (simp only [failAtEnd]; decide)
    | (cases ‹Radix› <;> simp only [failAtEnd, Radix.emptyError] <;> decide)

theorem failureOf_lexical {ε : Type} {k : LexicalErrorKind} {span : Span}
    (h : (k == .unexpectedTrailingToken) = false) (continuesFrom : Option Span.Location) :
    failureOf (ε := ε) (LexerError.Internal.new (.lexical k) span continuesFrom) = .lexical := by
  simp [failureOf, h]

/-! ## The end of file -/

theorem lexemeHanded_eofAt (version : Version) (input : List UInt8) :
    lexemeHanded version (eofAt (locAfter input)) = some (BSmtLibSpec.Lexer.endOfFile input) :=
  lexemeHanded_eof version input

/-- The end-of-file lexeme at a location is handed over as the end-of-file token there. -/
theorem lexemeHanded_eofAt_location (version : Version) (location : Span.Location) :
    lexemeHanded version (eofAt location) =
      some (BSmtLibSpec.Lexer.endOfFileAt (toLocation location)) := by
  rw [lexemeHanded_eq]
  simp only [toTokenType, Option.map_some, lexemeReserved]
  rfl

/-! ## The run for a consumer that takes whitespace and comments, and the pure run -/

theorem handedOf_plainOf (version : Version) (ls : List Lexeme) :
    handedOf version (plainOf ls) = handedOf version ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    unfold handedOf plainOf at ih ⊢
    simp only [List.filter_cons]
    cases ht : (toTokenType l.category).isSome with
    | true => simp only [ite_true, List.filterMap_cons]; rw [ih]
    | false =>
      have hnone : lexemeHanded version l = none := by
        simp only [lexemeHanded]
        cases h : toTokenType l.category with
        | none => rfl
        | some _ => simp [h] at ht
      simp only [Bool.false_eq_true, ite_false, List.filterMap_cons, hnone]
      exact ih

theorem streamFromSt_plain (version : Version) (ended : Bool) {stW stP : St}
    (h : PlainOf stW stP)
    (location : Span.Location) (bytes : List UInt8) :
    (streamFromSt version true ended stW location bytes).2 =
        (streamFromSt version false ended stP location bytes).2 ∧
      handedOf version (streamFromSt version true ended stW location bytes).1 =
        handedOf version (streamFromSt version false ended stP location bytes).1 := by
  have hr := lexBytes_plain version bytes location h
  unfold streamFromSt
  revert hr
  cases lexBytesW version true stW location bytes with
  | error lsW =>
    cases lexBytesW version false stP location bytes with
    | ok _ => intro hr; exact hr.elim
    | error lsP =>
      intro hr
      exact ⟨rfl, by rw [← hr, handedOf_plainOf]⟩
  | ok x =>
    obtain ⟨stW', locW, lsW⟩ := x
    cases lexBytesW version false stP location bytes with
    | error _ => intro hr; exact hr.elim
    | ok y =>
      obtain ⟨stP', locP, lsP⟩ := y
      rintro ⟨h1, rfl, h3⟩
      cases ended with
      | false =>
        exact ⟨rfl, by simp only [Bool.false_eq_true, ite_false]; rw [← h3, handedOf_plainOf]⟩
      | true =>
        have he := endStep_plain h1 locW
        simp only [ite_true]
        revert he
        cases endStepW true stW' locW with
        | none =>
          cases endStepW false stP' locW with
          | none => intro _; exact ⟨rfl, by rw [← h3, handedOf_plainOf]⟩
          | some _ => intro he; exact he.elim
        | some lsW' =>
          cases endStepW false stP' locW with
          | none => intro he; exact he.elim
          | some lsP' =>
            intro he
            refine ⟨rfl, ?_⟩
            dsimp only
            rw [← h3, ← he, ← plainOf_append, handedOf_plainOf]

/-- What the pure run hands over (`fedRun`) from the offset `o` on, read on its own and
located in the whole input, is the tokens of the run from the boundary at `o`, for a consumer
of either kind. -/
theorem segment_stream (version : Version) (ws : Bool) (input : List UInt8) (ended : Bool)
    (o : Nat) :
    BSmtLibSpec.Lexer.segment fedRun (fromVersion version) input ended o =
      { handed := handedOf version (stream version ws input ended o).1
        failed := (stream version ws input ended o).2 } := by
  rw [segment_fedRun, toVersion_fromVersion]
  cases ws with
  | false => rfl
  | true =>
    obtain ⟨h1, h2⟩ := streamFromSt_plain version ended (stW := .idle) (stP := .idle) trivial
      (locAfter (input.take o)) (input.drop o)
    simp only [stream, streamFrom_eq]
    rw [h1, h2]

section
variable (consumer : BSmtLibSpec.Lexer.Consumer)

/-- A lexer that discards drops the bytes, and its location stays. -/
theorem vBytes_discarding {s : Span.Location} (bytes : List UInt8) :
    ∀ (core : Core) (held : Option (Span.Located consumer.Result)) (taken : List Handed),
      core.activity = .discarding s →
      ∃ core', vBytes consumer core held bytes taken = ((.ok held, core'), taken) ∧
        core'.version = core.version ∧ core'.activity = .discarding s ∧
        core'.location = core.location ∧ core'.holding = core.holding ∧
        core'.initialVersion = core.initialVersion := by
  induction bytes with
  | nil => intro core held taken ha; exact ⟨core, rfl, rfl, ha, rfl, rfl, rfl⟩
  | cons b bytes ih =>
    intro core held taken ha
    obtain ⟨core1, h1, hv1, ha1, hl1, hh1, hi1⟩ := lexByte_discarding consumer core b taken ha
    obtain ⟨core', h', hv', ha', hl', hh', hi'⟩ := ih core1 held taken ha1
    refine ⟨core', ?_, hv'.trans hv1, ha', ?_, hh'.trans hh1, hi'.trans hi1⟩
    · simp only [vBytes, h1]; exact h'
    · rw [hl', hl1]


/-- Whether a token is in progress. -/
def St.weight : St → Nat
  | .idle => 0
  | .token _ => 1

/-- The session of a lexer that holds the result `held` with the tokens `taken`, as the first
lexeme of the run after it decides: trailing input at its start, or the end of the input, which
returns the result; with no lexeme, a lexical error if the run fails, and otherwise the result
held. -/
def holdSession (start : BSmtLibSpec.Lexicon.Version) (version : Version)
    (taken : List Handed)
    (held : Span.Located consumer.Result) :
    List Lexeme × Bool → BSmtLibSpec.Lexer.Session consumer.Result consumer.Error
  | (l :: _, _) =>
    if l.category == .endOfFile then
      ⟨taken, .finished held.value (toLocation held.location), start, none⟩
    else
      ⟨taken, .failed (.trailing (toLocation l.start)), fromVersion version, none⟩
  | ([], true) => ⟨taken, .failed .lexical, fromVersion version, none⟩
  | ([], false) =>
    ⟨taken, .holding held.value (toLocation held.location), fromVersion version, none⟩

theorem trailing_failureOf (l : Lexeme) (continuesFrom : Option Span.Location) :
    failureOf (ε := consumer.Error)
        (LexerError.Internal.new (.lexical .unexpectedTrailingToken) (trailingSpan l) continuesFrom) =
      .trailing (toLocation l.start) := by
  simp only [failureOf, trailingSpan]
  rfl


theorem drop_succ_of {input bytes : List UInt8} {j : Nat} {b : UInt8}
    (h : input.drop j = b :: bytes) :
    input.drop (j + 1) = bytes ∧
      locAfter (input.take (j + 1)) = (locAfter (input.take j)).afterByte b := by
  have hb : input[j]? = some b := by
    have := congrArg (·[0]?) h
    simpa [List.getElem?_drop] using this
  refine ⟨?_, ?_⟩
  · rw [← List.drop_drop, h]; rfl
  · rw [List.take_add_one, hb]
    simp only [Option.toList_some]
    exact locAfter_concat _ b

theorem drop_length_eq_nil {input : List UInt8} {j : Nat} (h : input.drop j = []) :
    locAfter (input.take j) = locAfter input := by
  rw [List.drop_eq_nil_iff] at h
  rw [List.take_of_length_le h]

section
variable (consumer : BSmtLibSpec.Lexer.Consumer) (sv : BSmtLibSpec.Lexicon.Version)
    (input : List UInt8)
  (ended : Bool)

theorem finish_token_ne_eof {ws : Bool} {p : Pending} {location : Span.Location} {l : Lexeme}
    (h : finish ws p location = .token l) : (l.category == .endOfFile) = false := by
  simp only [finish] at h
  repeat' split at h
  all_goals cases h
  all_goals first | rfl | (cases ‹Radix› <;> rfl)

theorem discardedOf_of_activity {core : Core} {st : St} (h : core.activity = st.activity) :
    discardedOf core = none := by
  cases st <;> simp [discardedOf, h, St.activity]

theorem reset_version (core : Core) (sv : BSmtLibSpec.Lexicon.Version)
    (hi : core.initialVersion = toVersion sv) : fromVersion core.reset.version = sv := by
  simp [Core.reset, Core.initial, hi, fromVersion_toVersion]

theorem discardedOf_reset (core : Core) : discardedOf core.reset = none := (rfl)

/-- While a result is held, the end of the input returns it, unless the token in progress is
trailing input or fails. -/
theorem hold_nil (v : Version) (x : Span.Located consumer.Result) (st : St) (j : Nat)
    (core : Core)
    (taken : List Handed) (hv : core.version = v)
    (ha : core.activity = st.activity) (hl : core.location = locAfter (input.take j))
    (hh : core.holding = true) (hi : core.initialVersion = toVersion sv) :
    vSession consumer core (some x) [] ended taken =
      holdSession consumer sv v taken x
        (streamFromSt v consumer.concrete ended st (locAfter (input.take j)) []) := by
  rw [streamFromSt_nil]
  unfold vSession
  simp only [vBytes]
  cases ended with
  | false =>
    simp only [Bool.false_eq_true, ite_false, holdSession, sessionOf, hv,
      discardedOf_of_activity ha, Option.map_none]
  | true =>
    simp only [ite_true]
    cases st with
    | idle =>
      rw [vEnd_held consumer core taken (.inl ha) hh]
      simp only [endStepW, eofResult, holdSession, eofLexeme, sessionOf,
        reset_version core sv hi, discardedOf_reset, Option.map_none]
      rfl
    | token p =>
      cases hf : finish consumer.concrete p core.location with
      | none =>
        rw [(vEnd_finish_none consumer core taken ha hf).1 hh]
        simp only [endStepW, ← hl, hf, eofResult, holdSession, eofLexeme, sessionOf,
          reset_version (idleAt core) sv hi, discardedOf_reset, Option.map_none]
        rfl
      | token l =>
        obtain ⟨hlv, h1, -, -⟩ := vEnd_finish_token consumer core taken ha hf
        rw [h1 (handOverAt_holding consumer (idleAt core) l hlv hh taken)]
        simp only [endStepW, ← hl, hf, holdSession, finish_token_ne_eof hf, Bool.false_eq_true,
          ite_false, sessionOf, trailing_failureOf]
        simp [idleAt, hv, discardedOf]
      | error f =>
        rw [vEnd_finish_error consumer core taken ha hf]
        simp only [endStepW, ← hl, hf, holdSession, sessionOf, hv,
          failureOf_lexical (finish_error_kind hf), discardedOf_of_activity ha, Option.map_none]


theorem start_token_ne_eof {version : Version} {ws : Bool} {location : Span.Location}
    {c : UInt8}
    {l : Lexeme} (h : start version ws location c = .token l) :
    (l.category == .endOfFile) = false := by
  simp only [start] at h
  repeat' split at h
  all_goals cases h
  all_goals rfl

theorem advance_lexeme_ne_eof {ws : Bool} {p : Pending} {location : Span.Location} {c : UInt8}
    {l : Lexeme}
    (h : advance ws p location c = .tokenWith l ∨ advance ws p location c = .tokenBefore l) :
    (l.category == .endOfFile) = false := by
  rcases h with h | h
  all_goals
    simp only [advance, legacyStringByte] at h
    repeat' split at h
    all_goals cases h
    all_goals first | rfl | (cases ‹Radix› <;> rfl)

theorem lexStart_error' (consumer : BSmtLibSpec.Lexer.Consumer) (core : Core) (c : UInt8)
    (taken : List Handed) {f : LexFailure}
    (hs : start core.version consumer.concrete core.location c = .error f) :
    vRun consumer (lexStart (H := Answering consumer) core c) taken =
      ((.error ⟨.lexical f.kind, f.span, f.location⟩, core), taken) := by
  have hf : startS core.version consumer.concrete core.location c = ⟨.error f, trivial⟩ :=
    Subtype.ext hs
  simp only [lexStart, isConcrete_answering, hf]
  rfl

theorem vSession_step_none {core core' : Core} {b : UInt8} {taken taken' : List Handed}
    (held : Option (Span.Located consumer.Result)) (bs : List UInt8) (ended : Bool)
    (h : vByte consumer core b taken = ((.ok none, core'), taken')) :
    vSession consumer core held (b :: bs) ended taken =
      vSession consumer core' held bs ended taken' := by
  unfold vSession
  simp only [vBytes, h]

theorem vSession_step_some {core core' : Core} {b : UInt8} {taken taken' : List Handed}
    {located : Span.Located consumer.Result}
    (held : Option (Span.Located consumer.Result)) (bs : List UInt8) (ended : Bool)
    (h : vByte consumer core b taken = ((.ok (some located), core'), taken')) :
    vSession consumer core held (b :: bs) ended taken =
      vSession consumer core' (some located) bs ended taken' := by
  unfold vSession
  simp only [vBytes, h]

theorem vSession_step_error {core core' : Core} {b : UInt8} {taken taken' : List Handed}
    {f : Failure (Option consumer.Error)}
    (held : Option (Span.Located consumer.Result)) (bs : List UInt8) (ended : Bool)
    (h : vByte consumer core b taken = ((.error f, core'), taken')) :
    vSession consumer core held (b :: bs) ended taken =
      sessionOf consumer taken' (.failed (failureOf (LexerError.Internal.new f.cause f.span none)))
        core' := by
  unfold vSession
  simp only [vBytes, h]

/-- While a result is held, the first lexeme the lexer finishes is trailing input, and the end of
the input returns the result. -/
theorem hold (v : Version) (x : Span.Located consumer.Result) : ∀ (n : Nat)
    (bytes : List UInt8)
    (st : St), 2 * bytes.length + (St.weight st) ≤ n → ∀ (j : Nat) (core : Core)
    (taken : List Handed),
    input.drop j = bytes → core.version = v → core.activity = st.activity →
    core.location = locAfter (input.take j) → core.holding = true →
    core.initialVersion = toVersion sv →
    vSession consumer core (some x) bytes ended taken =
      holdSession consumer sv v taken x
        (streamFromSt v consumer.concrete ended st (locAfter (input.take j)) bytes) := by
  intro n
  induction n with
  | zero =>
    intro bytes st hn j core taken hj hv ha hl hh hi
    have hb : bytes = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hb
    exact hold_nil consumer sv input ended v x st j core taken hv ha hl hh hi
  | succ n ih =>
    intro bytes st hn j core taken hj hv ha hl hh hi
    cases bytes with
    | nil => exact hold_nil consumer sv input ended v x st j core taken hv ha hl hh hi
    | cons b bs =>
      obtain ⟨hj', hl'⟩ := drop_succ_of hj
      have hvs : core.version = v := hv
      -- a quiet step and the rest
      have quiet : ∀ {core' : Core} {st' : St}, vByte consumer core b taken =
          ((.ok none, core'), taken) → core'.version = core.version →
          core'.activity = st'.activity → core'.location = core.location.afterByte b →
          core'.holding = core.holding → core'.initialVersion = core.initialVersion →
          (St.weight st') ≤ 1 →
          byteStepW v consumer.concrete st (locAfter (input.take j)) b = some (st', []) →
          vSession consumer core (some x) (b :: bs) ended taken =
            holdSession consumer sv v taken x
              (streamFromSt v consumer.concrete ended st (locAfter (input.take j)) (b :: bs)) := by
        intro core' st' h hv' ha' hl'' hh' hi' hw hs
        rw [vSession_step_none consumer _ bs ended h,
          ih bs st' (by simp at hn ⊢; omega) (j + 1) core' taken hj' (hv'.trans hv) ha'
            (by rw [hl'', hl, hl']) (hh'.trans hh) (hi'.trans hi),
          streamFromSt_cons_some hs, hl']
        rfl
      -- trailing input at the lexeme
      have trailing : ∀ {core' : Core} (l : Lexeme) (ls : List Lexeme) (st' : St),
          vByte consumer core b taken =
            ((.error ⟨.lexical .unexpectedTrailingToken, trailingSpan l, l.start⟩, core'), taken) →
          core'.version = v → discardedOf core' = none → (l.category == .endOfFile) = false →
          (streamFromSt v consumer.concrete ended st (locAfter (input.take j)) (b :: bs)).1 =
            l :: ls →
          vSession consumer core (some x) (b :: bs) ended taken =
            holdSession consumer sv v taken x
              (streamFromSt v consumer.concrete ended st (locAfter (input.take j)) (b :: bs)) := by
        intro core' l ls st' h hv' hd he hs
        rw [vSession_step_error consumer _ bs ended h]
        generalize streamFromSt v consumer.concrete ended st (locAfter (input.take j)) (b :: bs) = S
          at hs
        obtain ⟨L, fl⟩ := S
        simp only at hs
        subst hs
        simp only [holdSession, he, Bool.false_eq_true, ite_false, sessionOf, hv', hd,
          Option.map_none, trailing_failureOf]
      -- a lexical error of the pure step
      have lexical : ∀ {core' : Core} (k : LexicalErrorKind) (span : Span) (loc : Span.Location),
          vByte consumer core b taken = ((.error ⟨.lexical k, span, loc⟩, core'), taken) →
          (k == .unexpectedTrailingToken) = false →
          core'.version = v → discardedOf core' = none →
          streamFromSt v consumer.concrete ended st (locAfter (input.take j)) (b :: bs) =
            ([], true) →
          vSession consumer core (some x) (b :: bs) ended taken =
            holdSession consumer sv v taken x
              (streamFromSt v consumer.concrete ended st (locAfter (input.take j)) (b :: bs)) := by
        intro core' k span loc h hk hv' hd hs
        rw [vSession_step_error consumer _ bs ended h, hs]
        simp only [holdSession, sessionOf, hv', hd, Option.map_none, failureOf_lexical hk]
      have hloc : locAfter (input.take j) = core.location := hl.symm
      cases st with
      | idle =>
        rw [hloc, ← hvs]
        rw [hloc, ← hvs] at quiet trailing lexical
        cases hs : start core.version consumer.concrete core.location b with
        | idle =>
          obtain ⟨core', h, hv', ha', hl'', hh', hi'⟩ :=
            lexStart_none consumer core b taken (st := .idle) (by simp [startStepW, hs])
          rw [← lexByte_idle consumer core b taken ha] at h
          exact quiet h hv' ha' hl'' hh' hi' (by simp [St.weight])
            (by simp [byteStepW, startStepW, hs])
        | pending p =>
          obtain ⟨core', h, hv', ha', hl'', hh', hi'⟩ :=
            lexStart_none consumer core b taken (st := .token p) (by simp [startStepW, hs])
          rw [← lexByte_idle consumer core b taken ha] at h
          exact quiet h hv' ha' hl'' hh' hi' (by simp [St.weight])
            (by simp [byteStepW, startStepW, hs])
        | token l =>
          obtain ⟨hlv, h⟩ := lexStart_token consumer core b taken hs
          rw [handOverAt_holding consumer (idleAfter core b) l hlv (by simpa [idleAfter] using hh),
            ← lexByte_idle consumer core b taken ha] at h
          refine trailing l (streamFromSt core.version consumer.concrete ended .idle
            (core.location.afterByte b) bs).1 .idle h (by simp [idleAfter, hv])
            (by simp [discardedOf, idleAfter])
            (start_token_ne_eof hs) ?_
          rw [streamFromSt_cons_some (st' := .idle) (ls := [l])
            (by simp [byteStepW, startStepW, hs])]
          rfl
        | error f =>
          have h := lexStart_error' consumer core b taken hs
          rw [← lexByte_idle consumer core b taken ha] at h
          refine lexical f.kind f.span f.location h (start_error_kind hs) rfl
            (discardedOf_of_activity (st := .idle) ha) ?_
          rw [streamFromSt_cons_none (by simp [byteStepW, startStepW, hs])]
          rfl
      | token p =>
        rw [hloc, ← hvs]
        rw [hloc, ← hvs] at quiet trailing lexical
        cases hadv : advance consumer.concrete p core.location b with
        | pending p' =>
          obtain ⟨core', h, hv', ha', hl'', hh', hi'⟩ :=
            lexByte_pending consumer core b taken ha hadv
          exact quiet (st' := .token p') h hv' ha' hl'' hh' hi' (by simp [St.weight])
            (by simp [byteStepW, hadv])
        | idle =>
          obtain ⟨core', h, hv', ha', hl'', hh', hi'⟩ :=
            lexByte_advance_idle consumer core b taken ha hadv
          exact quiet (st' := .idle) h hv' ha' hl'' hh' hi' (by simp [St.weight])
            (by simp [byteStepW, hadv])
        | tokenWith l =>
          obtain ⟨hlv, h⟩ := lexByte_tokenWith consumer core b taken ha hadv
          rw [handOverAt_holding consumer (idleAfter core b) l hlv
            (by simpa [idleAfter] using hh)] at h
          refine trailing l (streamFromSt core.version consumer.concrete ended .idle
            (core.location.afterByte b) bs).1 .idle h (by simp [idleAfter, hv])
            (by simp [discardedOf, idleAfter])
            (advance_lexeme_ne_eof (.inl hadv)) ?_
          rw [streamFromSt_cons_some (st' := .idle) (ls := [l]) (by simp [byteStepW, hadv])]
          rfl
        | tokenBefore l =>
          obtain ⟨hlv, h⟩ := lexByte_tokenBefore consumer core b taken ha hadv
          have h' := h (handOverAt_holding consumer (idleAt core) l hlv
            (by simpa [idleAt] using hh) taken)
          refine trailing l (streamFromSt core.version consumer.concrete ended .idle
            core.location (b :: bs)).1 .idle h' (by simp [idleAt, hv])
            (by simp [discardedOf, idleAt])
            (advance_lexeme_ne_eof (.inr hadv)) ?_
          rw [streamFromSt_tokenBefore hadv]
        | error f =>
          have h := lexByte_advance_error consumer core b taken ha hadv
          refine lexical f.kind f.span f.location h (advance_error_kind hadv) rfl
            (discardedOf_of_activity (st := .token p) ha) ?_
          rw [streamFromSt_cons_none (by simp [byteStepW, hadv])]
          simp [failedBeforeW, hadv]

end

end

end BSmtLib.Facts.Proofs.Lexer.Consumers.VHold

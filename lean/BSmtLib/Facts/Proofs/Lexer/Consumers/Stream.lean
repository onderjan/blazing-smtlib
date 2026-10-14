module

public import BSmtLib.Facts.Proofs.Lexer.Consumers.Layout

@[expose] public section

/-!
# The run from a boundary

The naive lexer's pure run from nothing in progress at a location, over bytes, and then, if the
input has ended, the end of the input (`streamFrom`), and the run from the boundary at an offset
of the input (`stream`). Of it:

- the lexemes the first byte finishes, and where they end (`byteStepW_cases`);
- after a lexeme other than the end of file, the run goes on as the run from nothing in progress
  at the end of the lexeme (`lexBytesW_restart`, `streamFrom_restart`);
- what the pure run hands over (`fedRun`) from an offset on, read on its own and located in the
  whole input (`BSmtLibSpec.Lexer.segment`), is the tokens of the run from the boundary at the
  offset (`segment_fedRun`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.Stream

open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.Consumers.Pure.Lexeme
open BSmtLib.Facts.Proofs.Lexer.VNaive.Facts BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix
open BSmtLib.Facts.Proofs.Lexer.VNaive.Prefix.Lexeme BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Lexer.Internal.VNaive

theorem startStepW_cases {version : Token.Version} {ws : Bool} {location : Span.Location}
    {c : UInt8}
    {st : St} {ls : List Lexeme} (h : startStepW version ws location c = some (st, ls)) :
    ls = [] ∨ ∃ l, ls = [l] ∧ st = .idle ∧ l.end = location.afterByte c := by
  simp only [startStepW] at h
  split at h
  · cases h; exact .inl rfl
  · cases h; exact .inl rfl
  · cases h
    exact .inr ⟨_, rfl, rfl, (start_token_span ‹_›).2⟩
  · cases h

theorem byteStepW_cases {version : Token.Version} {ws : Bool} {st st' : St}
    {location : Span.Location}
    {c : UInt8} {ls : List Lexeme} (h : byteStepW version ws st location c = some (st', ls)) :
    ls = [] ∨ (∃ l, ls = [l] ∧ st' = .idle ∧ l.end = location.afterByte c) ∨
      (∃ l ls', ls = l :: ls' ∧ l.end = location ∧
        startStepW version ws location c = some (st', ls')) := by
  cases st with
  | idle =>
    rcases startStepW_cases h with h | h
    · exact .inl h
    · exact .inr (.inl h)
  | token p =>
    simp only [byteStepW] at h
    split at h
    · cases h; exact .inl rfl
    · cases h; exact .inl rfl
    · cases h
      exact .inr (.inl ⟨_, rfl, rfl, (advance_tokenWith ‹_›).2⟩)
    · obtain ⟨⟨st'', ls''⟩, hs, he⟩ := Option.map_eq_some_iff.mp h
      cases he
      exact .inr (.inr ⟨_, _, rfl, (advance_tokenBefore ‹_›).2, hs⟩)
    · cases h

theorem failedBeforeW_cases {version : Token.Version} {ws : Bool} {st : St}
    {location : Span.Location}
    {c : UInt8} (h : byteStepW version ws st location c = none) :
    failedBeforeW ws st location c = [] ∨
      ∃ l, failedBeforeW ws st location c = [l] ∧ l.end = location ∧
        startStepW version ws location c = none := by
  cases st with
  | idle => exact .inl rfl
  | token p =>
    simp only [failedBeforeW]
    split
    · rename_i l hadv
      simp only [byteStepW, hadv, Option.map_eq_none_iff] at h
      exact .inr ⟨l, rfl, (advance_tokenBefore hadv).2, h⟩
    · exact .inl rfl

/-- After a lexeme other than the end of file, the run goes on as a run from nothing in progress
at the end of the lexeme, over the bytes after it. -/
theorem lexBytesW_restart (version : Token.Version) (ws : Bool) (bytes : List UInt8) :
    ∀ {st : St} {location : Span.Location} {pre post : List Lexeme} {l : Lexeme},
      (∀ {st' location'}, lexBytesW version ws st location bytes =
          .ok (st', location', pre ++ l :: post) →
        ∃ k ≤ bytes.length, l.end = advanceLoc location (bytes.take k) ∧
          lexBytesW version ws .idle l.end (bytes.drop k) = .ok (st', location', post)) ∧
      (lexBytesW version ws st location bytes = .error (pre ++ l :: post) →
        ∃ k ≤ bytes.length, l.end = advanceLoc location (bytes.take k) ∧
          lexBytesW version ws .idle l.end (bytes.drop k) = .error post) := by
  induction bytes with
  | nil =>
    intro st location pre post l
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [lexBytesW, Except.ok.injEq, Prod.mk.injEq] at h
      exact absurd h.2.2 (by simp)
    · simp [lexBytesW] at h
  | cons c bytes ih =>
    intro st location pre post l
    -- where the lexeme is among those of the first byte
    have first : ∀ {st1 : St} {ls1 mid : List Lexeme},
        byteStepW version ws st location c = some (st1, ls1) → ls1 = pre ++ l :: mid →
        ∃ k ≤ (c :: bytes).length, l.end = advanceLoc location ((c :: bytes).take k) ∧
          ∀ r, lexBytesW version ws st1 (location.afterByte c) bytes = r →
            lexBytesW version ws .idle l.end ((c :: bytes).drop k) = withBefore mid r := by
      intro st1 ls1 mid hb hls
      rcases byteStepW_cases hb with h0 | ⟨l1, h1, hst, he⟩ | ⟨l1, ls', h1, he, hs⟩
      · simp [h0] at hls
      · subst h1 hst
        obtain ⟨rfl, rfl, rfl⟩ : pre = [] ∧ l1 = l ∧ mid = [] := by
          cases pre with
          | nil => simp_all
          | cons a pre => simp at hls
        refine ⟨1, by simp, by simp [advanceLoc, he], fun r hr => ?_⟩
        simp only [List.drop_succ_cons, List.drop_zero, ← hr, withBefore_nil, he]
      · subst h1
        cases pre with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at hls
          obtain ⟨rfl, rfl⟩ := hls
          refine ⟨0, by simp, by simp [advanceLoc, he], fun r hr => ?_⟩
          simp only [List.drop_zero, lexBytesW, byteStepW, he, hs, hr]
        | cons a pre =>
          simp only [List.cons_append, List.cons.injEq] at hls
          obtain ⟨rfl, hls⟩ := hls
          rcases startStepW_cases hs with h0 | ⟨p, hp, hst, hpe⟩
          · subst h0; simp at hls
          · subst hp hst
            obtain ⟨rfl, rfl, rfl⟩ : pre = [] ∧ p = l ∧ mid = [] := by
              cases pre with
              | nil => simp_all
              | cons b pre => simp at hls
            refine ⟨1, by simp, by simp [advanceLoc, hpe], fun r hr => ?_⟩
            simp only [List.drop_succ_cons, List.drop_zero, ← hr, withBefore_nil, hpe]
    simp only [lexBytesW]
    cases hb : byteStepW version ws st location c with
    | none =>
      refine ⟨fun h => by simp at h, fun h => ?_⟩
      simp only [Except.error.injEq] at h
      rcases failedBeforeW_cases hb with h0 | ⟨l0, h0, he, hs⟩
      · rw [h0] at h; simp at h
      · rw [h0] at h
        obtain ⟨rfl, rfl, rfl⟩ : pre = [] ∧ l0 = l ∧ post = [] := by
          cases pre with
          | nil => simp_all
          | cons a pre => simp at h
        refine ⟨0, by simp, by simp [advanceLoc, he], ?_⟩
        simp [lexBytesW, byteStepW, he, hs, failedBeforeW]
    | some r =>
      obtain ⟨st1, ls1⟩ := r
      dsimp only
      constructor
      · intro st' location' h
        cases hr : lexBytesW version ws st1 (location.afterByte c) bytes with
        | error _ => rw [hr] at h; simp [withBefore] at h
        | ok r =>
          obtain ⟨st2, loc2, ls2⟩ := r
          rw [hr] at h
          simp only [withBefore, Except.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, h⟩ := h
          rcases List.append_eq_append_iff.mp h with ⟨a', hpre, hls2⟩ | ⟨c', hls1, hpost⟩
          · obtain ⟨k, hk, he, hrun⟩ := (ih (pre := a') (post := post) (l := l)).1 (hls2 ▸ hr)
            refine ⟨k + 1, by simp; omega, by simp [advanceLoc, he], ?_⟩
            simpa using hrun
          · cases c' with
            | nil =>
              simp only [List.append_nil, List.nil_append] at hls1 hpost
              obtain ⟨k, hk, he, hrun⟩ :=
                (ih (pre := []) (post := post) (l := l)).1 (by rw [hr, ← hpost]; rfl)
              refine ⟨k + 1, by simp; omega, by simp [advanceLoc, he], ?_⟩
              simpa using hrun
            | cons x c'' =>
              simp only [List.cons_append, List.cons.injEq] at hpost
              obtain ⟨rfl, rfl⟩ := hpost
              obtain ⟨k, hk, he, hrun⟩ := first hb hls1
              exact ⟨k, hk, he, by rw [hrun _ hr]; rfl⟩
      · intro h
        cases hr : lexBytesW version ws st1 (location.afterByte c) bytes with
        | ok _ => rw [hr] at h; simp [withBefore] at h
        | error ls2 =>
          rw [hr] at h
          simp only [withBefore, Except.error.injEq] at h
          rcases List.append_eq_append_iff.mp h with ⟨a', hpre, hls2⟩ | ⟨c', hls1, hpost⟩
          · obtain ⟨k, hk, he, hrun⟩ := (ih (pre := a') (post := post) (l := l)).2 (hls2 ▸ hr)
            refine ⟨k + 1, by simp; omega, by simp [advanceLoc, he], ?_⟩
            simpa using hrun
          · cases c' with
            | nil =>
              simp only [List.append_nil, List.nil_append] at hls1 hpost
              obtain ⟨k, hk, he, hrun⟩ :=
                (ih (pre := []) (post := post) (l := l)).2 (by rw [hr, ← hpost]; rfl)
              refine ⟨k + 1, by simp; omega, by simp [advanceLoc, he], ?_⟩
              simpa using hrun
            | cons x c'' =>
              simp only [List.cons_append, List.cons.injEq] at hpost
              obtain ⟨rfl, rfl⟩ := hpost
              obtain ⟨k, hk, he, hrun⟩ := first hb hls1
              exact ⟨k, hk, he, by rw [hrun _ hr]; rfl⟩

theorem lexBytesW_location {version : Token.Version} {ws : Bool} (bytes : List UInt8) :
    ∀ {st st' : St} {location location' : Span.Location} {ls : List Lexeme},
      lexBytesW version ws st location bytes = .ok (st', location', ls) →
        location' = advanceLoc location bytes := by
  induction bytes with
  | nil =>
    intro st st' location location' ls h
    simp only [lexBytesW, Except.ok.injEq, Prod.mk.injEq] at h
    exact h.2.1.symm
  | cons c bytes ih =>
    intro st st' location location' ls h
    simp only [lexBytesW] at h
    split at h
    · cases h
    · rename_i st1 ls1 _
      cases hr : lexBytesW version ws st1 (location.afterByte c) bytes with
      | error _ => rw [hr] at h; simp [withBefore] at h
      | ok r =>
        obtain ⟨st2, loc2, ls2⟩ := r
        rw [hr] at h
        simp only [withBefore, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact ih hr

/-- The run from nothing in progress at the location over the bytes, and then, if the input has
ended, the end of the input: the lexemes it finishes, and whether it fails. -/
def streamFrom (version : Token.Version) (ws ended : Bool) (location : Span.Location)
    (bytes : List UInt8) :
    List Lexeme × Bool :=
  match lexBytesW version ws .idle location bytes with
  | .error ls => (ls, true)
  | .ok (st, location', ls) =>
    if ended then
      match endStepW ws st location' with
      | some ls' => (ls ++ ls', false)
      | none => (ls, true)
    else (ls, false)

theorem endStepW_cases {ws : Bool} {st : St} {location : Span.Location} {ls : List Lexeme}
    (h : endStepW ws st location = some ls) :
    ls = [eofLexeme location] ∨ ∃ l, ls = [l, eofLexeme location] ∧ l.end = location := by
  cases st with
  | idle => simp only [endStepW, Option.some.injEq] at h; exact .inl h.symm
  | token p =>
    simp only [endStepW] at h
    split at h
    · cases h; exact .inl rfl
    · cases h; exact .inr ⟨_, rfl, (finish_token ‹_›).2⟩
    · cases h

/-- After a lexeme other than the end of file, the run goes on as a run from nothing in progress
at the end of the lexeme, over the bytes after it. -/
theorem streamFrom_restart {version : Token.Version} {ws ended : Bool} {location : Span.Location}
    {bytes : List UInt8} {pre post : List Lexeme} {l : Lexeme}
    (h : (streamFrom version ws ended location bytes).1 = pre ++ l :: post)
    (hl : l.category ≠ .endOfFile) :
    ∃ k ≤ bytes.length, l.end = advanceLoc location (bytes.take k) ∧
      streamFrom version ws ended l.end (bytes.drop k) =
        (post, (streamFrom version ws ended location bytes).2) := by
  unfold streamFrom at h ⊢
  cases hr : lexBytesW version ws .idle location bytes with
  | error ls =>
    rw [hr] at h
    obtain ⟨k, hk, he, hrun⟩ := (lexBytesW_restart version ws bytes).2 (hr.trans (congrArg _ h))
    exact ⟨k, hk, he, by rw [hrun]⟩
  | ok r =>
    obtain ⟨st, loc', ls⟩ := r
    rw [hr] at h
    dsimp only at h ⊢
    cases ended with
    | false =>
      simp only [Bool.false_eq_true, ite_false] at h ⊢
      obtain ⟨k, hk, he, hrun⟩ := (lexBytesW_restart version ws bytes).1 (hr.trans (by rw [h]))
      exact ⟨k, hk, he, by rw [hrun]⟩
    | true =>
      simp only [ite_true] at h ⊢
      cases hend : endStepW ws st loc' with
      | none =>
        rw [hend] at h
        dsimp only at h
        obtain ⟨k, hk, he, hrun⟩ := (lexBytesW_restart version ws bytes).1 (hr.trans (by rw [h]))
        exact ⟨k, hk, he, by rw [hrun]; simp [hend]⟩
      | some ls' =>
        rw [hend] at h
        dsimp only at h
        rcases List.append_eq_append_iff.mp h with ⟨a', hpre, hls'⟩ | ⟨c', hls, hpost⟩
        · -- the lexeme is one the end of the input finishes
          rcases endStepW_cases hend with h1 | ⟨t, h1, hte⟩
          · rw [h1] at hls'
            cases a' with
            | nil =>
              simp only [List.nil_append, List.cons.injEq] at hls'
              exact absurd (hls'.1 ▸ rfl : l.category = .endOfFile) hl
            | cons x a' => simp at hls'
          · rw [h1] at hls'
            have hloc := lexBytesW_location bytes hr
            cases a' with
            | nil =>
              simp only [List.nil_append, List.cons.injEq] at hls'
              obtain ⟨rfl, rfl⟩ := hls'
              refine ⟨bytes.length, Nat.le_refl _, by rw [List.take_length, hte, hloc], ?_⟩
              simp [lexBytesW, endStepW, List.drop_length, hte]
            | cons x a' =>
              simp only [List.cons_append, List.cons.injEq] at hls'
              obtain ⟨rfl, hls'⟩ := hls'
              cases a' with
              | nil =>
                simp only [List.nil_append, List.cons.injEq] at hls'
                exact absurd (hls'.1 ▸ rfl : l.category = .endOfFile) hl
              | cons y a' => simp at hls'
        · cases c' with
          | nil =>
            simp only [List.append_nil, List.nil_append] at hls hpost
            -- the lexeme is the first that the end of the input finishes
            rcases endStepW_cases hend with h1 | ⟨t, h1, hte⟩
            · rw [h1] at hpost
              simp only [List.cons.injEq] at hpost
              exact absurd (hpost.1 ▸ rfl : l.category = .endOfFile) hl
            · rw [h1] at hpost
              simp only [List.cons.injEq] at hpost
              obtain ⟨rfl, rfl⟩ := hpost
              have hloc := lexBytesW_location bytes hr
              refine ⟨bytes.length, Nat.le_refl _, by rw [List.take_length, hte, hloc], ?_⟩
              simp [lexBytesW, endStepW, List.drop_length, hte]
          | cons x c'' =>
            simp only [List.cons_append, List.cons.injEq] at hpost
            obtain ⟨rfl, rfl⟩ := hpost
            obtain ⟨k, hk, he, hrun⟩ :=
              (lexBytesW_restart version ws bytes).1 (hr.trans (by rw [hls]))
            exact ⟨k, hk, he, by rw [hrun]; simp [hend]⟩

/-- The run from the boundary at the offset `o` of the input: from nothing in progress, over the
input after `o`, and then, if the input has ended, the end of the input. -/
def stream (version : Token.Version) (ws : Bool) (input : List UInt8) (ended : Bool) (o : Nat) :
    List Lexeme × Bool :=
  streamFrom version ws ended (locAfter (input.take o)) (input.drop o)

/-- The tokens of the lexemes, as the consumer is handed them: whitespace and comments left
out. -/
def handedOf (version : Token.Version) (ls : List Lexeme) : List BSmtLibSpec.Lexer.Handed :=
  ls.filterMap (lexemeHanded version)

theorem handedAll_eq_handedOf {version : Token.Version} {ls : List Lexeme}
    (h : ∀ l ∈ ls, (Taken l)) :
    handedAll version ls = some (handedOf version ls) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    have hl := h l (by simp)
    unfold Lexeme.Taken at hl
    obtain ⟨x, hx⟩ : ∃ x, lexemeHanded version l = some x := by
      unfold lexemeHanded
      cases ht : toTokenType l.category with
      | none => rw [ht] at hl; cases hl
      | some t => exact ⟨_, rfl⟩
    rw [handedAll_cons_some hx, ih fun l' hl' => h l' (by simp [hl'])]
    simp [handedOf, hx]

theorem shiftRun_streamFrom (version : Token.Version) (ws ended : Bool)
    (base location : Span.Location)
    (bytes : List UInt8) :
    streamFrom version ws ended (locShift base location) bytes =
      ((streamFrom version ws ended location bytes).1.map (Lexeme.shift base),
        (streamFrom version ws ended location bytes).2) := by
  unfold streamFrom
  have := lexBytesW_shift version ws base bytes .idle location
  simp only [St.shift] at this
  rw [this]
  cases lexBytesW version ws .idle location bytes with
  | error ls => rfl
  | ok r =>
    obtain ⟨st, location', ls⟩ := r
    simp only [shiftRun]
    cases ended with
    | false => rfl
    | true =>
      simp only [ite_true]
      rw [endStepW_shift]
      cases endStepW ws st location' with
      | none => rfl
      | some ls' => simp [List.map_append]

theorem lexemeHanded_shift (version : Token.Version) (before : List UInt8) (l : Lexeme) :
    lexemeHanded version ((shift (locAfter before) l)) =
      (lexemeHanded version l).map (BSmtLibSpec.Lexer.Handed.after before) := by
  unfold lexemeHanded Lexeme.shift
  cases toTokenType l.category <;>
    simp [toLocation_shift, BSmtLibSpec.Lexer.Handed.after]

theorem handedOf_shift (version : Token.Version) (before : List UInt8) (ls : List Lexeme) :
    handedOf version (ls.map (Lexeme.shift (locAfter before))) =
      (handedOf version ls).map (BSmtLibSpec.Lexer.Handed.after before) := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [handedOf, List.map_cons, List.filterMap_cons, lexemeHanded_shift] at ih ⊢
    cases lexemeHanded version l <;> simp [ih]

/-- The run in the form of `fedOf` is its tokens. -/
theorem fedOf_eq_streamFrom (version : Token.Version) (ended : Bool) (location : Span.Location)
    (bytes : List UInt8) :
    fedOf version ended (lexBytes version .idle location bytes) =
      some (handedOf version (streamFrom version false ended location bytes).1,
        (streamFrom version false ended location bytes).2) := by
  have ht := lexBytes_taken (version := version) (location := location) bytes (st := .idle) trivial
  unfold streamFrom
  rw [lexBytesW_false, endStepW_false]
  cases hr : lexBytes version .idle location bytes with
  | error ls =>
    rw [hr] at ht
    simp only [fedOf, handedAll_eq_handedOf ht, Option.map_some]
  | ok r =>
    obtain ⟨st, location', ls⟩ := r
    rw [hr] at ht
    obtain ⟨hst, hls⟩ := ht
    cases ended with
    | false => simp only [fedOf, Bool.false_eq_true, ite_false, handedAll_eq_handedOf hls,
        Option.map_some]
    | true =>
      simp only [fedOf, ite_true]
      cases he : endStep st location' with
      | none => simp only [handedAll_eq_handedOf hls, Option.map_some]
      | some ls' =>
        have h' := endStep_taken he hst
        simp only
        rw [handedAll_eq_handedOf (fun l hl => by
          rcases List.mem_append.mp hl with hl | hl
          · exact hls l hl
          · exact h' l hl)]
        rfl

theorem toVersion_fromVersion (version : Token.Version) : toVersion
    (fromVersion version) = version := by
  cases version <;> rfl

theorem fromVersion_toVersion (version : BSmtLibSpec.Lexicon.Version) :
    fromVersion (toVersion version) = version := by
  cases version <;> rfl

/-- What the pure run hands over (`fedRun`) from the offset `o` of the input on, read on its own
and located in the whole input, is the tokens of the run from the boundary at `o`. -/
theorem segment_fedRun (version : BSmtLibSpec.Lexicon.Version) (input : List UInt8) (ended : Bool)
    (o : Nat) :
    BSmtLibSpec.Lexer.segment fedRun version input ended o =
      { handed := handedOf (toVersion version) (stream (toVersion version) false input ended o).1
        failed := (stream (toVersion version) false input ended o).2 } := by
  have h := fedRun_eq_run version [input.drop o] ended _ _
    (by rw [List.flatten_singleton]; exact fedOf_eq_streamFrom _ ended Span.Location.initial _)
  unfold BSmtLibSpec.Lexer.segment
  rw [h]
  simp only [stream]
  have hs := shiftRun_streamFrom (toVersion version) false ended (locAfter (input.take o))
    Span.Location.initial (input.drop o)
  rw [locShift_initial] at hs
  rw [hs, handedOf_shift]

end BSmtLib.Facts.Proofs.Lexer.Consumers.Stream

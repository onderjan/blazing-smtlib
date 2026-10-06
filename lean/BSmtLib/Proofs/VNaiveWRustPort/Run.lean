import BSmtLib.Proofs.VNaiveWRustPort.Slice

/-!
# The Rust port against the naive lexer's pure run

`handed_eq_run`: the Rust port `WRustPort`, run by the adapter, hands over what the naive
lexer's pure run `VNaive.run` finishes, as the adapter's consumer records it, however the
input is cut into slices. Between two calls the Rust port's lexer state is the naive lexer's
pure state at the end of what it was fed (`LexAgrees`): a call that lexes a slice
(`lexSliceStep_run`) lexes it as the naive lexer's run over its bytes (`sliceRun_ok`), and the
end of the input (`lexEofStep_run`) finishes as the naive lexer's (`lexEofInner_run`).

The slices are fed one at a time by the Rust port's step run (`stepSlice`), which gives the
lexer back also when a call fails; the public call is the step run without it
(`lexSlice_eq_stepSlice`). After any slices, before the end of the input, the Rust port has
handed over what the naive lexer's pure run over their bytes finishes, also up to an error, and
has failed exactly when that run fails or the consumer fails on a lexeme (`fedSteps_eq`, from
the start `fedSteps_new`); so the adapter's `fed` gives what the pure run gives (`fed_eq_run`).
The whole input follows from it with the end of the input (`handed_eq_run`).
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open BSmtLib.Proofs.Adapter VNaive BSmtLib.Proofs.Simulation

/-- The Rust port's monad of a call, with the adapter's consumer. -/
abbrev IM := Lexer.WRustPort.InnerM Collector Id

/-- What running a call from the lexer state and the consumer gives. -/
abbrev runI {α : Type} (x : IM α) (c : WCore) (coll : Collector) : (α × WCore) × Collector :=
  (x.run c).run coll

theorem runI_bind {α β : Type} (x : IM α) (f : α → IM β) (c : WCore) (coll : Collector) :
    runI (x >>= f) c coll =
      runI (f (runI x c coll).1.1) (runI x c coll).1.2 (runI x c coll).2 := rfl

theorem runI_getThe (c : WCore) (coll : Collector) :
    runI (getThe Lexer.WRustPort.LexerCore) c coll = ((c, c), coll) := rfl

theorem runI_pure {α : Type} (a : α) (c : WCore) (coll : Collector) :
    runI (pure a : IM α) c coll = ((a, c), coll) := rfl

theorem runI_modifyThe (f : WCore → WCore) (c : WCore) (coll : Collector) :
    runI (modifyThe Lexer.WRustPort.LexerCore f) c coll = (((), f c), coll) := rfl

/-- What a call that lexes a slice gives, with the result `res`, the lexer state `c'` and the
consumer `coll'`, as the naive lexer's run over the slice predicts with `o`: it goes on in the
predicted state with what the consumer records, or it fails, with what the consumer records of
the lexemes finished before the failure, or the consumer fails on a lexeme. -/
def SliceCall {ε α : Type} (v : Version) (cont : α)
    (o : Option (Except (List Spec.Lexer.Handed) (St × Location × List Spec.Lexer.Handed)))
    (res : Except ε α) (c' : WCore) (coll' : Collector) : Prop :=
  match o with
  | some (.ok (st', location', hs)) =>
    res = .ok cont ∧ Fixed v c' ∧ StAgrees v st' c' ∧ EofLoc c' location' ∧
      coll'.handed = hs
  | some (.error hs) => (∃ e, res = .error e) ∧ c'.recovers = false ∧ coll'.handed = hs
  | none => ∃ e, res = .error e

/-- The loop over the stops of the consumer in a slice, from its start, hands over what the
naive lexer's run over the slice finishes. -/
theorem sliceFrom_run (v : Version) (input : ByteSlice) (initialOffset floor : Nat)
    (hfloor : initialOffset ≤ floor + 1) (core : BS (some floor) 0) (coll : Collector) (st : St)
    (location : Location) (hpre : StepPre v input st location [] 0 core.val) :
    match (Lexer.WRustPort.lexSliceFrom (H := Collector) (m := Id) (R := Empty) (E := Unit) input
      initialOffset floor hfloor 0 (.ok .continue) core).run coll with
    | ((res, c'), coll') =>
      SliceCall v .continue (outcome v (some coll.handed) (feedFrom v input st location 0))
        res c' coll' := by
  rw [Lexer.WRustPort.lexSliceFrom, run_bindS]
  have h := sliceRun_ok v input _ 0 (Nat.lt_succ_self _) core coll st location [] hpre
  unfold SliceOut at h
  rw [pending_nil] at h
  generalize (Lexer.WRustPort.lexSliceRun (H := Collector) (m := Id) (R := Empty) (E := Unit)
    input 0 (.ok .continue) core).run coll = r at h ⊢
  obtain ⟨⟨exit, c'⟩, coll'⟩ := r
  unfold SliceCall
  cases ho : outcome v (some coll.handed) (feedFrom v input st location 0) with
  | none =>
    rw [ho] at h
    obtain ⟨g, hg⟩ := h
    simp only at hg
    subst hg
    exact ⟨g, rfl⟩
  | some r =>
    cases r with
    | ok e =>
      obtain ⟨st', location', hs⟩ := e
      rw [ho] at h
      obtain ⟨hex, hfix, hagree, hloc, hhs⟩ := h
      simp only at hex
      subst hex
      exact ⟨rfl, hfix, hagree, hloc, hhs⟩
    | error hs =>
      rw [ho] at h
      obtain ⟨⟨g, hg⟩, hrec, hhs⟩ := h
      simp only at hg
      subst hg
      exact ⟨⟨g, rfl⟩, hrec, hhs⟩

/-- Lexing a slice from the lexer state that is the naive lexer's pure state at `location`
hands over what the naive lexer's run over the slice finishes. -/
theorem sliceInner_run (v : Version) (slice : ByteSlice) (c : WCore) (coll : Collector)
    (st : St) (location : Location) (hfix : Fixed v c) (hagree : StAgrees v st c)
    (hloc : EofLoc c location) :
    match runI (Lexer.WRustPort.lexSliceInner (H := Collector) (m := Id) (R := Empty)
      (E := Unit) slice) c coll with
    | ((res, c'), coll') =>
      SliceCall v .continue (outcome v (some coll.handed) (feedFrom v slice st location 0))
        res c' coll' := by
  unfold Lexer.WRustPort.lexSliceInner
  refine sliceFrom_run v slice _ _ _ _ coll st location ⟨⟨hfix.1, hfix.2, hfix.3, hfix.4⟩, rfl,
    by cases st <;> exact hagree, ?_, holds_of_len_zero rfl, rfl⟩
  obtain ⟨h1, h2, h3⟩ := hloc
  exact ⟨by show location.offset = c.offset + (0 - 0); omega, h2, h3⟩

/-- A call that lexes a slice, from the lexer state that is the naive lexer's pure state at
`location`, lexes it as the naive lexer's run over its bytes. -/
theorem lexSliceStep_run (v : Version) (abandon recover : Location → StateT Collector Id Unit)
    (slice : ByteSlice) (c : WCore) (coll : Collector) (st : St) (location : Location)
    (hfix : Fixed v c) (hagree : StAgrees v st c) (hloc : EofLoc c location) :
    match runI (Lexer.WRustPort.lexSliceStep (H := Collector) (m := Id) (R := Empty) (E := Unit)
      abandon recover slice) c coll with
    | ((res, c'), coll') =>
      SliceCall v .continue (outcome v (some coll.handed) (feedFrom v slice st location 0))
        res c' coll' := by
  unfold Lexer.WRustPort.lexSliceStep Lexer.WRustPort.executeStep
  simp only [runI_bind, runI_getThe, hfix.discard, hfix.recoveryState, Bool.false_eq_true,
    ↓reduceIte]
  have hs := sliceInner_run v slice c coll st location hfix hagree hloc
  generalize runI (Lexer.WRustPort.lexSliceInner (H := Collector) (m := Id) (R := Empty)
    (E := Unit) slice) c coll = r at hs ⊢
  obtain ⟨⟨res, c'⟩, coll'⟩ := r
  unfold SliceCall at hs ⊢
  cases ho : outcome v (some coll.handed) (feedFrom v slice st location 0) with
  | none =>
    rw [ho] at hs
    obtain ⟨e, he⟩ := hs
    subst he
    exact ⟨_, rfl⟩
  | some r =>
    cases r with
    | ok e =>
      obtain ⟨st', location', hs'⟩ := e
      rw [ho] at hs
      obtain ⟨hres, hfix', hagree', hloc', hhs⟩ := hs
      subst hres
      exact ⟨rfl, hfix', hagree', hloc', hhs⟩
    | error hs' =>
      rw [ho] at hs
      obtain ⟨⟨e, he⟩, hrec, hhs⟩ := hs
      subst he
      simp only [runI_bind, runI_pure, Lexer.WRustPort.fail, runI_getThe, hrec, Bool.not_false,
        ↓reduceIte]
      exact ⟨⟨_, rfl⟩, trivial, hhs⟩

/-- The end of the input, from the lexer state that is the naive lexer's pure state at
`location`, hands over what the naive lexer's end of the input finishes. -/
theorem lexEofStep_run (v : Version) (abandon recover : Location → StateT Collector Id Unit)
    (c : WCore) (coll : Collector) (st : St) (location : Location) (hfix : Fixed v c)
    (hagree : StAgrees v st c) (hloc : EofLoc c location) :
    match runI (Lexer.WRustPort.lexEofStep (H := Collector) (m := Id) (R := Empty) (E := Unit)
      abandon recover) c coll with
    | ((res, _), coll') =>
      match (endStep st location).bind (handedAll v) with
      | some hs => res = .ok .continue ∧ coll'.handed = coll.handed ++ hs
      | none => ∃ e, res = .error e := by
  unfold Lexer.WRustPort.lexEofStep Lexer.WRustPort.executeStep
  simp only [runI_bind, runI_getThe, hfix.discard, hfix.recoveryState, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte]
  have h : match runI (Lexer.WRustPort.lexEofInner (H := Collector) (m := Id) (R := Empty)
      (E := Unit)) c coll with
    | ((res, _), coll') =>
      match (endStep st location).bind (handedAll v) with
      | some hs => res = .ok .continue ∧ coll'.handed = coll.handed ++ hs
      | none => ∃ f, res = .error f := lexEofInner_run v c coll st location hfix hagree hloc
  generalize runI (Lexer.WRustPort.lexEofInner (H := Collector) (m := Id) (R := Empty)
    (E := Unit)) c coll = r at h ⊢
  obtain ⟨⟨res, c'⟩, coll'⟩ := r
  cases hx : (endStep st location).bind (handedAll v) with
  | none =>
    rw [hx] at h
    obtain ⟨f, hf⟩ := h
    subst hf
    exact ⟨_, rfl⟩
  | some hs =>
    rw [hx] at h
    obtain ⟨hres, hhs⟩ := h
    subst hres
    exact ⟨rfl, hhs⟩

/-- The Rust port's lexer state between two calls is the naive lexer's pure state at
`location`, under the version. -/
def LexAgrees (v : Version) (st : St) (location : Location)
    (l : Lexer.WRustPort.Lexer Collector) : Prop :=
  Fixed v l.core ∧ StAgrees v st l.core ∧ EofLoc l.core location

/-! ## The calls, slice by slice -/

/-- A call of the Rust port that lexes a slice, with the adapter's consumer, by its step run,
which gives the lexer back also when the call fails. -/
def stepSlice (l : Lexer.WRustPort.Lexer Collector) (slice : ByteSlice) :
    Except (LexError Unit) (ControlFlow (Located Empty)) × Lexer.WRustPort.Lexer Collector :=
  l.run (Lexer.WRustPort.lexSliceStep (ops := Lexer.WRustPort.Rust.ops)
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast) slice)

/-- The Rust port's public call that lexes a slice is its step run, without the lexer when it
fails. -/
theorem lexSlice_eq_stepSlice (l : Lexer.WRustPort.Lexer Collector) (slice : ByteSlice) :
    (Lexer.WRustPort.Lexer.lexSlice l slice : Id _) =
      match stepSlice l slice with
      | (.ok flow, l') => .ok (flow, l')
      | (.error e, _) => .error (e, ()) := by
  unfold Lexer.WRustPort.Lexer.lexSlice stepSlice
  dsimp only
  generalize l.run (Lexer.WRustPort.lexSliceStep (ops := Lexer.WRustPort.Rust.ops)
    (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast) slice) = r
  obtain ⟨res, l'⟩ := r
  cases res <;> rfl

/-- What the Rust port has done after being fed the slices by its step run, before the end of
the input: the lexer, and whether a call failed. The feeding stops at the first call that
fails; the consumer never finishes, so no call breaks. -/
def fedSteps : Lexer.WRustPort.Lexer Collector → List Spec.Lexicon.Chars →
    Lexer.WRustPort.Lexer Collector × Bool
  | l, [] => (l, false)
  | l, slice :: slices =>
    match stepSlice l slice.toByteArray.toByteSlice with
    | (.ok .continue, l') => fedSteps l' slices
    | (.ok (.break finished), _) => finished.value.elim
    | (.error _, l') => (l', true)


/-- What the Rust port's step run gives for a slice, as the naive lexer's run over the slice
predicts with `o`: the lexer goes on in the predicted state, or fails with the consumer as the
run leaves it, or fails as the consumer fails on a lexeme. -/
def StepOut (v : Version)
    (o : Option (Except (List Spec.Lexer.Handed) (St × Location × List Spec.Lexer.Handed)))
    (r : Except (LexError Unit) (ControlFlow (Located Empty)) × Lexer.WRustPort.Lexer Collector) :
    Prop :=
  match o with
  | some (.ok (st', location', hs)) =>
    r.1 = .ok .continue ∧ LexAgrees v st' location' r.2 ∧ r.2.handler.handed = hs
  | some (.error hs) => (∃ e, r.1 = .error e) ∧ r.2.handler.handed = hs
  | none => ∃ e, r.1 = .error e

/-- A call that lexes a slice, by the step run, lexes it as the naive lexer's run over its
bytes. -/
theorem stepSlice_ops (v : Version) (l : Lexer.WRustPort.Lexer Collector) (slice : ByteSlice)
    (st : St) (location : Location) (h : LexAgrees v st location l) :
    StepOut v (outcome v (some l.handler.handed) (feedFrom v slice st location 0))
      (stepSlice l slice) := by
  obtain ⟨handler, core⟩ := l
  have hs := lexSliceStep_run v (LexRecovery.abandon Recovery.failFast)
    (LexRecovery.recover Recovery.failFast) slice core handler st location h.1 h.2.1 h.2.2
  unfold runI at hs
  simp only [stepSlice, Lexer.WRustPort.Lexer.run]
  generalize (StateT.run (Lexer.WRustPort.lexSliceStep (H := Collector) (m := Id) (R := Empty)
    (E := Unit) (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
    slice) core).run handler = r at hs ⊢
  obtain ⟨⟨res, c'⟩, coll'⟩ := r
  simp only at hs ⊢
  unfold SliceCall at hs
  unfold StepOut
  split at hs
  · obtain ⟨hres, hfix', hagree', hloc', hhs⟩ := hs
    exact ⟨hres, ⟨hfix', hagree', hloc'⟩, hhs⟩
  · exact ⟨hs.1, hs.2.2⟩
  · exact hs

/-- The run over two pieces of bytes, with the consumer that has recorded the lexemes of the
first piece. -/
theorem outcome_lexBytes_append (v : Version) (before : List Spec.Lexer.Handed) (st : St)
    (location : Location) (a b : List UInt8) :
    outcome v (some before) (lexBytes v st location (a ++ b)) =
      (outcome v (some before) (lexBytes v st location a)).bind fun r =>
        match r with
        | .ok (st', location', hs) => outcome v (some hs) (lexBytes v st' location' b)
        | .error hs => some (.error hs) := by
  rw [lexBytes_append]
  cases lexBytes v st location a with
  | error ls =>
    simp only [outcome, Option.bind_some]
    cases handedAll v ls <;> rfl
  | ok e =>
    obtain ⟨st', location', ls⟩ := e
    simp only
    rw [show withBefore ls (lexBytes v st' location' b) =
      Prep ls (lexBytes v st' location' b) from rfl]
    cases hls : handedAll v ls with
    | none =>
      have : outcome v (some before) (Prep ls (lexBytes v st' location' b)) = none := by
        rw [show some before = pending v ⟨before⟩ [] from (pending_nil v ⟨before⟩).symm,
          outcome_prep, List.nil_append, pending_none hls]
        rfl
      rw [this]
      simp [outcome, hls]
    | some hs =>
      rw [show some before = pending v ⟨before⟩ [] from (pending_nil v ⟨before⟩).symm,
        outcome_prep, List.nil_append, pending_some hls]
      simp [outcome, hls, pending_nil]

/-- The Rust port fed the slices by its step run, from a lexer state that is the naive lexer's
pure state at `location`, has handed over what the naive lexer's run over the bytes of the
slices finishes, and is at the naive lexer's pure state after them; it has failed exactly when
that run fails or the consumer fails on a lexeme, and when the run fails, it has handed over
what the run finishes before the failure. -/
theorem fedSteps_eq {v : Version} (slices : List Spec.Lexicon.Chars) :
    ∀ {st : St} {location : Location} (l : Lexer.WRustPort.Lexer Collector),
      LexAgrees v st location l →
      match outcome v (some l.handler.handed) (lexBytes v st location slices.flatten) with
      | some (.ok (st', location', hs)) =>
        (fedSteps l slices).2 = false ∧ (fedSteps l slices).1.handler.handed = hs ∧
          LexAgrees v st' location' (fedSteps l slices).1
      | some (.error hs) =>
        (fedSteps l slices).2 = true ∧ (fedSteps l slices).1.handler.handed = hs
      | none => (fedSteps l slices).2 = true := by
  induction slices with
  | nil =>
    intro st location l h
    simp only [List.flatten_nil, lexBytes, outcome, handedAll, List.mapM_nil, Option.bind_some,
      Option.pure_def, Option.map_some]
    exact ⟨rfl, (List.append_nil _).symm, h⟩
  | cons slice slices ih =>
    intro st location l h
    have hf := stepSlice_ops v l slice.toByteArray.toByteSlice st location h
    rw [feedFrom_toByteSlice v slice _ 0 rfl, List.drop_zero] at hf
    rw [List.flatten_cons, outcome_lexBytes_append]
    unfold StepOut at hf
    cases hx : outcome v (some l.handler.handed) (lexBytes v st location slice) with
    | none =>
      rw [hx] at hf
      obtain ⟨e, he⟩ := hf
      simp only [Option.bind_none, fedSteps]
      split
      · rename_i heq; rw [heq] at he; cases he
      · rename_i heq; rw [heq] at he; cases he
      · rfl
    | some r =>
      cases r with
      | error hs =>
        rw [hx] at hf
        obtain ⟨⟨e, he⟩, hhs⟩ := hf
        simp only [Option.bind_some, fedSteps]
        split
        · rename_i heq; rw [heq] at he; cases he
        · rename_i heq; rw [heq] at he; cases he
        · rename_i heq; rw [heq] at hhs; exact ⟨rfl, hhs⟩
      | ok e =>
        obtain ⟨st', location', hs⟩ := e
        rw [hx] at hf
        obtain ⟨hres, hag, hhs⟩ := hf
        simp only [Option.bind_some, fedSteps]
        generalize hr : stepSlice l slice.toByteArray.toByteSlice = r at hres hag hhs
        obtain ⟨res, l'⟩ := r
        simp only at hres hag hhs
        subst hres
        simp only
        rw [← hhs]
        exact ih l' hag

/-- The Rust port fed the slices by its step run from its start, before the end of the input,
has handed over what the naive lexer's pure run over the bytes of the slices finishes, also up to
an error, as the adapter's consumer records it, and has failed exactly when that run fails or the
consumer fails on a lexeme. -/
theorem fedSteps_new (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars) :
    match fedOf (toVersion version)
        (lexBytes (toVersion version) .idle Location.initial slices.flatten) with
    | some (hs, failed) =>
      (fedSteps (Lexer.WRustPort.Lexer.new { handed := [] } (toVersion version)) slices).2 =
          failed ∧
        (fedSteps (Lexer.WRustPort.Lexer.new { handed := [] } (toVersion version))
          slices).1.handler.handed = hs
    | none =>
      (fedSteps (Lexer.WRustPort.Lexer.new { handed := [] } (toVersion version)) slices).2 =
        true := by
  have h := fedSteps_eq (v := toVersion version) (st := .idle) (location := Location.initial)
    slices (Lexer.WRustPort.Lexer.new { handed := [] } (toVersion version))
    ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
  revert h
  generalize fedSteps (Lexer.WRustPort.Lexer.new { handed := [] } (toVersion version)) slices = r
  cases lexBytes (toVersion version) .idle Location.initial slices.flatten with
  | ok e =>
    obtain ⟨st', location', ls⟩ := e
    simp only [outcome, fedOf, Option.bind_some]
    cases handedAll (toVersion version) ls with
    | none => intro h; exact h
    | some hs =>
      intro h
      exact ⟨h.1, h.2.1⟩
  | error ls =>
    simp only [outcome, fedOf, Option.bind_some]
    cases handedAll (toVersion version) ls with
    | none => intro h; exact h
    | some hs =>
      intro h
      exact ⟨h.1, h.2⟩

/-- The adapter's feeding of slices by the step of `lexSlice` is the step run's. -/
theorem feedSlices_eq_fedSteps (l : Lexer.WRustPort.Lexer Collector)
    (slices : List Spec.Lexicon.Chars) :
    feedSlices Adapter.WRustPort.ops l slices =
      ((fedSteps l slices).1.handler, (fedSteps l slices).2) := by
  induction slices generalizing l with
  | nil => rfl
  | cons slice slices ih =>
    have e : Adapter.WRustPort.ops.lexSliceStep l slice.toByteArray.toByteSlice =
        stepSlice l slice.toByteArray.toByteSlice := rfl
    match hr : stepSlice l slice.toByteArray.toByteSlice with
    | (.error _, l') =>
      simp only [feedSlices, e, fedSteps, hr]
      rfl
    | (.ok .continue, l') =>
      simp only [feedSlices, e, fedSteps, hr]
      exact ih l'
    | (.ok (.break finished), _) => exact finished.value.elim

/-- `fed WRustPort.ops` gives what the naive lexer's pure run of the bytes of the slices gives,
also up to an error, if the consumer takes its lexemes. -/
theorem fed_eq_run (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars)
    (hs : List Spec.Lexer.Handed) (failed : Bool)
    (h : fedOf (toVersion version) (lexBytes (toVersion version) .idle Location.initial
      slices.flatten) = some (hs, failed)) :
    fed Adapter.WRustPort.ops version slices = { handed := hs, failed } := by
  have hn := fedSteps_new version slices
  rw [h] at hn
  simp only [fed, show Adapter.WRustPort.ops.new = Lexer.WRustPort.Lexer.new from rfl,
    feedSlices_eq_fedSteps]
  rw [hn.1]
  exact congrArg (fun hs => ({ handed := hs, failed } : Spec.Lexer.Fed)) hn.2
/-! ## The end of the input and the whole input -/

/-- A call of the adapter that lexes the end of the input hands over what the naive lexer's end
of the input finishes. -/
theorem lexEof_ops (v : Version) (l : Lexer.WRustPort.Lexer Collector) (st : St)
    (location : Location) (h : LexAgrees v st location l) :
    match (endStep st location).bind (handedAll v) with
    | some hs => ∃ l', Adapter.WRustPort.ops.lexEof l = .ok (.continue, l') ∧
        l'.handler.handed = l.handler.handed ++ hs
    | none => ∃ e, Adapter.WRustPort.ops.lexEof l = .error e := by
  obtain ⟨handler, core⟩ := l
  have hs := lexEofStep_run v (LexRecovery.abandon Recovery.failFast)
    (LexRecovery.recover Recovery.failFast) core handler st location h.1 h.2.1 h.2.2
  unfold runI at hs
  simp only [Adapter.WRustPort.ops, Lexer.WRustPort.Lexer.lexEof, Lexer.WRustPort.Lexer.run]
  generalize (StateT.run (Lexer.WRustPort.lexEofStep (H := Collector) (m := Id) (R := Empty)
    (E := Unit) (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast))
    core).run handler = r at hs ⊢
  obtain ⟨⟨res, c'⟩, coll'⟩ := r
  simp only at hs ⊢
  split at hs
  · rename_i hs' heq
    obtain ⟨hres, hhs⟩ := hs
    subst hres
    exact ⟨⟨coll', c'⟩, rfl, hhs⟩
  · rename_i heq
    obtain ⟨e, he⟩ := hs
    subst he
    exact ⟨_, rfl⟩

/-- The adapter's feeding of the slices is the step run's, and then the end of the input unless
a call failed. -/
theorem feed_eq_fedSteps (l : Lexer.WRustPort.Lexer Collector) (slices : List Spec.Lexicon.Chars) :
    feedAll Adapter.WRustPort.ops l slices =
      if (fedSteps l slices).2 then none
      else feedAll Adapter.WRustPort.ops (fedSteps l slices).1 [] := by
  induction slices generalizing l with
  | nil => rfl
  | cons slice slices ih =>
    have e : Adapter.WRustPort.ops.lexSlice l slice.toByteArray.toByteSlice =
        Lexer.WRustPort.Lexer.lexSlice l slice.toByteArray.toByteSlice := rfl
    match hr : stepSlice l slice.toByteArray.toByteSlice with
    | (.error _, l') =>
      simp only [feedAll, e, lexSlice_eq_stepSlice, fedSteps, hr]
      rfl
    | (.ok .continue, l') =>
      simp only [feedAll, e, lexSlice_eq_stepSlice, fedSteps, hr]
      exact ih l'
    | (.ok (.break finished), _) => exact finished.value.elim


/-- The Rust port, run by the adapter, gives what the naive lexer's pure run of the whole input
gives, as the consumer records it, however the input is cut into slices. -/
theorem handed_eq_run (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars) :
    handed Adapter.WRustPort.ops version slices =
      (VNaive.run (toVersion version) slices.flatten).bind (handedAll (toVersion version)) := by
  have h := fedSteps_eq (v := toVersion version) (st := .idle) (location := Location.initial)
    slices (Lexer.WRustPort.Lexer.new { handed := [] } (toVersion version))
    ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
  rw [handed, show Adapter.WRustPort.ops.new = Lexer.WRustPort.Lexer.new from rfl,
    feed_eq_fedSteps, VNaive.run, runFrom, ← lexBytes_toOption]
  revert h
  generalize fedSteps (Lexer.WRustPort.Lexer.new { handed := [] } (toVersion version)) slices = r
  obtain ⟨l', failed⟩ := r
  cases hx : lexBytes (toVersion version) .idle Location.initial slices.flatten with
  | error ls =>
    intro h
    simp only [outcome, Option.bind_some] at h
    have hf : failed = true := by
      cases hls : handedAll (toVersion version) ls with
      | none => rw [hls] at h; exact h
      | some hs => rw [hls] at h; exact h.1
    simp only [hf, ↓reduceIte, Except.toOption, Option.bind_none]
  | ok e =>
    obtain ⟨st', location', ls⟩ := e
    simp only [outcome, Option.bind_some, Except.toOption]
    cases hls : handedAll (toVersion version) ls with
    | none =>
      intro h
      simp only [Option.map_none] at h
      simp only [h, ↓reduceIte]
      cases endStep st' location' with
      | none => rfl
      | some ls' => simp [handedAll_append, hls]
    | some hs =>
      intro h
      simp only [Option.map_some] at h
      obtain ⟨hf, hh, hag⟩ := h
      subst hf
      simp only [Bool.false_eq_true, ↓reduceIte]
      have he := lexEof_ops (toVersion version) l' st' location' hag
      simp only [feedAll]
      cases hx' : (endStep st' location').bind (handedAll (toVersion version)) with
      | none =>
        rw [hx'] at he
        obtain ⟨e, he⟩ := he
        rw [he]
        cases hend : endStep st' location' with
        | none => rfl
        | some ls' =>
          rw [hend] at hx'
          simp only [Option.bind_some] at hx'
          simp [handedAll_append, hx']
      | some hs' =>
        rw [hx'] at he
        obtain ⟨l'', he, hhs⟩ := he
        rw [he]
        cases hend : endStep st' location' with
        | none => rw [hend] at hx'; simp at hx'
        | some ls' =>
          rw [hend] at hx'
          simp only [Option.bind_some] at hx'
          simp only [Option.map_some, Option.bind_some, handedAll_append, hls, hx']
          show some (Adapter.WRustPort.ops.handler l'').handed = _
          rw [show Adapter.WRustPort.ops.handler l'' = l''.handler from rfl, hhs, hh]
          rfl

end BSmtLib.Proofs.Lexer.VNaiveWRustPort

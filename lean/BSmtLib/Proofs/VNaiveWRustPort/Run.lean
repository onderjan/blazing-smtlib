import BSmtLib.Proofs.VNaiveWRustPort.Slice

/-!
# The Rust port against the naive lexer's pure run

`fedInput_eq_run`: the Rust port `WRustPort`, fed by the adapter slices and then, if the input
has ended, the end of the input, hands over what the naive lexer's pure run over the bytes and
then its end of the input finish, also up to an error, as the adapter's consumer records it,
and fails exactly when they do, however the input is cut into slices. Between two calls the
Rust port's lexer state is the naive lexer's pure state at the end of what it was fed
(`LexAgrees`): a call that lexes a slice (`lexSliceStep_run`) lexes it as the naive lexer's run
over its bytes (`sliceRun_ok`), and the end of the input (`lexEofStep_run`) finishes as the
naive lexer's (`lexEofInner_run`), and when that fails, hands over nothing more.

The slices are fed one at a time by the Rust port's step run (`stepSlice`), which gives the
lexer back also when a call fails, as the adapter's step does (`feedInput_eq_fedSteps`); the
public call is the step run without it (`lexSlice_eq_stepSlice`). After any slices the Rust port
has handed over what the naive lexer's pure run over their bytes finishes, also up to an error,
and has failed exactly when that run fails or the consumer fails on a lexeme (`fedSteps_eq`);
the end of the input follows unless a call failed (`feedEnd_ops`).
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

theorem runI_liftM {α : Type} (x : StateT Collector Id α) (c : WCore) (coll : Collector) :
    runI (liftM x : IM α) c coll = (((x.run coll).1, c), (x.run coll).2) := rfl

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

/-- Turning a failure into the error to return records nothing, if abandoning leaves the
consumer as it is. -/
theorem fail_coll (abandon : Location → StateT Collector Id Unit)
    (habandon : ∀ location coll, (abandon location).run coll = ((), coll))
    (failure : Lexer.Failure Unit) (atEnd : Bool) (c : WCore) (coll : Collector) :
    (runI (Lexer.WRustPort.fail (H := Collector) (m := Id) (E := Unit) abandon failure atEnd) c
      coll).2 = coll := by
  unfold Lexer.WRustPort.fail
  simp only [runI_bind, runI_getThe]
  by_cases hr : c.recovers = true
  · simp only [hr, Bool.not_true, Bool.false_eq_true, ↓reduceIte, runI_bind, runI_modifyThe,
      runI_pure, runI_liftM, habandon]
  · simp only [Bool.not_eq_true] at hr
    simp only [hr, Bool.not_false, ↓reduceIte, runI_pure]

/-- The end of the input, from the lexer state that is the naive lexer's pure state at
`location`, hands over what the naive lexer's end of the input finishes; when that fails, the
consumer has recorded nothing more, if abandoning leaves it as it is. -/
theorem lexEofStep_run (v : Version) (abandon recover : Location → StateT Collector Id Unit)
    (habandon : ∀ location coll, (abandon location).run coll = ((), coll))
    (c : WCore) (coll : Collector) (st : St) (location : Location) (hfix : Fixed v c)
    (hagree : StAgrees v st c) (hloc : EofLoc c location) :
    match runI (Lexer.WRustPort.lexEofStep (H := Collector) (m := Id) (R := Empty) (E := Unit)
      abandon recover) c coll with
    | ((res, _), coll') =>
      match (endStep st location).bind (handedAll v) with
      | some hs => res = .ok .continue ∧ coll'.handed = coll.handed ++ hs
      | none => (∃ e, res = .error e) ∧
        (endStep st location = none → coll'.handed = coll.handed) := by
  unfold Lexer.WRustPort.lexEofStep Lexer.WRustPort.executeStep
  simp only [runI_bind, runI_getThe, hfix.discard, hfix.recoveryState, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte]
  have h : match runI (Lexer.WRustPort.lexEofInner (H := Collector) (m := Id) (R := Empty)
      (E := Unit)) c coll with
    | ((res, _), coll') =>
      match (endStep st location).bind (handedAll v) with
      | some hs => res = .ok .continue ∧ coll'.handed = coll.handed ++ hs
      | none => (∃ f, res = .error f) ∧
        (endStep st location = none → coll'.handed = coll.handed) :=
    lexEofInner_run v c coll st location hfix hagree hloc
  generalize runI (Lexer.WRustPort.lexEofInner (H := Collector) (m := Id) (R := Empty)
    (E := Unit)) c coll = r at h ⊢
  obtain ⟨⟨res, c'⟩, coll'⟩ := r
  cases hx : (endStep st location).bind (handedAll v) with
  | none =>
    rw [hx] at h
    obtain ⟨⟨f, hf⟩, hcoll⟩ := h
    subst hf
    simp only [runI_bind, runI_pure, fail_coll abandon habandon]
    exact ⟨⟨_, rfl⟩, hcoll⟩
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

/-! ## The end of the input and the adapter -/

/-- The adapter's feeding of the slices by the step of `lexSlice` is the step run's, followed,
unless a call failed, by what the adapter feeds after the slices. -/
theorem feedInput_eq_fedSteps (l : Lexer.WRustPort.Lexer Collector) (ended : Bool)
    (slices : List Spec.Lexicon.Chars) :
    feedInput Adapter.WRustPort.ops l ended slices =
      if (fedSteps l slices).2 then ((fedSteps l slices).1.handler, true)
      else feedInput Adapter.WRustPort.ops (fedSteps l slices).1 ended [] := by
  induction slices generalizing l with
  | nil => rfl
  | cons slice slices ih =>
    have e : Adapter.WRustPort.ops.lexSliceStep l slice.toByteArray.toByteSlice =
        stepSlice l slice.toByteArray.toByteSlice := rfl
    match hr : stepSlice l slice.toByteArray.toByteSlice with
    | (.error _, l') =>
      simp only [feedInput, e, fedSteps, hr]
      rfl
    | (.ok .continue, l') =>
      simp only [feedInput, e, fedSteps, hr]
      exact ih l'
    | (.ok (.break finished), _) => exact finished.value.elim

/-- The adapter's feeding of the end of the input, from a lexer state that is the naive lexer's
pure state at `location`, hands over what the naive lexer's end of the input finishes; when that
fails, the consumer has recorded nothing more. -/
theorem feedEnd_ops (v : Version) (l : Lexer.WRustPort.Lexer Collector) (st : St)
    (location : Location) (h : LexAgrees v st location l) :
    match (endStep st location).bind (handedAll v) with
    | some hs => (feedEnd Adapter.WRustPort.ops l).2 = false ∧
        (feedEnd Adapter.WRustPort.ops l).1.handed = l.handler.handed ++ hs
    | none => (feedEnd Adapter.WRustPort.ops l).2 = true ∧
        (endStep st location = none →
          (feedEnd Adapter.WRustPort.ops l).1.handed = l.handler.handed) := by
  obtain ⟨handler, core⟩ := l
  have hs := lexEofStep_run v (LexRecovery.abandon Recovery.failFast)
    (LexRecovery.recover Recovery.failFast) (fun _ _ => rfl) core handler st location h.1 h.2.1
    h.2.2
  unfold runI at hs
  simp only [feedEnd, Adapter.WRustPort.ops, Lexer.WRustPort.Lexer.run]
  generalize (StateT.run (Lexer.WRustPort.lexEofStep (H := Collector) (m := Id) (R := Empty)
    (E := Unit) (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast))
    core).run handler = r at hs ⊢
  obtain ⟨⟨res, c'⟩, coll'⟩ := r
  simp only at hs ⊢
  cases hx : (endStep st location).bind (handedAll v) with
  | some hs' =>
    rw [hx] at hs
    obtain ⟨hres, hhs⟩ := hs
    subst hres
    exact ⟨rfl, hhs⟩
  | none =>
    rw [hx] at hs
    obtain ⟨⟨e, he⟩, hc⟩ := hs
    subst he
    exact ⟨rfl, hc⟩

/-- `fedInput WRustPort.ops` gives what the naive lexer's pure run of the bytes of the slices and
then, if the input has ended, the naive lexer's end of the input give, also up to an error, if
the consumer takes the lexemes. -/
theorem fedInput_eq_run (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars)
    (ended : Bool) (hs : List Spec.Lexer.Handed) (failed : Bool)
    (h : fedOf (toVersion version) ended (lexBytes (toVersion version) .idle Location.initial
      slices.flatten) = some (hs, failed)) :
    fedInput Adapter.WRustPort.ops version slices ended = { handed := hs, failed } := by
  have hfs := fedSteps_eq (v := toVersion version) (st := .idle) (location := Location.initial)
    slices (Lexer.WRustPort.Lexer.new { handed := [] } (toVersion version))
    ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
  have hnew : (Lexer.WRustPort.Lexer.new ({ handed := [] } : Collector)
      (toVersion version)).handler.handed = [] := rfl
  rw [hnew] at hfs
  simp only [fedInput, show Adapter.WRustPort.ops.new = Lexer.WRustPort.Lexer.new from rfl]
  rw [feedInput_eq_fedSteps]
  revert hfs h
  generalize fedSteps (Lexer.WRustPort.Lexer.new { handed := [] } (toVersion version)) slices = r
  obtain ⟨l', fl⟩ := r
  cases lexBytes (toVersion version) .idle Location.initial slices.flatten with
  | error ls =>
    intro h hfs
    dsimp only
    cases hls : handedAll (toVersion version) ls with
    | none => simp [fedOf, hls] at h
    | some hs' =>
      simp only [outcome, Option.bind_some, hls, Option.map_some, List.nil_append] at hfs
      simp only [fedOf, hls, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hh⟩ := hfs
      obtain ⟨rfl, rfl⟩ := h
      simp only [↓reduceIte]
      rw [hh]
  | ok e =>
    obtain ⟨st', location', ls⟩ := e
    intro h hfs
    dsimp only
    cases hls : handedAll (toVersion version) ls with
    | none =>
      cases ended with
      | false => simp [fedOf, hls] at h
      | true =>
        simp only [fedOf, ↓reduceIte] at h
        cases hend : endStep st' location' with
        | none => rw [hend] at h; simp [hls] at h
        | some ls' => rw [hend] at h; simp [handedAll_append, hls] at h
    | some hs1 =>
      simp only [outcome, Option.bind_some, hls, Option.map_some, List.nil_append] at hfs
      obtain ⟨rfl, hh, hag⟩ := hfs
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases ended with
      | false =>
        simp only [fedOf, Bool.false_eq_true, ↓reduceIte, hls, Option.map_some,
          Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [feedInput, Bool.false_eq_true, ↓reduceIte]
        rw [show Adapter.WRustPort.ops.handler l' = l'.handler from rfl, hh]
      | true =>
        have he := feedEnd_ops (toVersion version) l' st' location' hag
        simp only [feedInput, ↓reduceIte]
        simp only [fedOf, ↓reduceIte] at h
        cases hend : endStep st' location' with
        | none =>
          rw [hend] at h he
          simp only [Option.bind_none] at he
          simp only [hls, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [he.1, he.2 trivial, hh]
        | some ls' =>
          rw [hend] at h he
          simp only [Option.bind_some] at he
          simp only [handedAll_append, hls, Option.bind_some] at h
          cases hls' : handedAll (toVersion version) ls' with
          | none => rw [hls'] at h; cases h
          | some hs2 =>
            rw [hls'] at h he
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rw [he.1, he.2, hh]

end BSmtLib.Proofs.Lexer.VNaiveWRustPort

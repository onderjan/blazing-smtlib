import BSmtLib.Proofs.V4FastPathsWRustPort.Slice

/-!
# The Rust port against the naive lexer's pure run

`handed_eq_run`: the Rust port `WRustPort`, run by the adapter, hands over what the naive
lexer's pure run `V1Naive.run` finishes, as the adapter's consumer records it, however the
input is cut into slices. Between two calls the Rust port's lexer state is the naive lexer's
pure state at the end of what it was fed (`LexAgrees`): a call that lexes a slice
(`lexSliceStep_run`) lexes it as the naive lexer's run over its bytes (`sliceRun_ok`), and the
end of the input (`lexEofStep_run`) finishes as the naive lexer's (`lexEofInner_run`).
-/

namespace BSmtLib.Proofs.Lexer.V4FastPathsWRustPort

open BSmtLib.Proofs.Adapter V1Naive V1NaiveV2Batched V3Runs V2BatchedV3Runs

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

/-- The loop over the stops of the consumer in a slice, from its start, hands over what the
naive lexer's run over the slice finishes. -/
theorem sliceFrom_run (v : Version) (input : ByteSlice) (initialOffset floor : Nat)
    (hfloor : initialOffset ≤ floor + 1) (core : BS (some floor) 0) (coll : Collector) (st : St)
    (location : Location) (hpre : StepPre v input st location [] 0 core.val) :
    match (Lexer.WRustPort.lexSliceFrom (H := Collector) (m := Id) (R := Empty) (E := Unit) input
      initialOffset floor hfloor 0 (.ok .continue) core).run coll with
    | ((res, c'), coll') =>
      match outcome v (some coll.handed) (feedFrom v input st location 0) with
      | some (st', location', hs) =>
        res = .ok .continue ∧ Fixed v c' ∧ StAgrees v st' c' ∧ EofLoc c' location' ∧
          coll'.handed = hs
      | none => ∃ e, res = .error e := by
  rw [Lexer.WRustPort.lexSliceFrom, run_bindS]
  have h := sliceRun_ok v input _ 0 (Nat.lt_succ_self _) core coll st location [] hpre
  unfold SliceOut at h
  rw [pending_nil] at h
  generalize (Lexer.WRustPort.lexSliceRun (H := Collector) (m := Id) (R := Empty) (E := Unit)
    input 0 (.ok .continue) core).run coll = r at h ⊢
  obtain ⟨⟨exit, c'⟩, coll'⟩ := r
  cases ho : outcome v (some coll.handed) (feedFrom v input st location 0) with
  | none =>
    rw [ho] at h
    obtain ⟨g, hg⟩ := h
    simp only at hg
    subst hg
    exact ⟨g, rfl⟩
  | some e =>
    obtain ⟨st', location', hs⟩ := e
    rw [ho] at h
    obtain ⟨hex, hfix, hagree, hloc, hhs⟩ := h
    simp only at hex
    subst hex
    exact ⟨rfl, hfix, hagree, hloc, hhs⟩

/-- Lexing a slice from the lexer state that is the naive lexer's pure state at `location`
hands over what the naive lexer's run over the slice finishes. -/
theorem sliceInner_run (v : Version) (slice : ByteSlice) (c : WCore) (coll : Collector)
    (st : St) (location : Location) (hfix : Fixed v c) (hagree : StAgrees v st c)
    (hloc : EofLoc c location) :
    match runI (Lexer.WRustPort.lexSliceInner (H := Collector) (m := Id) (R := Empty)
      (E := Unit) slice) c coll with
    | ((res, c'), coll') =>
      match outcome v (some coll.handed) (feedFrom v slice st location 0) with
      | some (st', location', hs) =>
        res = .ok .continue ∧ Fixed v c' ∧ StAgrees v st' c' ∧ EofLoc c' location' ∧
          coll'.handed = hs
      | none => ∃ e, res = .error e := by
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
      match outcome v (some coll.handed) (feedFrom v slice st location 0) with
      | some (st', location', hs) =>
        res = .ok .continue ∧ Fixed v c' ∧ StAgrees v st' c' ∧ EofLoc c' location' ∧
          coll'.handed = hs
      | none => ∃ e, res = .error e := by
  unfold Lexer.WRustPort.lexSliceStep Lexer.WRustPort.executeStep
  simp only [runI_bind, runI_getThe, hfix.discard, hfix.recoveryState, Bool.false_eq_true,
    ↓reduceIte]
  have hs := sliceInner_run v slice c coll st location hfix hagree hloc
  generalize runI (Lexer.WRustPort.lexSliceInner (H := Collector) (m := Id) (R := Empty)
    (E := Unit) slice) c coll = r at hs ⊢
  obtain ⟨⟨res, c'⟩, coll'⟩ := r
  cases ho : outcome v (some coll.handed) (feedFrom v slice st location 0) with
  | none =>
    rw [ho] at hs
    obtain ⟨e, he⟩ := hs
    subst he
    exact ⟨_, rfl⟩
  | some e =>
    obtain ⟨st', location', hs'⟩ := e
    rw [ho] at hs
    obtain ⟨hres, hfix', hagree', hloc', hhs⟩ := hs
    subst hres
    exact ⟨rfl, hfix', hagree', hloc', hhs⟩

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

/-- A call of the adapter that lexes a slice lexes it as the naive lexer's run over its bytes. -/
theorem lexSlice_ops (v : Version) (l : Lexer.WRustPort.Lexer Collector) (slice : ByteSlice)
    (st : St) (location : Location) (h : LexAgrees v st location l) :
    match outcome v (some l.handler.handed) (feedFrom v slice st location 0) with
    | some (st', location', hs) =>
      ∃ l', Adapter.WRustPort.ops.lexSlice l slice = .ok (.continue, l') ∧
        LexAgrees v st' location' l' ∧ l'.handler.handed = hs
    | none => ∃ e, Adapter.WRustPort.ops.lexSlice l slice = .error e := by
  obtain ⟨handler, core⟩ := l
  have hs := lexSliceStep_run v (LexRecovery.abandon Recovery.failFast)
    (LexRecovery.recover Recovery.failFast) slice core handler st location h.1 h.2.1 h.2.2
  unfold runI at hs
  simp only [Adapter.WRustPort.ops, Lexer.WRustPort.Lexer.lexSlice, Lexer.WRustPort.Lexer.run]
  generalize (StateT.run (Lexer.WRustPort.lexSliceStep (H := Collector) (m := Id) (R := Empty)
    (E := Unit) (LexRecovery.abandon Recovery.failFast) (LexRecovery.recover Recovery.failFast)
    slice) core).run handler = r at hs ⊢
  obtain ⟨⟨res, c'⟩, coll'⟩ := r
  simp only at hs ⊢
  split at hs
  · rename_i st' location' hs' heq
    obtain ⟨hres, hfix', hagree', hloc', hhs⟩ := hs
    subst hres
    exact ⟨⟨coll', c'⟩, rfl, ⟨hfix', hagree', hloc'⟩, hhs⟩
  · rename_i heq
    obtain ⟨e, he⟩ := hs
    subst he
    exact ⟨_, rfl⟩

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

theorem feed_eq {v : Version} (slices : List Spec.Lexicon.Chars) :
    ∀ {st : St} {location : Location} (l : Lexer.WRustPort.Lexer Collector),
      LexAgrees v st location l →
      feed Adapter.WRustPort.ops l slices =
        (runFrom v st location slices.flatten).bind fun ls =>
          (handedAll v ls).map (l.handler.handed ++ ·) := by
  induction slices with
  | nil =>
    intro st location l h
    have he := lexEof_ops v l st location h
    simp only [feed, List.flatten_nil, runFrom, feedBytes, Option.bind_some]
    cases hx : (endStep st location).bind (handedAll v) with
    | none =>
      rw [hx] at he
      obtain ⟨e, he⟩ := he
      rw [he]
      cases hend : endStep st location with
      | none => rfl
      | some ls =>
        rw [hend] at hx
        simp only [Option.bind_some] at hx
        simp [hx]
    | some hs =>
      rw [hx] at he
      obtain ⟨l', he, hhs⟩ := he
      rw [he]
      cases hend : endStep st location with
      | none => rw [hend] at hx; simp at hx
      | some ls =>
        rw [hend] at hx
        simp only [Option.bind_some] at hx
        simp only [List.nil_append, Option.bind_some, hx, Option.map_some]
        exact congrArg some hhs
  | cons slice slices ih =>
    intro st location l h
    have hf := lexSlice_ops v l slice.toByteArray.toByteSlice st location h
    rw [feedFrom_toByteSlice v slice _ 0 rfl, List.drop_zero] at hf
    simp only [feed, List.flatten_cons, runFrom_append]
    cases hx : feedBytes v st location slice with
    | none =>
      rw [hx] at hf
      obtain ⟨e, he⟩ := hf
      rw [he]
      rfl
    | some e =>
      obtain ⟨st', location', ls⟩ := e
      rw [hx] at hf
      simp only [outcome, Option.bind_some] at hf
      cases hls : handedAll v ls with
      | none =>
        rw [hls] at hf
        obtain ⟨e, he⟩ := hf
        rw [he]
        simp only [Option.bind_some]
        cases runFrom v st' location' slices.flatten with
        | none => rfl
        | some ls' => simp [handedAll_append, hls]
      | some hs =>
        rw [hls] at hf
        obtain ⟨l', he, hag, hhs⟩ := hf
        rw [he]
        simp only [Option.bind_some]
        rw [ih l' hag]
        cases runFrom v st' location' slices.flatten with
        | none => rfl
        | some ls' =>
          simp only [Option.bind_some, Option.map_some, handedAll_append, hls, hhs]
          cases handedAll v ls' <;> simp [List.append_assoc]

/-- The Rust port, run by the adapter, gives what the naive lexer's pure run of the whole input
gives, as the consumer records it, however the input is cut into slices. -/
theorem handed_eq_run (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars) :
    handed Adapter.WRustPort.ops version slices =
      (V1Naive.run (toVersion version) slices.flatten).bind (handedAll (toVersion version)) := by
  rw [handed, show Adapter.WRustPort.ops.new = Lexer.WRustPort.Lexer.new from rfl, V1Naive.run,
    feed_eq (v := toVersion version) (st := .idle)
    (location := Location.initial) slices (Lexer.WRustPort.Lexer.new { handed := [] }
      (toVersion version))
    ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩]
  cases runFrom (toVersion version) .idle Location.initial slices.flatten with
  | none => rfl
  | some ls =>
    show Option.map ([] ++ ·) (handedAll (toVersion version) ls) =
      handedAll (toVersion version) ls
    cases handedAll (toVersion version) ls <;> rfl

end BSmtLib.Proofs.Lexer.V4FastPathsWRustPort

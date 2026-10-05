import BSmtLib.Proofs.V1NaiveV2Batched.HandOver
import BSmtLib.Proofs.V2BatchedV3Runs.Steps

/-!
# The batched lexer against the naive lexer's pure run

The batched lexer, run by the adapter, hands over what the naive lexer's pure run
`V1Naive.run` finishes, as the adapter's consumer records it, however the input is cut into
slices (`handed_eq_run`). Between two bytes the batched lexer holds a batch of lexemes not yet
handed over; what the consumer has recorded together with what it will record of the batch
(`pending`) is what the naive lexer's consumer has recorded.
-/

namespace BSmtLib.Proofs.Lexer.V1NaiveV2Batched

open BSmtLib.Proofs.Adapter V1Naive V2Batched V2BatchedV3Runs

/-- What the consumer has recorded and will record of the lexemes, or none if it fails on one
of them. -/
def pending (v : Version) (coll : Collector) (ls : List Lexeme) : Option (List Spec.Lexer.Handed) :=
  (handedAll v ls).map (coll.handed ++ ·)

/-- The outcome of a step is a failure. -/
def Fails (o : Outcome Empty Unit) : Prop :=
  ∃ f, o = .failed f ∨ o = .stopped (.failed f)

theorem pending_none_append {v : Version} {coll : Collector} {xs : List Lexeme}
    (h : pending v coll xs = none) (ys : List Lexeme) : pending v coll (xs ++ ys) = none := by
  simp only [pending, Option.map_eq_none_iff] at h ⊢
  rw [handedAll_append, h]
  rfl

theorem handedAll_single (v : Version) (l : Lexeme) :
    handedAll v [l] = (lexemeHanded v l).map ([·]) := by
  simp only [handedAll, List.mapM_cons, List.mapM_nil]
  cases lexemeHanded v l <;> rfl

/-- A result of a step, without the proof that the batch fits the state. -/
def strip {α : Type} {P : α → Prop} (r : {a // P a} × Collector) : α × Collector :=
  (r.1.1, r.2)

/-- What a hand-over of the lexeme `l` after the batch `b` may give: the lexer goes on in the same
state, and the consumer records or will record the batch and the lexeme; or the hand-over fails,
and the consumer would fail on the batch and the lexeme. -/
def EmitSpec (core : Core) (b : Array Lexeme) (l : Lexeme) (coll : Collector)
    (r : (Outcome Empty Unit × Core × Array Lexeme) × Collector) : Prop :=
  (r.1.1 = .next ∧ r.1.2.1.version = core.version ∧ r.1.2.1.location = core.location ∧
    r.1.2.1.activity = core.activity ∧
    pending core.version r.2 r.1.2.2.toList = pending core.version coll (b.toList ++ [l])) ∨
  (Fails r.1.1 ∧ pending core.version coll (b.toList ++ [l]) = none)

/-- What the batched lexer's hand-over of a lexeme does with the consumer. -/
theorem emit_run (sliceStart : Nat) (core : Core) (b : Array Lexeme) (l : Lexeme)
    (h : Ordered 0 b.toList) (hstart : lastEnd 0 b.toList ≤ l.start.offset) (hl : l.Valid)
    (hend : l.end.offset ≤ core.frontier) (coll : Collector) :
    EmitSpec core b l coll (strip ((emit (H := Collector) (m := Id) (R := Empty) (E := Unit)
      sliceStart core b l h hstart hl hend).run coll)) := by
  unfold emit
  split
  · simp only [StateT.run_bind]
    obtain ⟨fok, ferr⟩ := flush_batch core b h coll
    generalize (flush (H := Collector) (m := Id) (R := Empty) (E := Unit) core b h).run coll = X
      at fok ferr ⊢
    obtain ⟨⟨stop, core1⟩, coll1⟩ := X
    cases hb : handedAll core.version b.toList with
    | none =>
      obtain ⟨f, hf⟩ := ferr hb
      simp only at hf
      subst hf
      right
      exact ⟨⟨f, Or.inr rfl⟩, pending_none_append (by simp [pending, hb]) _⟩
    | some hs =>
      obtain ⟨h1, ⟨d, h2⟩, h3⟩ := fok hs hb
      simp only at h1 h2 h3
      subst h1 h2
      have hh := handOverAt_run { core with depth := d } l hl coll1
      simp only [StateT.run] at hh ⊢
      simp only [bind, StateT.bind, hh]
      cases hlh : lexemeHanded core.version l with
      | some x =>
        left
        refine ⟨rfl, rfl, rfl, rfl, ?_⟩
        show pending core.version { handed := coll1.handed ++ [x] } [] = _
        simp only [pending, handedAll_append, hb, handedAll_single, hlh, h3, Option.bind_some,
          Option.map_some]
        simp [handedAll]
      | none =>
        right
        refine ⟨⟨_, Or.inl rfl⟩, ?_⟩
        simp [pending, handedAll_append, hb, handedAll_single, hlh]
  · simp only
    split
    · left
      simp [strip, pending, pure, StateT.pure, StateT.run]
    · simp only [StateT.run_bind]
      have hpush : Ordered 0 (b.push l).toList := by
        rw [Array.toList_push]
        exact ordered_append h hstart hl
      obtain ⟨fok, ferr⟩ := flush_batch core (b.push l) hpush coll
      generalize (flush (H := Collector) (m := Id) (R := Empty) (E := Unit) core
        (b.push l) _).run coll = X at fok ferr ⊢
      obtain ⟨⟨stop, core1⟩, coll1⟩ := X
      rw [Array.toList_push] at fok ferr
      cases hb : handedAll core.version (b.toList ++ [l]) with
      | none =>
        obtain ⟨f, hf⟩ := ferr hb
        simp only at hf
        subst hf
        right
        exact ⟨⟨f, Or.inr rfl⟩, by simp [pending, hb]⟩
      | some hs =>
        obtain ⟨h1, ⟨d, h2⟩, h3⟩ := fok hs hb
        simp only at h1 h2 h3
        subst h1 h2
        left
        refine ⟨rfl, rfl, rfl, rfl, ?_⟩
        show pending core.version coll1 [] = _
        simp only [pending, hb, h3, Option.map_some]
        simp [handedAll]

theorem pending_congr_append {v : Version} {c₁ c₂ : Collector} {xs ys : List Lexeme}
    (h : pending v c₁ xs = pending v c₂ ys) (zs : List Lexeme) :
    pending v c₁ (xs ++ zs) = pending v c₂ (ys ++ zs) := by
  simp only [pending] at h ⊢
  rw [handedAll_append, handedAll_append]
  cases h1 : handedAll v xs with
  | none =>
    cases h2 : handedAll v ys with
    | none => rfl
    | some y => rw [h1, h2] at h; simp at h
  | some x =>
    cases h2 : handedAll v ys with
    | none => rw [h1, h2] at h; simp at h
    | some y =>
      rw [h1, h2] at h
      simp only [Option.map_some, Option.some.injEq] at h
      cases handedAll v zs with
      | none => rfl
      | some z =>
        simp only [Option.bind_some, Option.map_some, Option.some.injEq]
        rw [← List.append_assoc, h, List.append_assoc]

/--
What a step of the batched lexer at a byte may give, against the naive lexer's pure step
`expected`, after the batch `b`: if the pure step goes on, the lexer goes on in the state it
predicts, and the consumer records or will record the batch and the lexemes the step finishes;
or the step fails, and the consumer would fail on them. If the pure step fails, so does the
lexer.
-/
def StepSpec (version : Version) (expected : Option (St × List Lexeme)) (location : Location)
    (b : Array Lexeme) (coll : Collector)
    (r : (Outcome Empty Unit × Core × Array Lexeme) × Collector) : Prop :=
  match expected with
  | some (st, ls) =>
    (r.1.1 = .next ∧ Agrees version st location r.1.2.1 ∧
      pending version r.2 r.1.2.2.toList = pending version coll (b.toList ++ ls)) ∨
    (Fails r.1.1 ∧ pending version coll (b.toList ++ ls) = none)
  | none => Fails r.1.1

theorem collector_ws : Consume.consumesWhitespaceAndComments (H := Collector) = false := rfl

theorem lexStart_run2 {version : Version} {location : Location} {core : Core}
    (hv : core.version = version) (hl : core.location = location) (sliceStart : Nat)
    (b : Array Lexeme) (coll : Collector) (c : UInt8) (hfits : Fits core b) :
    StepSpec version (startStep version location c) (location.afterByte c) b coll
      (strip ((V2Batched.lexStart (H := Collector) (m := Id) sliceStart core b c hfits).run
        coll)) := by
  subst hv hl
  simp only [V2Batched.lexStart, startStep, collector_ws]
  cases hs : start core.version false core.location c with
  | idle =>
    simp only [startS, hs]
    left
    refine ⟨rfl, ⟨rfl, rfl, rfl⟩, ?_⟩
    show pending core.version coll b.toList = _
    rw [List.append_nil]
  | pending p =>
    simp only [startS, hs]
    left
    refine ⟨rfl, ⟨rfl, rfl, rfl⟩, ?_⟩
    show pending core.version coll b.toList = _
    rw [List.append_nil]
  | token l =>
    simp only [startS, hs]
    simp only [StateT.run, bind, StateT.bind, pure]
    generalize hX : emit (H := Collector) (m := Id) (R := Empty) (E := Unit) sliceStart _ b l _ _
      _ _ coll = X
    have he : EmitSpec { core with
        activity := .idle, location := core.location.afterByte c, startedBefore := trivial }
        b l coll (X.1.1, X.2) := by
      rw [← hX]
      exact emit_run _ _ _ _ _ _ _ _ _
    obtain ⟨⟨⟨o, c1, b1⟩, hf, hx⟩, coll1⟩ := X
    rcases he with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩
    · left; exact ⟨h1, ⟨h2, h4, h3⟩, h5⟩
    · right; exact ⟨h1, h2⟩
  | error f =>
    simp only [startS, hs]
    exact ⟨_, Or.inl rfl⟩

theorem lexByte_run2 {version : Version} {st : St} {location : Location} {core : Core}
    (h : Agrees version st location core) (recover : Location → StateT Collector Id Unit)
    (sliceStart : Nat) (b : Array Lexeme) (coll : Collector) (c : UInt8) (hfits : Fits core b) :
    StepSpec version (byteStep version st location c) (location.afterByte c) b coll
      (strip ((V2Batched.lexByte (H := Collector) recover sliceStart core b c hfits).run
        coll)) := by
  obtain ⟨hv, ha, hl⟩ := h
  cases st with
  | idle =>
    simp only [St.activity] at ha
    simp only [V2Batched.lexByte, withEq, ha, byteStep]
    exact lexStart_run2 hv hl sliceStart b coll c hfits
  | token p =>
    simp only [St.activity] at ha
    subst hv hl
    simp only [V2Batched.lexByte, withEq, ha, collector_ws, byteStep]
    cases hadv : advance false p core.location c with
    | pending p' =>
      simp only [advanceS, hadv]
      left
      refine ⟨rfl, ⟨rfl, rfl, rfl⟩, ?_⟩
      show pending core.version coll b.toList = _
      rw [List.append_nil]
    | idle =>
      simp only [advanceS, hadv]
      left
      refine ⟨rfl, ⟨rfl, rfl, rfl⟩, ?_⟩
      show pending core.version coll b.toList = _
      rw [List.append_nil]
    | tokenWith l =>
      simp only [advanceS, hadv]
      simp only [StateT.run, bind, StateT.bind, pure]
      generalize hX : emit (H := Collector) (m := Id) (R := Empty) (E := Unit) sliceStart _ b l
        _ _ _ _ coll = X
      have he : EmitSpec { core with
          activity := .idle, location := core.location.afterByte c, startedBefore := trivial }
          b l coll (X.1.1, X.2) := by
        rw [← hX]
        exact emit_run _ _ _ _ _ _ _ _ _
      obtain ⟨⟨⟨o, c1, b1⟩, hf, hx⟩, coll1⟩ := X
      rcases he with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩
      · left; exact ⟨h1, ⟨h2, h4, h3⟩, h5⟩
      · right; exact ⟨h1, h2⟩
    | tokenBefore l =>
      simp only [advanceS, hadv]
      simp only [StateT.run, bind, StateT.bind, pure]
      generalize hX : emit (H := Collector) (m := Id) (R := Empty) (E := Unit) sliceStart _ b l
        _ _ _ _ coll = X
      have he : EmitSpec { core with activity := .idle, startedBefore := trivial } b l coll
          (X.1.1, X.2) := by
        rw [← hX]
        exact emit_run _ _ _ _ _ _ _ _ _
      obtain ⟨⟨⟨outcome, core1, b1⟩, hf, hx⟩, coll1⟩ := X
      rcases he with ⟨h1, h2, h3, h4, h5⟩ | ⟨h1, h2⟩
      · simp only at h1 h2 h3 h4 h5
        subst h1
        have hs := lexStart_run2 (version := core.version) (location := core.location) h2 h3
          sliceStart b1 coll1 c hf
        simp only [StateT.run] at hs
        cases hss : startStep core.version core.location c with
        | none =>
          rw [hss] at hs
          exact hs
        | some e =>
          obtain ⟨st', ls⟩ := e
          rw [hss] at hs
          rcases hs with ⟨g1, g2, g3⟩ | ⟨g1, g2⟩
          · left
            refine ⟨g1, g2, ?_⟩
            rw [g3, pending_congr_append h5 ls, List.append_assoc]
            rfl
          · right
            refine ⟨g1, ?_⟩
            have := (pending_congr_append h5 ls).symm.trans g2
            simp only [List.append_assoc, List.singleton_append] at this
            exact this
      · obtain ⟨f, hf⟩ := h1
        simp only at hf h2
        cases startStep core.version core.location c with
        | none =>
          rcases hf with hf | hf <;> subst hf
          · exact ⟨f, Or.inl rfl⟩
          · exact ⟨f, Or.inr rfl⟩
        | some e =>
          obtain ⟨st', ls⟩ := e
          right
          refine ⟨?_, ?_⟩
          · rcases hf with hf | hf <;> subst hf
            · exact ⟨f, Or.inl rfl⟩
            · exact ⟨f, Or.inr rfl⟩
          · have := pending_none_append h2 ls
            simp only [List.append_assoc, List.singleton_append] at this
            exact this
    | error f =>
      simp only [advanceS, hadv]
      exact ⟨_, Or.inl rfl⟩

/-! ## The loop over a slice -/

/-- After a failed step, the loop fails. -/
theorem cont_fails (recover : Location → StateT Collector Id Unit) (sliceStart : Nat)
    (slice : ByteSlice) (committed : Nat) (flow : ControlFlow (Located Empty))
    {o : Outcome Empty Unit} (ho : Fails o) (core : Core) (b : Array Lexeme) (next : Nat)
    (hfits : Fits core b)
    (coll : Collector) :
    ∃ f, ((cont (loop2 (H := Collector) (m := Id) recover sliceStart slice) sliceStart slice
      committed flow o core b next hfits).run coll).1.1 = .error f := by
  obtain ⟨f, hf | hf⟩ := ho <;> subst hf
  · simp only [cont, settle, StateT.run_bind]
    obtain ⟨fok, ferr⟩ := flush_batch core b hfits.1 coll
    generalize (flush (H := Collector) (m := Id) (R := Empty) (E := Unit) core b hfits.1).run
      coll = X
      at fok ferr ⊢
    obtain ⟨⟨stop, core1⟩, coll1⟩ := X
    cases hb : handedAll core.version b.toList with
    | none =>
      obtain ⟨g, hg⟩ := ferr hb
      simp only at hg
      subst hg
      exact ⟨g, rfl⟩
    | some hs =>
      obtain ⟨h1, -, -⟩ := fok hs hb
      simp only at h1
      subst h1
      exact ⟨f, rfl⟩
  · exact ⟨f, rfl⟩

/-- What the loop over a slice may give, against the naive lexer's pure run `expected` of the
rest of the slice, after the batch `b`. -/
def FeedsB (version : Version) (expected : Option (St × Location × List Lexeme))
    (b : Array Lexeme) (coll : Collector)
    (result : (Except (Failure Unit) (ControlFlow (Located Empty)) × Core) × Collector) : Prop :=
  match expected with
  | some (st, location, ls) =>
    match pending version coll (b.toList ++ ls) with
    | some hs => result.1.1 = .ok .continue ∧ Agrees version st location result.1.2 ∧
        result.2.handed = hs
    | none => ∃ f, result.1.1 = .error f
  | none => ∃ f, result.1.1 = .error f

theorem lexFrom_run2 {version : Version} (bytes : List UInt8)
    (recover : Location → StateT Collector Id Unit) (sliceStart committed : Nat) (n : Nat) :
    ∀ (index : Nat), bytes.length - index = n → ∀ {st : St} {location : Location} {core : Core},
      Agrees version st location core → ∀ (b : Array Lexeme) (hfits : Fits core b)
      (coll : Collector),
      FeedsB version (feedBytes version st location (bytes.drop index)) b coll
        ((V2Batched.lexFrom (H := Collector) recover sliceStart bytes.toByteArray.toByteSlice
          index committed core b .continue hfits).run coll) := by
  induction n with
  | zero =>
    intro index hn st location core h b hfits coll
    have hle : bytes.length ≤ index := by omega
    have hns : ¬ index < bytes.toByteArray.toByteSlice.size := by
      rw [size_toByteSlice]; omega
    rw [List.drop_eq_nil_of_le hle]
    simp only [feedBytes, FeedsB, List.append_nil]
    rw [V2Batched.lexFrom]
    simp only [hns, dite_false, settleEnd, StateT.run_bind]
    obtain ⟨fok, ferr⟩ := flush_batch core b hfits.1 coll
    generalize (flush (H := Collector) (m := Id) (R := Empty) (E := Unit) core b hfits.1).run
      coll = X
      at fok ferr ⊢
    obtain ⟨⟨stop, core1⟩, coll1⟩ := X
    have hv : core.version = version := h.1
    subst hv
    cases hb : handedAll core.version b.toList with
    | none =>
      obtain ⟨g, hg⟩ := ferr hb
      simp only at hg
      subst hg
      simp only [pending, hb, Option.map_none]
      exact ⟨g, rfl⟩
    | some hs =>
      obtain ⟨h1, ⟨d, h2⟩, h3⟩ := fok hs hb
      simp only at h1 h2 h3
      subst h1 h2
      simp only [pending, hb, Option.map_some]
      exact ⟨rfl, h, h3⟩
  | succ n ih =>
    intro index hn st location core h b hfits coll
    have hlt : index < bytes.length := by omega
    have hs : index < bytes.toByteArray.toByteSlice.size := by
      rw [size_toByteSlice]; exact hlt
    have hl := loop2_lt recover sliceStart bytes.toByteArray.toByteSlice index committed core b
      (.continue : ControlFlow (Located Empty)) hfits hs
    simp only [loop2] at hl
    rw [hl, getElem_toByteSlice, List.drop_eq_getElem_cons hlt]
    simp only [feedBytes, StateT.run_bind]
    generalize bytes[index] = c
    have hb := lexByte_run2 h recover sliceStart b coll c hfits
    generalize (V2Batched.lexByte recover sliceStart core b c hfits).run coll = R at hb ⊢
    obtain ⟨⟨⟨o, core1, b1⟩, hf1⟩, coll1⟩ := R
    simp only [strip] at hb
    simp only [id_bind]
    cases hstep : byteStep version st location c with
    | none =>
      rw [hstep] at hb
      obtain ⟨f, hf⟩ := cont_fails recover sliceStart _ committed .continue hb core1 b1
        (index + 1) hf1 coll1
      exact ⟨f, hf⟩
    | some e =>
      obtain ⟨st', ls⟩ := e
      rw [hstep] at hb
      rcases hb with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · simp only at h1 h2 h3
        subst h1
        rw [cont_next]
        have hrest := ih (index + 1) (by omega) h2 b1 hf1 coll1
        simp only [loop2]
        cases hf : feedBytes version st' (location.afterByte c) (List.drop (index + 1) bytes) with
        | none =>
          rw [hf] at hrest
          exact hrest
        | some e' =>
          obtain ⟨st'', loc'', ls'⟩ := e'
          rw [hf] at hrest
          simp only [FeedsB, Option.map_some] at hrest ⊢
          rw [← List.append_assoc, ← pending_congr_append h3 ls']
          exact hrest
      · obtain ⟨f, hf⟩ := cont_fails recover sliceStart _ committed .continue h1 core1 b1
          (index + 1) hf1 coll1
        cases hfb : feedBytes version st' (location.afterByte c) (List.drop (index + 1) bytes) with
        | none =>
          dsimp only
          rw [hfb]
          exact ⟨f, hf⟩
        | some e' =>
          obtain ⟨st'', loc'', ls'⟩ := e'
          have hp := pending_none_append h2 ls'
          simp only [List.append_assoc] at hp
          dsimp only
          rw [hfb]
          simp only [FeedsB, Option.map_some, hp]
          exact ⟨f, hf⟩

/-! ## The lexer's calls -/

theorem feeds_of_feedsB_ok {ε : Type} {version : Version}
    {e : Option (St × Location × List Lexeme)} {coll coll' : Collector} {core : Core}
    {flow : ControlFlow (Located Empty)}
    (h : FeedsB version e #[] coll ((.ok flow, core), coll')) :
    Feeds (ε := ε) version (ControlFlow.continue : ControlFlow (Located Empty)) e coll
      ((.ok flow, core), coll') := by
  unfold FeedsB at h
  unfold Feeds
  cases e with
  | none => obtain ⟨f, hf⟩ := h; cases hf
  | some e =>
    obtain ⟨st', loc', ls⟩ := e
    simp only [Option.bind_some]
    simp only [pending, List.nil_append] at h
    cases hl : handedAll version ls with
    | none =>
      rw [hl] at h
      obtain ⟨f, hf⟩ := h
      cases hf
    | some hs =>
      rw [hl] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hfl : flow = .continue := Except.ok.inj h1
      subst hfl
      exact ⟨rfl, h2, h3⟩

theorem feeds_of_feedsB_error {ε : Type} {version : Version}
    {e : Option (St × Location × List Lexeme)} {coll coll' coll'' : Collector} {core core' : Core}
    {f : Failure Unit} (err : ε)
    (h : FeedsB version e #[] coll ((.error f, core), coll')) :
    Feeds version (ControlFlow.continue : ControlFlow (Located Empty)) e coll
      ((.error err, core'), coll'') := by
  unfold FeedsB at h
  unfold Feeds
  cases e with
  | none => exact ⟨err, rfl⟩
  | some e =>
    obtain ⟨st', loc', ls⟩ := e
    simp only [Option.bind_some]
    simp only [pending, List.nil_append] at h
    cases hl : handedAll version ls with
    | none => exact ⟨err, rfl⟩
    | some hs =>
      rw [hl] at h
      obtain ⟨h1, -, -⟩ := h
      cases h1

theorem lexSliceStep_run2 {version : Version} {st : St} {location : Location} {core : Core}
    (h : Agrees version st location core) (bytes : List UInt8) (coll : Collector) :
    Feeds version (ControlFlow.continue : ControlFlow (Located Empty))
      (feedBytes version st location bytes) coll
      ((V2Batched.lexSliceStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ())
        bytes.toByteArray.toByteSlice core).run coll) := by
  have hf := lexFrom_run2 bytes (fun _ => pure ()) core.location.offset 0 _ 0 rfl h #[]
    (fits_empty _) coll
  simp only [List.drop_zero] at hf
  have ha : core.activity = st.activity := h.2.1
  cases st with
  | idle =>
    simp only [St.activity] at ha
    simp only [V2Batched.lexSliceStep, StateT.run, ha, StateT.bind, pure, StateT.pure, bind,
      failCall]
    simp only [StateT.run] at hf
    generalize V2Batched.lexFrom (fun _ => pure ()) core.location.offset
      bytes.toByteArray.toByteSlice 0 0 core #[] .continue (fits_empty _) coll = r at hf ⊢
    obtain ⟨⟨res, core'⟩, coll'⟩ := r
    cases res with
    | ok flow => exact feeds_of_feedsB_ok hf
    | error f => exact feeds_of_feedsB_error _ hf
  | token p =>
    simp only [St.activity] at ha
    simp only [V2Batched.lexSliceStep, StateT.run, ha, StateT.bind, pure, StateT.pure, bind,
      failCall]
    simp only [StateT.run] at hf
    generalize V2Batched.lexFrom (fun _ => pure ()) core.location.offset
      bytes.toByteArray.toByteSlice 0 0 core #[] .continue (fits_empty _) coll = r at hf ⊢
    obtain ⟨⟨res, core'⟩, coll'⟩ := r
    cases res with
    | ok flow => exact feeds_of_feedsB_ok hf
    | error f => exact feeds_of_feedsB_error _ hf

theorem lexSlice_eq2 (handler : Collector) (core : Core) (slice : ByteSlice) :
    (V2Batched.lexSlice (⟨handler, core⟩ : V1Naive.Lexer Collector) slice : Id _) =
      match (V2Batched.lexSliceStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ())
          slice core).run handler with
      | ((.ok flow, core), handler) => .ok (flow, { handler, core })
      | ((.error err, _), _) => .error (err, ()) := by
  unfold V2Batched.lexSlice
  simp only [bind, pure, StateT.run]
  rw [show (Recovery.failFast == Recovery.recovering) = false from rfl,
    show LexRecovery.abandon (H := Collector) (m := Id) Recovery.failFast =
      fun _ => StateT.pure () from rfl,
    show LexRecovery.recover (H := Collector) (m := Id) Recovery.failFast =
      fun _ => StateT.pure () from rfl]
  generalize V2Batched.lexSliceStep (H := Collector) false (fun _ => StateT.pure ())
    (fun _ => StateT.pure ()) slice core handler = r
  obtain ⟨⟨res, core'⟩, h'⟩ := r
  cases res <;> rfl

theorem ops2_lexSlice : V2Batched.ops.lexSlice = V2Batched.lexSlice := rfl

theorem ops2_lexEof : V2Batched.ops.lexEof = V1Naive.Lexer.lexEof := rfl

theorem feed_eq2 {version : Version} (slices : List Spec.Lexicon.Chars) :
    ∀ {st : St} {location : Location} (handler : Collector) (core : Core),
      Agrees version st location core →
      feed V2Batched.ops ⟨handler, core⟩ slices =
        (runFrom version st location slices.flatten).bind fun ls =>
          (handedAll version ls).map (handler.handed ++ ·) := by
  induction slices with
  | nil =>
    intro st location handler core h
    have he := lexEofStep_run h handler
    simp only [feed, ops2_lexEof, lexEof_eq, List.flatten_nil, runFrom, feedBytes,
      Option.bind_some, List.nil_append]
    generalize (lexEofStep (H := Collector) false (fun _ => pure ()) (fun _ => pure ())
      core).run handler = r at he ⊢
    obtain ⟨⟨res, core'⟩, handler'⟩ := r
    unfold Ends at he
    cases hx : (endStep st location).bind (handedAll version) with
    | none =>
      rw [hx] at he
      obtain ⟨f, hf⟩ := he
      simp only at hf
      subst hf
      cases hend : endStep st location with
      | none => rfl
      | some ls =>
        rw [hend] at hx
        simp only [Option.bind_some] at hx
        simp [hx]
    | some hs =>
      rw [hx] at he
      obtain ⟨hok, hhs⟩ := he
      simp only at hok hhs
      subst hok
      cases hend : endStep st location with
      | none => rw [hend] at hx; simp at hx
      | some ls =>
        rw [hend] at hx
        simp only [Option.bind_some] at hx
        simp [hx, ← hhs]
        rfl
  | cons slice slices ih =>
    intro st location handler core h
    have hf := lexSliceStep_run2 h slice handler
    simp only [feed, ops2_lexSlice, lexSlice_eq2, List.flatten_cons, runFrom_append]
    generalize (V2Batched.lexSliceStep (H := Collector) false (fun _ => pure ())
      (fun _ => pure ()) slice.toByteArray.toByteSlice core).run handler = r at hf ⊢
    obtain ⟨⟨res, core'⟩, handler'⟩ := r
    unfold Feeds at hf
    cases hx : feedBytes version st location slice with
    | none =>
      rw [hx] at hf
      obtain ⟨f, hf⟩ := hf
      simp only at hf
      subst hf
      rfl
    | some e =>
      obtain ⟨st', location', ls⟩ := e
      rw [hx] at hf
      simp only [Option.bind_some] at hf
      cases hls : handedAll version ls with
      | none =>
        rw [hls] at hf
        obtain ⟨f, hf⟩ := hf
        subst hf
        simp only [Option.bind_some]
        cases runFrom version st' location' slices.flatten with
        | none => rfl
        | some ls' => simp [handedAll_append, hls]
      | some hs =>
        rw [hls] at hf
        obtain ⟨hok, hag, hhs⟩ := hf
        subst hok
        simp only [Option.bind_some]
        rw [ih handler' core' hag]
        cases runFrom version st' location' slices.flatten with
        | none => rfl
        | some ls' =>
          simp only [Option.bind_some, Option.map_some, handedAll_append, hls, hhs]
          cases handedAll version ls' <;> simp [List.append_assoc]

/-- The batched lexer, run by the adapter, gives what the pure run of the whole input gives,
as the consumer records it, however the input is cut into slices. -/
theorem handed_eq_run (version : Spec.Lexicon.Version) (slices : List Spec.Lexicon.Chars) :
    handed V2Batched.ops version slices =
      (run (toVersion version) slices.flatten).bind (handedAll (toVersion version)) := by
  rw [handed, show V2Batched.ops.new = V1Naive.Lexer.new from rfl, V1Naive.Lexer.new, run,
    feed_eq2 (st := .idle) slices { handed := [] } (Core.initial (toVersion version))
    ⟨rfl, rfl, rfl⟩]
  simp only [Core.initial, List.nil_append]
  cases runFrom (toVersion version) .idle Location.initial slices.flatten with
  | none => rfl
  | some ls => simp

end BSmtLib.Proofs.Lexer.V1NaiveV2Batched

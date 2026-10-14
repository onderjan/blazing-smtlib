import BSmtLib.Facts.Proofs.Lexer.Consumers.Boundary

/-!
# The naive lexer's steps with a consumer of the spec

The naive lexer's steps with the adapter's consumer `Answering consumer`, as functions of the
lexer state and the tokens taken (`vRun`, `vByte`, `vBytes`): what the consumer does with a
lexeme handed over alone (`reply`, `consume_single`), the hand-over (`handOverAt_reply`,
`handOverAt_holding`), and the step on a byte in each state of the lexer.
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Lexer.Internal.VNaive

theorem answering_eq {consumer : BSmtLibSpec.Lexer.Consumer}
    (a b : Answering consumer) : a = b := by
  cases a; cases b; rfl

section
variable {g : Token.BatchTag}

theorem switched_eq (consumer : BSmtLibSpec.Lexer.Consumer) (taken : List Handed)
    (cursor : Token.BatchCursor g) :
    (Answering.switched consumer taken cursor).val.version =
        ((consumer.switchTo taken).map toVersion).getD cursor.version ∧
      (Answering.switched consumer taken cursor).val.discardRequested =
        cursor.discardRequested := by
  unfold Answering.switched
  split
  next hs =>
    rw [hs]
    exact ⟨rfl, rfl⟩
  next v hs =>
    simp only [hs, Option.map_some, Option.getD_some]
    split
    · rename_i n hn
      simp only [Token.BatchCursor.setVersion, Except.ok.injEq] at hn
      subst hn
      refine ⟨rfl, ?_⟩; split <;> rfl
    · rename_i hn
      simp [Token.BatchCursor.setVersion] at hn

theorem requests_eq (consumer : BSmtLibSpec.Lexer.Consumer) (taken : List Handed)
    (cursor : Token.BatchCursor g) :
    (Answering.requests consumer taken cursor).val.version =
        ((consumer.switchTo taken).map toVersion).getD cursor.version ∧
      (Answering.requests consumer taken cursor).val.discardRequested =
        (consumer.discards taken || cursor.discardRequested) := by
  obtain ⟨h1, h2⟩ := switched_eq consumer taken cursor
  unfold Answering.requests
  dsimp only
  split
  · rename_i hd
    exact ⟨h1, by rw [hd]; rfl⟩
  · rename_i hd
    exact ⟨h1, by rw [h2]; simp [hd]⟩

end

/-- What the consumer does with the lexeme handed over alone under the version, after the entries
`taken`: its answer, the version after it, whether it has the rest discarded, and the entries
taken after it. -/
def reply (consumer : BSmtLibSpec.Lexer.Consumer) (version : Token.Version) (taken : List Handed)
    (l : Lexeme) :
    Except (Option consumer.Error) (ControlFlow consumer.Result) × Token.Version × Bool × List
        Handed :=
  match lexemeEntry consumer.concrete version l with
  | none => (.error none, version, false, taken)
  | some h =>
    match consumer.answer (taken ++ [h]) with
    | .fail e => (.error (some e),
        ((consumer.switchTo (taken ++ [h])).map toVersion).getD version,
        consumer.discards (taken ++ [h]), taken ++ [h])
    | .break r => (.ok (.break r), ((consumer.switchTo (taken ++ [h])).map toVersion).getD version,
        consumer.discards (taken ++ [h]), taken ++ [h])
    | .continue => (.ok .continue,
        ((consumer.switchTo (taken ++ [h])).map toVersion).getD version,
        consumer.discards (taken ++ [h]), taken ++ [h])

/-- The consumer takes the lexeme handed over alone as `reply` says. -/
theorem consume_single (consumer : BSmtLibSpec.Lexer.Consumer) (version : Token.Version)
    (l : Lexeme)
    (hl : l.Valid) (taken : List Handed) :
    let r := (Answering.consume consumer (Token.BatchCursor.new version (l.batch hl))
      (l.hasNext hl version)).run taken
    (r.1.1, r.1.2.val.version, r.1.2.val.discardRequested, r.2) =
      reply consumer version taken l := by
  intro r
  have hk := entry_batch consumer version l hl
  have hnone : ¬ ((Token.BatchCursor.new version (l.batch hl)).next
      (l.hasNext hl version)).2.1.HasNext :=
    Nat.lt_irrefl _
  have hv : ((Token.BatchCursor.new version (l.batch hl)).next (l.hasNext hl version)).2.1.version =
    version := rfl
  have hd : ((Token.BatchCursor.new version (l.batch hl)).next
    (l.hasNext hl version)).2.1.discardRequested = false := rfl
  have hpk : ((Token.BatchCursor.new version (l.batch hl)).next (l.hasNext hl version)).1 =
    (Token.BatchCursor.new version (l.batch hl)).peek (l.hasNext hl version) := rfl
  simp only [r]
  rw [Answering.consume]
  generalize hn : (Token.BatchCursor.new version (l.batch hl)).next (l.hasNext hl version) = n
    at hnone hv hd hpk
  obtain ⟨token, next, consumed⟩ := n
  dsimp only at hnone hv hd hpk ⊢
  rw [hpk, hk]
  unfold reply
  cases lexemeEntry consumer.concrete version l with
  | none =>
    dsimp only
    exact Prod.ext rfl (Prod.ext hv (Prod.ext hd rfl))
  | some h =>
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, StateT.run_set, pure_bind]
    obtain ⟨h1, h2⟩ := requests_eq consumer (taken ++ [h]) next
    cases ha : consumer.answer (taken ++ [h]) with
    | fail e =>
      refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
      · show (Answering.requests consumer (taken ++ [h]) next).val.version = _
        rw [h1, hv]
      · show (Answering.requests consumer (taken ++ [h]) next).val.discardRequested = _
        rw [h2, hd, Bool.or_false]
    | «break» res =>
      refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
      · show (Answering.requests consumer (taken ++ [h]) next).val.version = _
        rw [h1, hv]
      · show (Answering.requests consumer (taken ++ [h]) next).val.discardRequested = _
        rw [h2, hd, Bool.or_false]
    | «continue» =>
      by_cases hr :
          ((consumer.switchTo (taken ++ [h])).isSome || consumer.discards (taken ++ [h])) = true
      · simp only [hr, ite_true]
        refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
        · show (Answering.requests consumer (taken ++ [h]) next).val.version = _
          rw [h1, hv]
        · show (Answering.requests consumer (taken ++ [h]) next).val.discardRequested = _
          rw [h2, hd, Bool.or_false]
      · simp only [hr, Bool.false_eq_true, ite_false, hnone, dite_false]
        have hs : consumer.switchTo (taken ++ [h]) = none := by
          cases hsw : consumer.switchTo (taken ++ [h]) <;> simp_all
        have hdi : consumer.discards (taken ++ [h]) = false := by
          cases hdd : consumer.discards (taken ++ [h]) <;> simp_all
        refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ rfl))
        · show next.version = _
          rw [hv, hs]; rfl
        · show next.discardRequested = _
          rw [hd, hdi]

section
variable (consumer : BSmtLibSpec.Lexer.Consumer)

/-- A result of the naive lexer's steps with the consumer `Answering consumer`: the result and
the lexer state, and the tokens taken. -/
abbrev VRes (α : Type) := (α × Core) × List Handed

/-- Runs a step of the naive lexer with the consumer `Answering consumer` from the tokens
taken. -/
def vRun {α : Type} (step : StateT (Answering consumer) AnswerM (α × Core))
    (taken : List Handed) : VRes α :=
  let ((r, _), taken) := (step.run {}).run taken
  (r, taken)

theorem vRun_bind {α β : Type} (x : StateT (Answering consumer) AnswerM α)
    (f : α → StateT (Answering consumer) AnswerM (β × Core)) (taken : List Handed) :
    vRun consumer (x >>= f) taken =
      vRun consumer (f ((x.run {}).run taken).1.1) ((x.run {}).run taken).2 := by
  simp only [vRun, StateT.run_bind]
  generalize hx : (x.run {}).run taken = r
  obtain ⟨⟨a, h⟩, taken'⟩ := r
  rw [answering_eq h {}]
  rfl

theorem vRun_pure {α : Type} (a : α × Core) (taken : List Handed) :
    vRun consumer (pure a) taken = (a, taken) := rfl

/-- The core after the lexeme handed over, as `reply` says: the version, and discarding. -/
def coreAfter (core : Core) (l : Lexeme) (version : Token.Version) (discards : Bool) : Core :=
  let core1 := { core with version, depth := depthAfter core.depth l.category }
  if discards then { core1 with activity := .discarding l.end, startedBefore := trivial }
  else core1

/-- The core after the lexeme handed over, at which the consumer failed: the version, and
discarding unless the lexer discards already. -/
def coreAfterError (core : Core) (l : Lexeme) (version : Token.Version) (discards : Bool) : Core :=
  let core1 := { core with version, depth := depthAfter core.depth l.category }
  if discards then
    { core1 with activity := .discarding (core.activity.discardStart l.end)
                 startedBefore := trivial }
  else core1

theorem handOver_run (core : Core) (l : Lexeme) (hl : l.Valid) (taken : List Handed) :
    ((handOver (H := Answering consumer) core l hl).run {}).run taken =
      let r := (Answering.consume consumer (Token.BatchCursor.new core.version (l.batch hl))
        (l.hasNext hl core.version)).run taken
      (((r.1.1, r.1.2.val.discardRequested,
        { core with version := r.1.2.val.version, depth := depthAfter core.depth l.category }),
        {}), r.2) := by
  simp only [handOver, StateT.run_bind, StateT.run_pure]
  rfl

/-- The hand-over of a lexeme to the consumer, as `reply` says, while no result is held. -/
theorem handOverAt_reply (core : Core) (l : Lexeme) (hl : l.Valid) (hh : core.holding = false)
    (taken : List Handed) :
    vRun consumer (handOverAt (H := Answering consumer) core l hl) taken =
      match reply consumer core.version taken l with
      | (.ok .continue, version, discards, taken') =>
        ((.ok none, coreAfter core l version discards), taken')
      | (.ok (.break value), version, discards, taken') =>
        ((.ok (some ⟨value, l.end⟩), { coreAfter core l version discards with holding := true }),
          taken')
      | (.error err, version, discards, taken') =>
        ((.error ⟨.consumer err, Span.newUnchecked l.end l.end, l.end⟩,
          coreAfterError core l version discards), taken') := by
  have hc := consume_single consumer core.version l hl taken
  simp only [handOverAt, hh, Bool.false_eq_true, ite_false]
  rw [vRun_bind, handOver_run]
  dsimp only at hc ⊢
  rw [← hc]
  generalize (Answering.consume consumer (Token.BatchCursor.new core.version (l.batch hl))
    (l.hasNext hl core.version)).run taken = r
  obtain ⟨⟨answer, after, hafter⟩, taken'⟩ := r
  dsimp only
  cases answer with
  | error e =>
    simp only [vRun_pure, coreAfterError]
  | ok flow =>
    cases flow with
    | «continue» => simp only [vRun_pure, coreAfter]
    | «break» v => simp only [vRun_pure, coreAfter]


/-- The naive lexer's step on a byte. -/
def vByte (core : Core) (b : UInt8) (taken : List Handed) :
    VRes (Except (Failure (Option consumer.Error)) (Option (Span.Located consumer.Result))) :=
  vRun consumer (lexByte (H := Answering consumer) (fun _ => pure ()) core b) taken

/-- The naive lexer's loop over bytes, as `lexFrom` over a slice. -/
def vBytes (core : Core) (held : Option (Span.Located consumer.Result)) :
    List UInt8 → List Handed →
      VRes (Except (Failure (Option consumer.Error)) (Option (Span.Located consumer.Result)))
  | [], taken => ((.ok held, core), taken)
  | b :: bs, taken =>
    match vByte consumer core b taken with
    | ((.ok none, core'), taken') => vBytes core' held bs taken'
    | ((.ok (some located), core'), taken') => vBytes core' (some located) bs taken'
    | ((.error f, core'), taken') => ((.error f, core'), taken')

theorem lexFrom_vBytes (bytes : List UInt8) (n : Nat) :
    ∀ (index : Nat), bytes.length - index = n → ∀ (core : Core)
      (held : Option (Span.Located consumer.Result)) (taken : List Handed),
      vRun consumer (lexFrom (H := Answering consumer) (fun _ => pure ())
        bytes.toByteArray.toByteSlice index core held) taken =
        vBytes consumer core held (bytes.drop index) taken := by
  induction n with
  | zero =>
    intro index hn core held taken
    have hle : bytes.length ≤ index := by omega
    rw [lexFrom]
    have hns : ¬ index < bytes.toByteArray.toByteSlice.size := by
      rw [size_toByteSlice]; omega
    simp only [hns, dite_false, List.drop_eq_nil_of_le hle, vBytes]
    rfl
  | succ n ih =>
    intro index hn core held taken
    have hlt : index < bytes.length := by omega
    rw [lexFrom]
    have hs : index < bytes.toByteArray.toByteSlice.size := by
      rw [size_toByteSlice]; exact hlt
    simp only [hs, dite_true, getElem_toByteSlice, List.drop_eq_getElem_cons hlt, vBytes]
    rw [vRun_bind]
    unfold vByte vRun
    generalize ((lexByte (H := Answering consumer) (fun _ => pure ()) core bytes[index]).run
      {}).run taken = r
    obtain ⟨⟨⟨res, core'⟩, h⟩, taken'⟩ := r
    cases res with
    | ok held' =>
      cases held' with
      | none => exact ih (index + 1) (by omega) core' held taken'
      | some located => exact ih (index + 1) (by omega) core' (some located) taken'
    | error f => rfl


theorem isConcrete_answering : Token.Consume.isConcrete
    (H := Answering consumer) = consumer.concrete :=
  rfl

/-- With no token in progress, a byte that starts no lexeme leaves the lexer in the pure run's
state after it. -/
theorem lexStart_none (core : Core) (c : UInt8) (taken : List Handed) {st : St}
    (hs : startStepW core.version consumer.concrete core.location c = some (st, [])) :
    ∃ core', vRun consumer (lexStart (H := Answering consumer) core c) taken =
        ((.ok none, core'), taken) ∧ core'.version = core.version ∧
      core'.activity = st.activity ∧ core'.location = core.location.afterByte c ∧
      core'.holding = core.holding ∧ core'.initialVersion = core.initialVersion := by
  simp only [startStepW] at hs
  simp only [lexStart, isConcrete_answering]
  split at hs
  · rename_i h
    cases hs
    simp only [startS, h]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rename_i p h
    cases hs
    simp only [startS, h]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases hs
  · cases hs


/-- With no token in progress, a byte that fails fails the lexer with a lexical error. -/
theorem lexStart_error (core : Core) (c : UInt8) (taken : List Handed)
    (hs : startStepW core.version consumer.concrete core.location c = none) :
    ∃ f : LexFailure, vRun consumer (lexStart (H := Answering consumer) core c) taken =
      ((.error ⟨.lexical f.kind, f.span, f.location⟩, core), taken) := by
  simp only [startStepW] at hs
  simp only [lexStart, isConcrete_answering]
  split at hs <;> try cases hs
  rename_i f h
  simp only [startS, h]
  exact ⟨f, rfl⟩

/-- The lexer state with nothing in progress, after the byte. -/
def idleAfter (core : Core) (c : UInt8) : Core :=
  { core with activity := .idle, location := core.location.afterByte c, startedBefore := trivial }

/-- With no token in progress, a byte that is a token by itself is handed over at once. -/
theorem lexStart_token (core : Core) (c : UInt8) (taken : List Handed) {l : Lexeme}
    (hs : start core.version consumer.concrete core.location c = .token l) :
    ∃ hl, vRun consumer (lexStart (H := Answering consumer) core c) taken =
      vRun consumer (handOverAt (H := Answering consumer) (idleAfter core c) l hl) taken := by
  simp only [lexStart, isConcrete_answering, startS]
  split
  all_goals
    rename_i heq
    have h := congrArg Subtype.val heq
    simp only [hs] at h
  · cases h
  · cases h
  · rename_i l' hl' _
    cases h
    exact ⟨‹Started.Spec core.location c (Started.token l)›.1, rfl⟩
  · cases h


theorem lexByte_idle (core : Core) (c : UInt8) (taken : List Handed)
    (ha : core.activity = .idle) :
    vByte consumer core c taken =
      vRun consumer (lexStart (H := Answering consumer) core c) taken := by
  simp only [vByte, lexByte, withEq, ha]

theorem lexByte_discarding (core : Core) (c : UInt8) (taken : List Handed) {s : Span.Location}
    (ha : core.activity = .discarding s) :
    ∃ core', vByte consumer core c taken = ((.ok none, core'), taken) ∧
      core'.version = core.version ∧ core'.activity = .discarding s ∧
      core'.location = core.location ∧ core'.holding = core.holding ∧
      core'.initialVersion = core.initialVersion := by
  simp only [vByte, lexByte, withEq, ha]
  exact ⟨_, rfl, rfl, ha, rfl, rfl, rfl⟩

theorem lexByte_pending (core : Core) (c : UInt8) (taken : List Handed) {p p' : Pending}
    (ha : core.activity = .token p)
    (hadv : advance consumer.concrete p core.location c = .pending p') :
    ∃ core', vByte consumer core c taken = ((.ok none, core'), taken) ∧
      core'.version = core.version ∧ core'.activity = .token p' ∧
      core'.location = core.location.afterByte c ∧ core'.holding = core.holding ∧
      core'.initialVersion = core.initialVersion := by
  simp only [vByte, lexByte, withEq, ha, isConcrete_answering, advanceS, hadv]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem lexByte_advance_idle (core : Core) (c : UInt8) (taken : List Handed) {p : Pending}
    (ha : core.activity = .token p)
    (hadv : advance consumer.concrete p core.location c = .idle) :
    ∃ core', vByte consumer core c taken = ((.ok none, core'), taken) ∧
      core'.version = core.version ∧ core'.activity = .idle ∧
      core'.location = core.location.afterByte c ∧ core'.holding = core.holding ∧
      core'.initialVersion = core.initialVersion := by
  simp only [vByte, lexByte, withEq, ha, isConcrete_answering, advanceS, hadv]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem lexByte_tokenWith (core : Core) (c : UInt8) (taken : List Handed) {p : Pending}
    {l : Lexeme} (ha : core.activity = .token p)
    (hadv : advance consumer.concrete p core.location c = .tokenWith l) :
    ∃ hl, vByte consumer core c taken =
      vRun consumer (handOverAt (H := Answering consumer) (idleAfter core c) l hl) taken := by
  have hp := core.started ha
  have hw := advance_tokenWith hadv
  refine ⟨.inl (by rw [hw.1, hw.2, afterByte_offset]; omega), ?_⟩
  simp only [vByte, lexByte, withEq, ha, isConcrete_answering, advanceS, hadv]
  rfl

theorem lexByte_advance_error (core : Core) (c : UInt8) (taken : List Handed) {p : Pending}
    {f : LexFailure} (ha : core.activity = .token p)
    (hadv : advance consumer.concrete p core.location c = .error f) :
    vByte consumer core c taken = ((.error ⟨.lexical f.kind, f.span, f.location⟩, core), taken) :=
        by
  simp only [vByte, lexByte, withEq, ha, isConcrete_answering, advanceS, hadv]
  rfl


/-- The lexer state with nothing in progress, at its location. -/
def idleAt (core : Core) : Core := { core with activity := .idle, startedBefore := trivial }

/-- The lexer state discarding from `s`, at the location it has. -/
def discardingAfter (core : Core) (s : Span.Location) : Core :=
  { core with activity := .discarding s, startedBefore := trivial }

theorem run_of_vRun {α : Type} {step : StateT (Answering consumer) AnswerM (α × Core)}
    {taken taken' : List Handed} {a : α × Core} (h : vRun consumer step taken = (a, taken')) :
    (step.run {}).run taken = ((a, {}), taken') := by
  unfold vRun at h
  generalize (step.run {}).run taken = r at h ⊢
  obtain ⟨⟨a', hh⟩, t⟩ := r
  cases h
  rw [answering_eq hh {}]

/-- A byte that ends the token in progress before it: the token is handed over first. -/
theorem lexByte_tokenBefore (core : Core) (c : UInt8) (taken : List Handed) {p : Pending}
    {l : Lexeme} (ha : core.activity = .token p)
    (hadv : advance consumer.concrete p core.location c = .tokenBefore l) :
    ∃ hl, ∀ {r core2 taken2},
      vRun consumer (handOverAt (H := Answering consumer) (idleAt core) l hl) taken =
        ((r, core2), taken2) →
      vByte consumer core c taken =
        match r with
        | .ok none =>
          match core2.activity with
          | .discarding s => ((.ok none, discardingAfter core2 s), taken2)
          | _ => vRun consumer (lexStart (H := Answering consumer) core2 c) taken2
        | .ok (some located) =>
          match core2.activity with
          | .discarding s => ((.ok (some located), discardingAfter core2 s), taken2)
          | _ =>
            match vRun consumer (lexStart (H := Answering consumer) core2 c) taken2 with
            | ((r, core3), taken3) => ((r.map fun _ => some located, core3), taken3)
        | .error f => ((.error f, core2), taken2) := by
  have hp := core.started ha
  have hb := advance_tokenBefore hadv
  refine ⟨.inl (by rw [hb.1, hb.2]; exact hp), fun {r core2 taken2} hr => ?_⟩
  simp only [vByte, lexByte, withEq, ha, isConcrete_answering, advanceS, hadv]
  rw [vRun_bind]
  rw [show ((handOverAt (H := Answering consumer)
      { core with activity := .idle, startedBefore := trivial } l _).run {}).run taken =
      (((r, core2), {}), taken2) from run_of_vRun consumer hr]
  dsimp only
  cases r with
  | error f => rfl
  | ok held =>
    cases held with
    | none => cases core2.activity <;> rfl
    | some located =>
      cases core2.activity <;> try rfl
      all_goals
        rw [vRun_bind]
        rfl

/-- The span of the error that the lexeme is trailing input. -/
def trailingSpan (l : Lexeme) : Span :=
  Span.newUnchecked l.start l.end

/-- While a result is held, the lexeme handed over is trailing input. -/
theorem handOverAt_holding (core : Core) (l : Lexeme) (hl : l.Valid) (hh : core.holding = true)
    (taken : List Handed) :
    vRun consumer (handOverAt (H := Answering consumer) core l hl) taken =
      ((.error ⟨.lexical .unexpectedTrailingToken, trailingSpan l, l.start⟩, core), taken) := by
  simp only [handOverAt, hh, ite_true]
  rfl

end

end BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps

import BSmtLib.Proofs.X1BatchInCoreX2Contents.Slice

/-!
# The calls of the two lexers on their states

A call of a lexer runs on its state and the consumer's (`InnerM`). Two such computations of the
two lexers are related by `SimI`: from a state whose content buffer fits its array, the first
gives values with a property and a state whose buffer fits, and the second, run from the mapped
state, gives the same values mapped and the mapped state.
-/

namespace BSmtLib.Proofs.X1BatchInCoreX2Contents

open BSmtLib.Proofs.Simulation

section SimI

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- From a state whose buffer fits, `f` gives values with `Q` and a state whose buffer fits, and
`g`, from the mapped state, the values mapped by `ψ` and the mapped state. -/
def SimI {α β : Type} (Q : α → Prop) (ψ : α → β) (f : Lexer.X2Contents.InnerM H m α)
    (g : Lexer.X1BatchInCore.InnerM H m β) : Prop :=
  ∀ c : Core2, Fits c.tokenContent →
    SimH (fun x => Q x.1 ∧ Fits x.2.tokenContent) (fun x => (ψ x.1, coreMap x.2)) (f.run c)
      (g.run (coreMap c))

theorem SimI.pure {α β : Type} {Q : α → Prop} {ψ : α → β} {a : α} {b : β} (hq : Q a)
    (e : ψ a = b) :
    SimI (H := H) (m := m) Q ψ (Pure.pure a) (Pure.pure b) := fun c hc =>
  SimH.pure ⟨hq, hc⟩ (by rw [e])

theorem SimI.bind {α β γ δ : Type} {Q : α → Prop} {Q₂ : γ → Prop} {ψ : α → β} {χ : γ → δ}
    {f : Lexer.X2Contents.InnerM H m α} {g : Lexer.X1BatchInCore.InnerM H m β}
    {k : α → Lexer.X2Contents.InnerM H m γ} {k' : β → Lexer.X1BatchInCore.InnerM H m δ}
    (hf : SimI Q ψ f g) (hk : ∀ x, Q x → SimI Q₂ χ (k x) (k' (ψ x))) :
    SimI Q₂ χ (f >>= k) (g >>= k') := fun c hc => by
  simp only [StateT.run_bind]
  exact SimH.bind (hf c hc) fun x hx => hk x.1 hx.1 x.2 hx.2

theorem SimI.seq {α β γ δ : Type} {Q₂ : γ → Prop} {ψ : α → β} {χ : γ → δ}
    {f : Lexer.X2Contents.InnerM H m α} {g : Lexer.X1BatchInCore.InnerM H m β}
    {k : α → Lexer.X2Contents.InnerM H m γ} {k' : β → Lexer.X1BatchInCore.InnerM H m δ}
    (hf : SimI (fun _ => True) ψ f g) (hk : ∀ x, SimI Q₂ χ (k x) (k' (ψ x))) :
    SimI Q₂ χ (f >>= k) (g >>= k') :=
  SimI.bind hf fun x _ => hk x

omit [LawfulMonad m] in
theorem SimI.ite {α β : Type} {Q : α → Prop} {ψ : α → β} {c c' : Prop} [Decidable c]
    [Decidable c'] (e : c ↔ c') {f₁ f₂ : Lexer.X2Contents.InnerM H m α}
    {g₁ g₂ : Lexer.X1BatchInCore.InnerM H m β} (h₁ : c → SimI Q ψ f₁ g₁)
    (h₂ : ¬c → SimI Q ψ f₂ g₂) : SimI Q ψ (if c then f₁ else f₂) (if c' then g₁ else g₂) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte, e.mp hc]; exact h₁ hc
  · have : ¬c' := fun h => hc (e.mpr h)
    simp only [hc, ↓reduceIte, this]; exact h₂ hc

theorem SimI.mono {α β : Type} {Q Q' : α → Prop} {ψ : α → β}
    {f : Lexer.X2Contents.InnerM H m α} {g : Lexer.X1BatchInCore.InnerM H m β}
    (hq : ∀ x, Q x → Q' x) (hf : SimI Q ψ f g) : SimI Q' ψ f g := fun c hc =>
  SimH.mono (fun _ hx => ⟨hq _ hx.1, hx.2⟩) (hf c hc)

/-- A read of the state, followed by steps on what was read. -/
theorem SimI.get_bind {α β : Type} {Q : α → Prop} {ψ : α → β}
    {k : Core2 → Lexer.X2Contents.InnerM H m α} {k' : Core1 → Lexer.X1BatchInCore.InnerM H m β}
    (hk : ∀ c, Fits c.tokenContent → SimI Q ψ (k c) (k' (coreMap c))) :
    SimI Q ψ (getThe Core2 >>= k) (getThe Core1 >>= k') := fun c hc => by
  simp only [StateT.run_bind]
  have e1 : (getThe Core2 : Lexer.X2Contents.InnerM H m Core2).run c =
      (Pure.pure (c, c) : StateT H m (Core2 × Core2)) := rfl
  have e2 : (getThe Core1 : Lexer.X1BatchInCore.InnerM H m Core1).run (coreMap c) =
      (Pure.pure (coreMap c, coreMap c) : StateT H m (Core1 × Core1)) := rfl
  rw [e1, e2, pure_bind, pure_bind]
  exact hk c hc c hc

/-- A change of the state that the map carries over. -/
theorem SimI.modify {f : Core2 → Core2} {g : Core1 → Core1}
    (e : ∀ c, Fits c.tokenContent → g (coreMap c) = coreMap (f c))
    (hf : ∀ c, Fits c.tokenContent → Fits (f c).tokenContent) :
    SimI (H := H) (m := m) (fun _ => True) id (modifyThe Core2 f) (modifyThe Core1 g) :=
  fun c hc => by
    show SimH _ _ (Pure.pure (PUnit.unit, f c)) (Pure.pure (PUnit.unit, g (coreMap c)))
    exact SimH.pure ⟨trivial, hf c hc⟩ (by rw [e c hc])

/-- A state set by both lexers, the second's the first's mapped. -/
theorem SimI.set {c₂ : Core2} {c₁ : Core1} (e : c₁ = coreMap c₂) (hc : Fits c₂.tokenContent) :
    SimI (H := H) (m := m) (fun _ => True) id (MonadStateOf.set c₂) (MonadStateOf.set c₁) :=
  fun c _ => by
    show SimH _ _ (Pure.pure (PUnit.unit, c₂)) (Pure.pure (PUnit.unit, c₁))
    exact SimH.pure ⟨trivial, hc⟩ (by rw [e])

/-- An action of the consumer, the same in both lexers. -/
theorem SimI.lift {α : Type} (a : StateT H m α) :
    SimI (fun _ => True) id (monadLift a : Lexer.X2Contents.InnerM H m α)
      (monadLift a : Lexer.X1BatchInCore.InnerM H m α) := fun c hc => by
  intro h
  refine ⟨(fun x => ⟨((x.1, c), x.2), trivial, hc⟩) <$> a.run h, ?_, ?_⟩
  · show ((StateT.lift a : StateT Core2 (StateT H m) α).run c).run h = _
    simp
  · show ((StateT.lift a : StateT Core1 (StateT H m) α).run (coreMap c)).run h = _
    simp

end SimI

/-! ## The helpers that each lexer defines for itself -/

/-- What skipping goes through, in the second lexer for the first. -/
def skipMap (s : Lexer.X2Contents.Skipping) : Lexer.X1BatchInCore.Skipping :=
  { skip := s.skip, depth := s.depth, line := s.line, lineStart := s.lineStart }

/-- Decides the condition of a test of the byte in both lexers. -/
local macro "decide_cond " c:term : tactic =>
  `(tactic| (by_cases hcond : $c <;> simp only [hcond, ↓reduceIte, Bool.false_eq_true]))

set_option hygiene false in
/-- Ends a step of skipping in both lexers: with the same result, or with the next step from
mapped states, which is the induction hypothesis `ih`. -/
local macro "skip_finish" : tactic => `(tactic| first
  | rfl
  | (split <;> (rw [← ih _ (by omega) _ _ rfl]; rfl))
  | (rw [← ih _ (by omega) _ _ rfl]; rfl))

set_option hygiene false in
/-- The tests of a byte outside strings, quoted symbols and comments. -/
local macro "plain_tests" : tactic => `(tactic| (
  decide_cond (bytes[index] == byte! '"') = true
  · skip_finish
  decide_cond (bytes[index] == byte! '|') = true
  · skip_finish
  decide_cond (Lexer.isDelimiter bytes[index] && depth == 0) = true
  · skip_finish
  decide_cond (bytes[index] == byte! ';') = true
  · skip_finish
  decide_cond (bytes[index] == byte! '(') = true
  · skip_finish
  decide_cond (bytes[index] == byte! ')') = true
  · decide_cond (depth - 1 == 0) = true <;> skip_finish
  · skip_finish))

theorem skipBytes_eq (bytes : ByteSlice) (legacy : Bool) (offset : Nat) :
    ∀ k index (skipping : Lexer.X2Contents.Skipping), bytes.size - index = k →
      Lexer.X1BatchInCore.skipBytes bytes legacy offset index (skipMap skipping) =
        Prod.map id skipMap (Lexer.X2Contents.skipBytes bytes legacy offset index skipping) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro index skipping hk
  rw [Lexer.X1BatchInCore.skipBytes.eq_def, Lexer.X2Contents.skipBytes.eq_def]
  split
  · rename_i h
    obtain ⟨skip, depth, line, lineStart⟩ := skipping
    conv => lhs; zeta
    conv => rhs; arg 2; zeta
    cases skip <;> simp only [skipMap]
    · plain_tests
    · plain_tests
    · plain_tests
    · decide_cond (bytes[index] == byte! '"') = true
      · skip_finish
      decide_cond (bytes[index] == byte! '\\' && legacy) = true <;> skip_finish
    · skip_finish
    · decide_cond (bytes[index] == byte! '|') = true <;> skip_finish
    · decide_cond (bytes[index] == byte! '\n' || bytes[index] == byte! '\r') = true <;>
        skip_finish
  · rename_i h
    rfl

theorem countLineFeeds_loop_eq (bytes : ByteSlice) :
    ∀ k i count afterLast, bytes.size - i = k →
      Lexer.X1BatchInCore.countLineFeeds.loop bytes i count afterLast =
        Lexer.X2Contents.countLineFeeds.loop bytes i count afterLast := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro i count afterLast hk
  rw [Lexer.X1BatchInCore.countLineFeeds.loop.eq_def, Lexer.X2Contents.countLineFeeds.loop.eq_def]
  by_cases h : i < bytes.size
  · simp only [h, dite_true]
    split <;> exact ih _ (by omega) _ _ _ rfl
  · simp only [h, dite_false]

theorem countLineFeeds_eq (bytes : ByteSlice) :
    Lexer.X1BatchInCore.countLineFeeds bytes = Lexer.X2Contents.countLineFeeds bytes :=
  countLineFeeds_loop_eq bytes _ 0 0 none rfl

/-! ## The calls -/

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]

omit [Consume H m R E] in
theorem reset_sim :
    SimI (H := H) (m := m) (fun _ => True) id Lexer.X2Contents.reset Lexer.X1BatchInCore.reset := by
  unfold Lexer.X2Contents.reset Lexer.X1BatchInCore.reset
  exact SimI.modify (fun c _ => by simp only [coreMap, contentBytes_clear]) fun c _ => fits_clear _

omit [Consume H m R E] in
theorem executeStep_sim
    {step : Lexer.X2Contents.InnerM H m (Except (Lexer.Failure E) (ControlFlow R))}
    {step' : Lexer.X1BatchInCore.InnerM H m (Except (Lexer.Failure E) (ControlFlow R))}
    (h : SimI (fun _ => True) id step step') :
    SimI (fun _ => True) id (Lexer.X2Contents.executeStep step)
      (Lexer.X1BatchInCore.executeStep step') := by
  unfold Lexer.X2Contents.executeStep Lexer.X1BatchInCore.executeStep
  refine SimI.bind h fun x _ => ?_
  cases x with
  | error f => exact SimI.pure trivial rfl
  | ok flow =>
    cases flow with
    | «continue» => exact SimI.pure trivial rfl
    | «break» r => exact SimI.get_bind fun c _ => SimI.pure trivial rfl

omit [Consume H m R E] in
theorem failCall_sim (abandon : Location → StateT H m Unit) (failure : Lexer.Failure E)
    (atEnd : Bool) :
    SimI (fun _ => True) id (Lexer.X2Contents.failCall abandon failure atEnd)
      (Lexer.X1BatchInCore.failCall abandon failure atEnd) := by
  unfold Lexer.X2Contents.failCall Lexer.X1BatchInCore.failCall
  refine SimI.get_bind fun c _ => ?_
  refine SimI.ite Iff.rfl (fun _ => SimI.pure trivial rfl) fun _ => ?_
  refine SimI.seq (SimI.modify (fun c _ => (coreMap_resumeAt _ _ _).symm)
    fun _ _ => fits_clear _) fun _ => ?_
  refine SimI.seq (SimI.lift _) fun _ => ?_
  refine SimI.seq (SimI.modify (fun _ _ => rfl) fun _ h => h) fun _ => ?_
  exact SimI.pure trivial rfl

omit [Consume H m R E] in
theorem discardBytes_sim (bytes : ByteSlice) :
    SimI (H := H) (m := m) (fun _ => True) id (Lexer.X2Contents.discardBytes bytes)
      (Lexer.X1BatchInCore.discardBytes bytes) := by
  unfold Lexer.X2Contents.discardBytes Lexer.X1BatchInCore.discardBytes
  refine SimI.modify (fun c _ => ?_) fun c hc => ?_
  · simp only [countLineFeeds_eq]
    obtain ⟨⟨lf, al⟩, h⟩ : ∃ p, Lexer.X2Contents.countLineFeeds bytes = p := ⟨_, rfl⟩
    cases al <;> simp only [h] <;> rfl
  · obtain ⟨⟨lf, al⟩, h⟩ : ∃ p, Lexer.X2Contents.countLineFeeds bytes = p := ⟨_, rfl⟩
    cases al <;> simp only [h] <;> exact hc

omit [Consume H m R E] in
theorem skipSlice_sim (slice : ByteSlice) (skip : Lexer.RecoveryState) :
    SimI (H := H) (m := m) (fun _ => True) id (Lexer.X2Contents.skipSlice slice skip)
      (Lexer.X1BatchInCore.skipSlice slice skip) := by
  unfold Lexer.X2Contents.skipSlice Lexer.X1BatchInCore.skipSlice
  refine SimI.get_bind fun c hc => ?_
  refine SimI.ite Iff.rfl (fun _ => SimI.pure trivial rfl) fun _ => ?_
  have e : Lexer.X1BatchInCore.skipBytes slice ((coreMap c).version == .v2_0) (coreMap c).offset 0
      { skip := if (skip == .boundary) = true then .plain else skip,
        depth := (coreMap c).consumedDepth, line := (coreMap c).line,
        lineStart := (coreMap c).lineStart } =
      Prod.map id skipMap (Lexer.X2Contents.skipBytes slice (c.version == .v2_0) c.offset 0
        { skip := if (skip == .boundary) = true then .plain else skip, depth := c.consumedDepth,
          line := c.line, lineStart := c.lineStart }) :=
    skipBytes_eq slice (c.version == .v2_0) c.offset _ 0
      { skip := if (skip == .boundary) = true then .plain else skip, depth := c.consumedDepth,
        line := c.line, lineStart := c.lineStart } rfl
  conv => arg 3; zeta
  conv => arg 4; zeta
  rw [e]
  generalize Lexer.X2Contents.skipBytes slice (c.version == .v2_0) c.offset 0
    { skip := if (skip == .boundary) = true then .plain else skip, depth := c.consumedDepth,
      line := c.line, lineStart := c.lineStart } = r
  obtain ⟨p, s⟩ := r
  cases p
  all_goals
    refine SimI.seq (SimI.set rfl hc) fun _ => ?_
    exact SimI.pure trivial rfl

theorem coreMap_recoveryState (c : Core2) : (coreMap c).recoveryState = c.recoveryState := rfl

variable (hblind : ContentBlind H m R E)
include hblind

theorem lexSliceInner_simI (slice : ByteSlice) :
    SimI (fun _ => True) id
      (Lexer.X2Contents.lexSliceInner (H := H) (m := m) (R := R) (E := E) slice)
      (Lexer.X1BatchInCore.lexSliceInner slice) := fun c hc =>
  SimH.mono (fun _ h => ⟨trivial, h⟩) (lexSliceInner_sim hblind slice c hc)

set_option hygiene false in
/-- What both lexers do with the slice, or with its rest after the recovery: lex it, then turn a
failure into the error, or discard the rest of the slice after a break. It names the consumer's
`abandon` and the proof's `hblind`. -/
local macro "slice_lex" : tactic => `(tactic| (
  refine SimI.get_bind fun c _ => ?_
  refine SimI.bind (executeStep_sim (lexSliceInner_simI hblind _)) fun x _ => ?_
  cases x with
  | error f =>
    exact SimI.bind (failCall_sim abandon f false) fun _ _ => SimI.pure trivial rfl
  | ok flow =>
    cases flow with
    | «continue» => exact SimI.pure trivial rfl
    | «break» l =>
      refine SimI.seq (SimI.modify (fun _ _ => rfl) fun _ h => h) fun _ => ?_
      exact SimI.seq (discardBytes_sim _) fun _ => SimI.pure trivial rfl))

theorem lexSliceStep_sim (abandon recover : Location → StateT H m Unit) (slice : ByteSlice) :
    SimI (fun _ => True) id (Lexer.X2Contents.lexSliceStep (R := R) (E := E) abandon recover slice)
      (Lexer.X1BatchInCore.lexSliceStep abandon recover slice) := by
  unfold Lexer.X2Contents.lexSliceStep Lexer.X1BatchInCore.lexSliceStep
  refine SimI.get_bind fun c _ => ?_
  refine SimI.ite Iff.rfl (fun _ => SimI.seq (discardBytes_sim slice) fun _ =>
    SimI.pure trivial rfl) fun _ => ?_
  refine SimI.get_bind fun c' _ => ?_
  rw [coreMap_recoveryState]
  conv => arg 3; zeta
  conv => arg 4; zeta
  generalize c'.recoveryState = rs
  cases rs with
  | none => slice_lex
  | some skip =>
    refine SimI.ite Iff.rfl (fun _ => SimI.pure trivial rfl) fun _ => ?_
    refine SimI.bind (skipSlice_sim slice skip) fun x _ => ?_
    cases x with
    | none => exact SimI.pure trivial rfl
    | some skipped =>
      refine SimI.seq (SimI.modify (fun _ _ => rfl) fun _ h => h) fun _ => ?_
      refine SimI.get_bind fun c _ => ?_
      refine SimI.seq (SimI.lift _) fun _ => ?_
      slice_lex

theorem lexEofInner_sim :
    SimI (fun _ => True) id (Lexer.X2Contents.lexEofInner (H := H) (m := m) (R := R) (E := E))
      Lexer.X1BatchInCore.lexEofInner := by
  intro c hc
  obtain ⟨version, initialVersion, state, discard, recovers, consumedDepth, lexedDepth,
    recoveryState, tokenStart, tokenContent, offset, base, line, lineStart, batch, tokenStarted,
    batchEnded⟩ := c
  show SimH _ _ (Lexer.X2Contents.lexEofInner _) (Lexer.X1BatchInCore.lexEofInner _)
  cases state
  all_goals
    unfold Lexer.X2Contents.lexEofInner Lexer.X1BatchInCore.lexEofInner
    dsimp only
    refine SimH.bind (SimH.ofSimF (I := BFits) (P := BFits) (Q := fun _ => BFits) (ψ := id)
      (φ := boundMap) ?_ _ hc) fun x hx => ?_
    rotate_left
    · -- what the end of the input returns
      obtain ⟨r, core⟩ := x
      cases r with
      | ok u => exact SimH.pure ⟨trivial, hx.1 u rfl⟩ rfl
      | error i =>
        obtain ⟨result, location, after⟩ := i
        cases result with
        | error cause => exact SimH.pure ⟨trivial, hx.2 _ rfl⟩ rfl
        | ok stop => cases stop <;> exact SimH.pure ⟨trivial, hx.2 _ rfl⟩ rfl
    -- the token in progress is finished, then the end-of-file token is handed over
    refine SimF.bind (Q := fun _ => BFits) (ψ := id)
      (SimF.tryCatch (Q := fun _ => BFits) (ψ := id) ?_ fun e => ?_) fun _ => ?_
    rotate_left
    · obtain ⟨result, location, after⟩ := e
      cases result with
      | error cause => exact SimF.throw (fun _ h => h) _
      | ok stop =>
        cases stop with
        | relex => exact SimF.pure (fun _ h => h) rfl
        | finished r => exact SimF.throw (fun _ h => h) _
    · refine SimF.bind (startToken_sim _ _ _ _ _) fun y => ?_
      obtain ⟨location, hl⟩ := y
      exact handOverEof_sim hblind location
  · exact SimF.pure (fun _ h => h) rfl
  · exact finishNumeral_sim hblind _ _ _ _ _
  · exact finishDecimal_sim hblind _ _ _ _ _ _
  · exact fail_sim id _ _ _
  · exact finishDigitRun_sim hblind _ _ _ _ _ _ _ _ _
  · exact finishDigitRun_sim hblind _ _ _ _ _ _ _ _ _
  · exact fail_sim id _ _ _
  · exact finishStringLiteral_sim hblind _ _ _ _ _
  · exact fail_sim id _ _ _
  · exact finishSimpleSymbol_sim hblind _ _ _ _ _
  · exact fail_sim id _ _ _
  · exact finishKeyword_sim hblind _ _ _ _ _ _
  · exact SimF.bind consumes_sim fun _ => SimF.ite Iff.rfl
      (fun _ => sinkStored_sim hblind _ _ _ _ _ _ _ _) fun _ => SimF.pure (fun _ h => h) rfl
  · exact sinkStored_sim hblind _ _ _ _ _ _ _ _
  · exact sinkStored_sim hblind _ _ _ _ _ _ _ _

set_option hygiene false in
/-- What both lexers do at the end of the input, after the recovery if there was one: the
end-of-input step, then the reset or the error. It names the consumer's `abandon` and the
proof's `hblind`. -/
local macro "eof_rest" : tactic => `(tactic| (
  refine SimI.bind (executeStep_sim (lexEofInner_sim hblind)) fun x _ => ?_
  cases x with
  | ok flow => exact SimI.seq reset_sim fun _ => SimI.pure trivial rfl
  | error f =>
    exact SimI.ite Iff.rfl (fun _ => SimI.seq reset_sim fun _ => SimI.pure trivial rfl) fun _ =>
      SimI.bind (failCall_sim abandon f true) fun _ _ => SimI.pure trivial rfl))

theorem lexEofStep_sim (abandon recover : Location → StateT H m Unit) :
    SimI (fun _ => True) id (Lexer.X2Contents.lexEofStep (R := R) (E := E) abandon recover)
      (Lexer.X1BatchInCore.lexEofStep abandon recover) := by
  unfold Lexer.X2Contents.lexEofStep Lexer.X1BatchInCore.lexEofStep
  refine SimI.get_bind fun c _ => ?_
  refine SimI.ite Iff.rfl (fun _ => SimI.seq reset_sim fun _ => SimI.pure trivial rfl)
    fun _ => ?_
  refine SimI.get_bind fun c' _ => ?_
  rw [coreMap_recoveryState]
  conv => arg 3; zeta
  conv => arg 4; zeta
  refine SimI.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimI.seq (SimI.modify (fun _ _ => rfl) fun _ h => h) fun _ => ?_
    refine SimI.get_bind fun _ _ => ?_
    refine SimI.seq (SimI.lift _) fun _ => ?_
    eof_rest
  · eof_rest

end

end BSmtLib.Proofs.X1BatchInCoreX2Contents

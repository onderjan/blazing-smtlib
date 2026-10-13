import BSmtLib.Proofs.WRustPortX1BatchInCore.Normal

/-!
# The steps per state

The steps for a token in progress are the same code over the operations, which hand the
finished tokens over (`Finish`), and the loop of the normal state shown alike before. The steps
run inside a slice, where the simulation is strict.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)
open BSmtLib.Proofs.Lexer.Slice (get? get runEnd runEndAll)
open BSmtLib.Proofs.Lexer.WRustPort (Ops)

/-- A change of the content buffer of both runs, from states with `SRb true`. -/
local macro "content_step " lemma:term:max : tactic => `(tactic|
  refine SimR.seq (SimR.of_srl fun l ls => SimR.post (Q' := fun _ _ => SRb true)
    (fun _ _ s t h => ⟨h.1.1, h.2⟩) ($lemma l ls)) ?_)

set_option hygiene false in
/-- The run of a string literal, from states with `SRb true`: a line feed or a quote goes on
with the loop by `ih`, any other byte that ends the run fails. The names are those of
`lexStringLiteralFrom_sim`; `P` is where the run starts. -/
local macro "string_run " P:term:max : tactic => `(tactic| (
  have hle := Lexer.Slice.le_runEnd input $P Lexer.RUN_STRING_PLAIN
  split
  · rename_i c2 h3
    have := Lexer.Slice.lt_size_of_get? h3
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (markLineFeedAt_sim _ _) ?_
      content_step (fun l ls => extendContent_sim l ls _ _ _ _)
      exact ih _ (by omega) _ rfl _ _
    · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · content_step (fun l ls => extendContent_sim l ls _ _ _ _)
        content_step (fun l ls => setTokenState_sim l ls _ _ _ _ _)
        exact ih _ (by omega) _ rfl _ _
      · exact SimR.of_srl fun l ls => errorAt_sim l ls _ _ _
  · refine SimR.of_srl fun l ls => ?_
    refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩))

set_option hygiene false in
/-- The end of a run of a string literal in the legacy mode: whether the byte that ends it goes
into the content, the run, the byte, and the loop by `ih`. The names are those of
`lexStringLiteralLegacy_sim`. -/
local macro "legacy_tail" : tactic => `(tactic| (
  refine SimR.bind_eq (P' := SRb true) (SimR.pure fun s t h => ⟨rfl, h⟩) fun ar => ?_
  content_step (fun l ls => extendContent_sim l ls _ _ _ _)
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · content_step (fun l ls => pushContent_sim l ls _ _)
    exact ih _ (by omega) _ rfl _ _
  · exact ih _ (by omega) _ rfl _ _))

set_option hygiene false in
/-- The run of a string literal in the legacy mode from the index `P`, from states with
`SRb true`. -/
local macro "legacy_run " P:term:max : tactic => `(tactic| (
  have hle := Lexer.Slice.le_runEndAll input $P (Lexer.RUN_STRING_PLAIN ||| Lexer.RUN_QUOTED_PLAIN)
  split
  · rename_i _ c2 hc2 h3
    have := Lexer.Slice.lt_size_of_get? hc2
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (markLineFeedAt_sim _ _) ?_
      legacy_tail
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · content_step (fun l ls => setTokenState_sim l ls _ _ _ _ _)
      legacy_tail
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · content_step (fun l ls => setTokenState_sim l ls _ _ _ _ _)
      legacy_tail
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · legacy_tail
    · simp only [bind_assoc, throw_bind]
      exact SimR.of_srl fun l ls => errorAt_sim l ls _ _ _
  · refine SimR.of_srl fun l ls => ?_
    refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩))

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H R E]
  [∀ batch, ConsumeFrom H (BatchCursor batch) m]
  {floor : Option Nat} {low : Nat} {o₁ o₂ : Ops H m R E}
  {LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop}

/-- What a step gives back: the same index, from states with `SRb true`. -/
abbrev StepQ {α β : Type} (val : α → Nat) (val' : β → Nat) (a : α) (b : β)
    (s t : St floor low) : Prop :=
  val a = val' b ∧ SRb true s t

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
/-- A finished token, with the batches in the states left as any. -/
theorem fin {α β : Type} {strict : Bool} {l ls : Nat} {P : St floor low → St floor low → Prop}
    {f : Lexer.WRustPort.LexM H m R E floor low α} {g : Lexer.WRustPort.LexM H m R E floor low β}
    (h : LSim strict P (fun _ _ => SREb strict l ls) f g) :
    LSim strict P (fun _ _ => SRLb strict l ls) f g :=
  SimR.post (fun _ _ _ _ h => ⟨h.1.1, h.2⟩) h

/-- The end of a step that finished its token: the normal state, and the index. -/
local macro "finished" : tactic => `(tactic| (
  refine SimR.seq (setNormal_sim _ _ _) ?_
  exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩))

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexFractionFrom_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (tokenStart : Location) (base : Nat) (h) :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexFractionFrom (ops := o₁) input start tokenStart base h)
      (Lexer.WRustPort.lexFractionFrom (ops := o₂) input start tokenStart base h) := by
  unfold Lexer.WRustPort.lexFractionFrom
  refine SimR.of_srl fun l ls => ?_
  refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
  refine SimR.dite Iff.rfl (fun _ _ => ?_) fun _ _ => ?_
  · refine SimR.seq (fin (finishDecimal_sim ho l ls _ _ _ _ _)) ?_
    finished
  · refine SimR.seq (setTokenState_sim l ls _ _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexNumeralOrDecimal_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (start : Nat) (tokenStart : Location) (base : Nat) (h) :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexNumeralOrDecimal (ops := o₁) input start tokenStart base h)
      (Lexer.WRustPort.lexNumeralOrDecimal (ops := o₂) input start tokenStart base h) := by
  unfold Lexer.WRustPort.lexNumeralOrDecimal
  refine SimR.of_srl fun l ls => ?_
  refine getCore_bind_P fun s t hs => ?_
  simp only [throw_bind]
  refine SimR.ite (by simp only [hs.1.1.tokenContent]) (fun _ => errorAt_sim l ls _ _ _) fun _ => ?_
  refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
  split
  · rename_i next h1
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (pushContent_sim l ls _ _) ?_
      refine SimR.bind (SimR.pre (fun s t h => ⟨h.1.1, h.2⟩)
        (lexFractionFrom_sim ho input _ tokenStart base _)) fun x y => ?_
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      exact SimR.pure fun s t h => h
    · refine SimR.seq (expectDelimiter_sim l ls _ _) ?_
      refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
      finished
  · exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexBaseSelection_sim (input : ByteSlice) (start : Nat) (hstart)
    (tokenStart : Location) (h) :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexBaseSelection input start hstart tokenStart h)
      (Lexer.WRustPort.lexBaseSelection input start hstart tokenStart h) := by
  unfold Lexer.WRustPort.lexBaseSelection
  refine SimR.of_srl fun l ls => ?_
  simp only [throw_bind]
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimR.seq (setTokenState_sim l ls _ _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimR.seq (setTokenState_sim l ls _ _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  · exact errorAt_sim l ls _ _ _

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexDigitRun_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (run : Lexer.DigitRun) (tokenStart : Location) (base : Nat) (h) :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexDigitRun (ops := o₁) input start run tokenStart base h)
      (Lexer.WRustPort.lexDigitRun (ops := o₂) input start run tokenStart base h) := by
  unfold Lexer.WRustPort.lexDigitRun
  refine SimR.of_srl fun l ls => ?_
  refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
  refine SimR.dite Iff.rfl (fun _ _ => ?_) fun _ _ => ?_
  · refine SimR.seq (fin (finishDigitRun_sim ho l ls _ _ _ _ _ _)) ?_
    finished
  · exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexSimpleSymbol_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (tokenStart : Location) (base : Nat) (h) :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexSimpleSymbol (ops := o₁) input start tokenStart base h)
      (Lexer.WRustPort.lexSimpleSymbol (ops := o₂) input start tokenStart base h) := by
  unfold Lexer.WRustPort.lexSimpleSymbol Lexer.WRustPort.finishSimpleSymbol
  refine SimR.of_srl fun l ls => ?_
  refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
  refine SimR.dite Iff.rfl (fun _ _ => ?_) fun _ _ => ?_
  · refine SimR.seq (expectDelimiter_sim l ls _ _) ?_
    refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
    finished
  · exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexKeyword_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (tokenStart : Location) (base : Nat) (h) :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexKeyword (ops := o₁) input start tokenStart base h)
      (Lexer.WRustPort.lexKeyword (ops := o₂) input start tokenStart base h) := by
  unfold Lexer.WRustPort.lexKeyword
  refine SimR.of_srl fun l ls => ?_
  refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
  refine SimR.dite Iff.rfl (fun _ _ => ?_) fun _ _ => ?_
  · refine SimR.seq (fin (finishKeyword_sim ho l ls _ _ _ _ _)) ?_
    finished
  · exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexQuotedSymbolClosed_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (start : Nat) (hstart) (tokenStart : Location) (base : Nat) (h) :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexQuotedSymbolClosed (ops := o₁) input start hstart tokenStart base h)
      (Lexer.WRustPort.lexQuotedSymbolClosed (ops := o₂) input start hstart tokenStart base h) := by
  unfold Lexer.WRustPort.lexQuotedSymbolClosed
  refine SimR.of_srl fun l ls => ?_
  refine SimR.seq (expectDelimiter_sim l ls _ _) ?_
  refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
  finished

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexWhitespace_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (origin : Nat)
    (tokenStart : Location) (base : Nat) :
    ∀ k (start : Nat), input.size - start = k → ∀ horigin hstart h,
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexWhitespace (ops := o₁) input start origin horigin hstart tokenStart
        base h)
      (Lexer.WRustPort.lexWhitespace (ops := o₂) input start origin horigin hstart tokenStart
        base h) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro start hk horigin hstart h
  rw [Lexer.WRustPort.lexWhitespace.eq_def (ops := o₁),
    Lexer.WRustPort.lexWhitespace.eq_def (ops := o₂)]
  dsimp only
  have hle := Lexer.Slice.le_runEnd input start Lexer.RUN_NON_LF_WHITESPACE
  split
  · rename_i c h1
    have := Lexer.Slice.lt_size_of_get? h1
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (markLineFeedAt_sim _ _) ?_
      content_step (fun l ls => extendContent_sim l ls _ _ _ _)
      exact ih _ (by omega) _ rfl _ _ _
    · unfold Lexer.WRustPort.finishWhitespace
      refine SimR.of_srl fun l ls => ?_
      refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
      refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
      finished
  · refine SimR.of_srl fun l ls => ?_
    refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexQuotedSymbol_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (origin : Nat)
    (tokenStart : Location) (base : Nat) :
    ∀ k (consumed : Nat), input.size - consumed = k → ∀ horigin hconsumed h,
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexQuotedSymbol (ops := o₁) input consumed origin horigin hconsumed
        tokenStart base h)
      (Lexer.WRustPort.lexQuotedSymbol (ops := o₂) input consumed origin horigin hconsumed
        tokenStart base h) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro consumed hk horigin hconsumed h
  rw [Lexer.WRustPort.lexQuotedSymbol.eq_def (ops := o₁),
    Lexer.WRustPort.lexQuotedSymbol.eq_def (ops := o₂)]
  dsimp only
  have hle := Lexer.Slice.le_runEnd input consumed Lexer.RUN_QUOTED_PLAIN
  split
  · rename_i c h1
    have := Lexer.Slice.lt_size_of_get? h1
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.of_srl fun l ls => ?_
      refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
      split
      · refine SimR.seq (expectDelimiter_sim l ls _ _) ?_
        refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
        finished
      · refine SimR.seq (setTokenState_sim l ls _ _ _ _ _) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · exact SimR.of_srl fun l ls => errorAt_sim l ls _ _ _
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (markLineFeedAt_sim _ _) ?_
      content_step (fun l ls => extendContent_sim l ls _ _ _ _)
      exact ih _ (by omega) _ rfl _ _ _
    · exact SimR.of_srl fun l ls => errorAt_sim l ls _ _ _
  · refine SimR.of_srl fun l ls => ?_
    refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexStringLiteralFrom_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (origin : Nat) (tokenStart : Location) (base : Nat) :
    ∀ k (consumed : Nat), input.size - consumed = k → ∀ horigin h,
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexStringLiteralFrom (ops := o₁) input consumed origin horigin tokenStart
        base h)
      (Lexer.WRustPort.lexStringLiteralFrom (ops := o₂) input consumed origin horigin tokenStart
        base h) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro consumed hk horigin h
  rw [Lexer.WRustPort.lexStringLiteralFrom.eq_def (ops := o₁),
    Lexer.WRustPort.lexStringLiteralFrom.eq_def (ops := o₂)]
  dsimp only
  split
  · rename_i _ c hc h1
    have := Lexer.Slice.lt_size_of_get? hc
    refine getCore_bind_P fun s t hs => ?_
    refine SimR.ite (by rw [hs.1.state]) (fun _ => ?_) fun _ => ?_
    · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · unfold Lexer.WRustPort.finishStringLiteral
        refine SimR.of_srl fun l ls => ?_
        refine SimR.seq (expectDelimiter_sim l ls _ _) ?_
        refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
        finished
      · content_step (fun l ls => pushContent_sim l ls _ _)
        content_step (fun l ls => setTokenState_sim l ls _ _ _ _ _)
        string_run (consumed + 1)
    · string_run consumed
  · exact SimR.pure fun s t h => ⟨rfl, h⟩

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexStringLiteralLegacy_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (origin : Nat) (tokenStart : Location) (base : Nat) :
    ∀ k (consumed : Nat), input.size - consumed = k → ∀ horigin h,
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexStringLiteralLegacy (ops := o₁) input consumed origin horigin
        tokenStart base h)
      (Lexer.WRustPort.lexStringLiteralLegacy (ops := o₂) input consumed origin horigin
        tokenStart base h) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro consumed hk horigin h
  rw [Lexer.WRustPort.lexStringLiteralLegacy.eq_def (ops := o₁),
    Lexer.WRustPort.lexStringLiteralLegacy.eq_def (ops := o₂)]
  dsimp only
  split
  · rename_i _ c hc h1
    have := Lexer.Slice.lt_size_of_get? hc
    refine getCore_bind_P fun s t hs => ?_
    rw [hs.1.state]
    split
    · unfold Lexer.WRustPort.finishStringLiteral
      refine SimR.of_srl fun l ls => ?_
      refine SimR.seq (expectDelimiter_sim l ls _ _) ?_
      refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
      finished
    · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · content_step (fun l ls => pushContent_sim l ls _ _)
        content_step (fun l ls => setTokenState_sim l ls _ _ _ _ _)
        legacy_run (consumed + 1)
      · content_step (fun l ls => pushContent_sim l ls _ _)
        content_step (fun l ls => setTokenState_sim l ls _ _ _ _ _)
        legacy_run consumed
    · legacy_run consumed
  · exact SimR.pure fun s t h => ⟨rfl, h⟩

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexStringLiteral_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (tokenStart : Location) (base : Nat) (h) :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexStringLiteral (ops := o₁) input start tokenStart base h)
      (Lexer.WRustPort.lexStringLiteral (ops := o₂) input start tokenStart base h) := by
  unfold Lexer.WRustPort.lexStringLiteral
  refine getCore_bind_P fun s t hs => ?_
  refine SimR.ite (by rw [hs.1.version]) (fun _ => ?_) fun _ => ?_
  · exact lexStringLiteralLegacy_sim ho input start tokenStart base _ start rfl _ _
  · exact lexStringLiteralFrom_sim ho input start tokenStart base _ start rfl _ _

omit [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexComment_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (hstart : start ≤ input.size) (tokenStart : Location) (base : Nat) (h) :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexComment (ops := o₁) input start hstart tokenStart base h)
      (Lexer.WRustPort.lexComment (ops := o₂) input start hstart tokenStart base h) := by
  unfold Lexer.WRustPort.lexComment
  simp only [Lexer.WRustPort.consumesWhitespaceAndComments, pure_bind]
  generalize Consume.isConcrete (H := H) = cw
  split
  · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.of_srl fun l ls => ?_
      refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
      exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    · exact SimR.pure fun s t h => ⟨rfl, h⟩
  · rename_i c h1
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (markLineFeedAt_sim _ _) ?_
      refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine SimR.of_srl fun l ls => ?_
        refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
        refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
        finished
      · refine SimR.of_srl fun l ls => ?_
        finished
    · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine SimR.of_srl fun l ls => ?_
        refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
        refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
        finished
      · refine SimR.of_srl fun l ls => ?_
        finished

omit [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem afterStep_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (next next' : {next : Nat // start ≤ next})
    (e : next.val = next'.val) :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.afterStep (ops := o₁) input start hstart next)
      (Lexer.WRustPort.afterStep (ops := o₂) input start hstart next') := by
  unfold Lexer.WRustPort.afterStep
  refine SimR.dite (by rw [e]) (fun _ _ => SimR.pure fun s t h => ⟨e, h⟩) fun _ _ => ?_
  exact lexNormal_sim ho input start hstart

omit [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexStep_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (state : Lexer.LexerState) (tokenStart : Location)
    (base : Nat) (hpending) :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexStep (ops := o₁) input start hstart state tokenStart base hpending)
      (Lexer.WRustPort.lexStep (ops := o₂) input start hstart state tokenStart base
        hpending) := by
  have after : ∀ {f g}, LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor)
      (low := low) (SRb true) (StepQ (·.val) (·.val)) f g →
      LSim true (SRb true) (StepQ (·.val) (·.val))
        (f >>= Lexer.WRustPort.afterStep (ops := o₁) input start hstart)
        (g >>= Lexer.WRustPort.afterStep (ops := o₂) input start hstart) := fun hf =>
    SimR.bind hf fun a b => SimR.of_fact' (Er := ErS true) fun e =>
      afterStep_sim ho input start hstart a b e
  cases state <;> unfold Lexer.WRustPort.lexStep <;> dsimp only
  · exact lexNormal_sim ho input start hstart
  · exact after (lexNumeralOrDecimal_sim ho _ _ _ _ _)
  · exact after (lexFractionFrom_sim ho _ _ _ _ _)
  · exact after (lexBaseSelection_sim _ _ _ _ _)
  · exact after (lexDigitRun_sim ho _ _ _ _ _ _)
  · exact after (lexDigitRun_sim ho _ _ _ _ _ _)
  · exact after (lexStringLiteral_sim ho _ _ _ _ _)
  · exact after (lexStringLiteral_sim ho _ _ _ _ _)
  · exact after (lexStringLiteral_sim ho _ _ _ _ _)
  · exact after (lexSimpleSymbol_sim ho _ _ _ _ _)
  · exact after (lexQuotedSymbol_sim ho _ _ _ _ _ start rfl _ _ _)
  · exact after (lexKeyword_sim ho _ _ _ _ _)
  · exact after (lexComment_sim ho _ _ _ _ _ _)
  · exact after (lexWhitespace_sim ho _ _ _ _ _ start rfl _ _ _)
  · exact after (lexQuotedSymbolClosed_sim ho _ _ _ _ _ _)

end

end BSmtLib.Proofs.WRustPortX1BatchInCore

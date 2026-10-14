module

public import BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Normal
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The steps per state

The steps for a token in progress are the same code over the operations, which hand the
finished tokens over (`Finish`), and the loop of the normal state shown alike before. The steps
run inside a slice, where the simulation is strict.
-/

namespace BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Steps

open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)
open BSmtLib.Lexer.Internal.WRustPort.Slice (get? get runEnd runEndAll)
open BSmtLib.Lexer.Internal.WRustPort (Ops)
open BSmtLib.Facts.Proofs.Lexer.Simulation.Relation BSmtLib.Facts.Proofs.Lexer.Simulation.Steps
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Finish
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Normal
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Ops

/-- A change of the content buffer of both runs, from states with `SRb true`. -/
local macro "content_step " lemma:term:max : tactic => `(tactic|
  refine SimR.seq (Core.SimR.of_srl fun l ls => SimR.post (Q' := fun _ _ => Core.SRb true)
    (fun _ _ s t h => ⟨h.1.1, h.2⟩) ($lemma l ls)) ?_)

set_option hygiene false in
/-- The run of a string literal, from states with `SRb true`: a line feed or a quote goes on
with the loop by `ih`, any other byte that ends the run fails. The names are those of
`lexStringLiteralFrom_sim`; `P` is where the run starts. -/
local macro "string_run " P:term:max : tactic => `(tactic| (
  have hle := Lexer.Internal.WRustPort.Slice.le_runEnd input $P Lexer.CharClass.RUN_STRING_PLAIN
  split
  · rename_i c2 h3
    have := Lexer.Internal.WRustPort.Slice.lt_size_of_get? h3
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (Core.markLineFeedAt_sim _ _) ?_
      content_step (fun l ls => Core.extendContent_sim l ls _ _ _ _)
      exact ih _ (by omega) _ rfl _ _
    · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · content_step (fun l ls => Core.extendContent_sim l ls _ _ _ _)
        content_step (fun l ls => Core.setTokenState_sim l ls _ _ _ _ _)
        exact ih _ (by omega) _ rfl _ _
      · exact Core.SimR.of_srl fun l ls => Core.errorAt_sim l ls _ _ _
  · refine Core.SimR.of_srl fun l ls => ?_
    refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩))

set_option hygiene false in
/-- The end of a run of a string literal in the legacy mode: whether the byte that ends it goes
into the content, the run, the byte, and the loop by `ih`. The names are those of
`lexStringLiteralLegacy_sim`. -/
local macro "legacy_tail" : tactic => `(tactic| (
  refine SimR.bind_eq (P' := Core.SRb true) (SimR.pure fun s t h => ⟨rfl, h⟩) fun ar => ?_
  content_step (fun l ls => Core.extendContent_sim l ls _ _ _ _)
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · content_step (fun l ls => Core.pushContent_sim l ls _ _)
    exact ih _ (by omega) _ rfl _ _
  · exact ih _ (by omega) _ rfl _ _))

set_option hygiene false in
/-- The run of a string literal in the legacy mode from the index `P`, from states with
`SRb true`. -/
local macro "legacy_run " P:term:max : tactic => `(tactic| (
  have hle := Lexer.Internal.WRustPort.Slice.le_runEndAll input $P
      (Lexer.CharClass.RUN_STRING_PLAIN ||| Lexer.CharClass.RUN_QUOTED_PLAIN)
  split
  · rename_i _ c2 hc2 h3
    have := Lexer.Internal.WRustPort.Slice.lt_size_of_get? hc2
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (Core.markLineFeedAt_sim _ _) ?_
      legacy_tail
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · content_step (fun l ls => Core.setTokenState_sim l ls _ _ _ _ _)
      legacy_tail
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · content_step (fun l ls => Core.setTokenState_sim l ls _ _ _ _ _)
      legacy_tail
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · legacy_tail
    · simp only [bind_assoc, throw_bind]
      exact Core.SimR.of_srl fun l ls => Core.errorAt_sim l ls _ _ _
  · refine Core.SimR.of_srl fun l ls => ?_
    refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩))

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m]
  {floor : Option Nat} {low : Nat} {o₁ o₂ : Ops H m R E}
  {LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop}

/-- What a step gives back: the same index, from states with `SRb true`. -/
abbrev StepQ {α β : Type} (val : α → Nat) (val' : β → Nat) (a : α) (b : β)
    (s t : Core.St floor low) : Prop :=
  val a = val' b ∧ Core.SRb true s t

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
/-- A finished token, with the batches in the states left as any. -/
theorem fin {α β : Type} {strict : Bool} {l ls : Nat}
    {P : Core.St floor low → Core.St floor low → Prop}
    {f : Lexer.Internal.WRustPort.LexM H m R E floor low α}
    {g : Lexer.Internal.WRustPort.LexM H m R E floor low β}
    (h : Core.LSim strict P (fun _ _ => Core.SREb strict l ls) f g) :
    Core.LSim strict P (fun _ _ => Core.SRLb strict l ls) f g :=
  SimR.post (fun _ _ _ _ h => ⟨h.1.1, h.2⟩) h

/-- The end of a step that finished its token: the normal state, and the index. -/
local macro "finished" : tactic => `(tactic| (
  refine SimR.seq (Core.setNormal_sim _ _ _) ?_
  exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩))

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexFractionFrom_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (tokenStart : Span.Location) (base : Nat) (h) :
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexFractionFrom (ops := o₁) input start tokenStart base h)
      (Lexer.Internal.WRustPort.lexFractionFrom (ops := o₂) input start tokenStart base h) := by
  unfold Lexer.Internal.WRustPort.lexFractionFrom
  refine Core.SimR.of_srl fun l ls => ?_
  refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
  refine SimR.dite Iff.rfl (fun _ _ => ?_) fun _ _ => ?_
  · refine SimR.seq (fin (finishDecimal_sim ho l ls _ _ _ _ _)) ?_
    finished
  · refine SimR.seq (Core.setTokenState_sim l ls _ _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexNumeralOrDecimal_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (start : Nat) (tokenStart : Span.Location) (base : Nat) (h) :
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexNumeralOrDecimal (ops := o₁) input start tokenStart base h)
      (Lexer.Internal.WRustPort.lexNumeralOrDecimal (ops := o₂) input start tokenStart base h) := by
  unfold Lexer.Internal.WRustPort.lexNumeralOrDecimal
  refine Core.SimR.of_srl fun l ls => ?_
  refine Core.getCore_bind_P fun s t hs => ?_
  simp only [throw_bind]
  refine SimR.ite (by simp only [hs.1.1.tokenContent])
      (fun _ => Core.errorAt_sim l ls _ _ _) fun _ => ?_
  refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
  split
  · rename_i next h1
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (Core.pushContent_sim l ls _ _) ?_
      refine SimR.bind (SimR.pre (fun s t h => ⟨h.1.1, h.2⟩)
        (lexFractionFrom_sim ho input _ tokenStart base _)) fun x y => ?_
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      exact SimR.pure fun s t h => h
    · refine SimR.seq (Core.expectDelimiter_sim l ls _ _) ?_
      refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
      finished
  · exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexBaseSelection_sim (input : ByteSlice) (start : Nat) (hstart)
    (tokenStart : Span.Location) (h) :
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexBaseSelection input start hstart tokenStart h)
      (Lexer.Internal.WRustPort.lexBaseSelection input start hstart tokenStart h) := by
  unfold Lexer.Internal.WRustPort.lexBaseSelection
  refine Core.SimR.of_srl fun l ls => ?_
  simp only [throw_bind]
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimR.seq (Core.setTokenState_sim l ls _ _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimR.seq (Core.setTokenState_sim l ls _ _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  · exact Core.errorAt_sim l ls _ _ _

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexDigitRun_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (run : Lexer.Helpers.DigitRun) (tokenStart : Span.Location) (base : Nat) (h) :
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexDigitRun (ops := o₁) input start run tokenStart base h)
      (Lexer.Internal.WRustPort.lexDigitRun (ops := o₂) input start run tokenStart base h) := by
  unfold Lexer.Internal.WRustPort.lexDigitRun
  refine Core.SimR.of_srl fun l ls => ?_
  refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
  refine SimR.dite Iff.rfl (fun _ _ => ?_) fun _ _ => ?_
  · refine SimR.seq (fin (finishDigitRun_sim ho l ls _ _ _ _ _ _)) ?_
    finished
  · exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexSimpleSymbol_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (tokenStart : Span.Location) (base : Nat) (h) :
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexSimpleSymbol (ops := o₁) input start tokenStart base h)
      (Lexer.Internal.WRustPort.lexSimpleSymbol (ops := o₂) input start tokenStart base h) := by
  unfold Lexer.Internal.WRustPort.lexSimpleSymbol Lexer.Internal.WRustPort.finishSimpleSymbol
  refine Core.SimR.of_srl fun l ls => ?_
  refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
  refine SimR.dite Iff.rfl (fun _ _ => ?_) fun _ _ => ?_
  · refine SimR.seq (Core.expectDelimiter_sim l ls _ _) ?_
    refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
    finished
  · exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexKeyword_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (tokenStart : Span.Location) (base : Nat) (h) :
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexKeyword (ops := o₁) input start tokenStart base h)
      (Lexer.Internal.WRustPort.lexKeyword (ops := o₂) input start tokenStart base h) := by
  unfold Lexer.Internal.WRustPort.lexKeyword
  refine Core.SimR.of_srl fun l ls => ?_
  refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
  refine SimR.dite Iff.rfl (fun _ _ => ?_) fun _ _ => ?_
  · refine SimR.seq (fin (finishKeyword_sim ho l ls _ _ _ _ _)) ?_
    finished
  · exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexQuotedSymbolClosed_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (start : Nat) (hstart) (tokenStart : Span.Location) (base : Nat) (h) :
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexQuotedSymbolClosed
          (ops := o₁) input start hstart tokenStart base h)
      (Lexer.Internal.WRustPort.lexQuotedSymbolClosed
          (ops := o₂) input start hstart tokenStart base h) := by
  unfold Lexer.Internal.WRustPort.lexQuotedSymbolClosed
  refine Core.SimR.of_srl fun l ls => ?_
  refine SimR.seq (Core.expectDelimiter_sim l ls _ _) ?_
  refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
  finished

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexWhitespace_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (origin : Nat)
    (tokenStart : Span.Location) (base : Nat) :
    ∀ k (start : Nat), input.size - start = k → ∀ horigin hstart h,
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexWhitespace (ops := o₁) input start origin horigin hstart
          tokenStart
        base h)
      (Lexer.Internal.WRustPort.lexWhitespace (ops := o₂) input start origin horigin hstart
          tokenStart
        base h) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro start hk horigin hstart h
  rw [Lexer.Internal.WRustPort.lexWhitespace.eq_def (ops := o₁),
    Lexer.Internal.WRustPort.lexWhitespace.eq_def (ops := o₂)]
  dsimp only
  have hle := Lexer.Internal.WRustPort.Slice.le_runEnd input start
      Lexer.CharClass.RUN_NON_LF_WHITESPACE
  split
  · rename_i c h1
    have := Lexer.Internal.WRustPort.Slice.lt_size_of_get? h1
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (Core.markLineFeedAt_sim _ _) ?_
      content_step (fun l ls => Core.extendContent_sim l ls _ _ _ _)
      exact ih _ (by omega) _ rfl _ _ _
    · unfold Lexer.Internal.WRustPort.finishWhitespace
      refine Core.SimR.of_srl fun l ls => ?_
      refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
      refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
      finished
  · refine Core.SimR.of_srl fun l ls => ?_
    refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexQuotedSymbol_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (origin : Nat)
    (tokenStart : Span.Location) (base : Nat) :
    ∀ k (consumed : Nat), input.size - consumed = k → ∀ horigin hconsumed h,
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexQuotedSymbol (ops := o₁) input consumed origin horigin hconsumed
        tokenStart base h)
      (Lexer.Internal.WRustPort.lexQuotedSymbol (ops := o₂) input consumed origin horigin hconsumed
        tokenStart base h) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro consumed hk horigin hconsumed h
  rw [Lexer.Internal.WRustPort.lexQuotedSymbol.eq_def (ops := o₁),
    Lexer.Internal.WRustPort.lexQuotedSymbol.eq_def (ops := o₂)]
  dsimp only
  have hle := Lexer.Internal.WRustPort.Slice.le_runEnd input consumed
      Lexer.CharClass.RUN_QUOTED_PLAIN
  split
  · rename_i c h1
    have := Lexer.Internal.WRustPort.Slice.lt_size_of_get? h1
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine Core.SimR.of_srl fun l ls => ?_
      refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
      split
      · refine SimR.seq (Core.expectDelimiter_sim l ls _ _) ?_
        refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
        finished
      · refine SimR.seq (Core.setTokenState_sim l ls _ _ _ _ _) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · exact Core.SimR.of_srl fun l ls => Core.errorAt_sim l ls _ _ _
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (Core.markLineFeedAt_sim _ _) ?_
      content_step (fun l ls => Core.extendContent_sim l ls _ _ _ _)
      exact ih _ (by omega) _ rfl _ _ _
    · exact Core.SimR.of_srl fun l ls => Core.errorAt_sim l ls _ _ _
  · refine Core.SimR.of_srl fun l ls => ?_
    refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexStringLiteralFrom_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (origin : Nat) (tokenStart : Span.Location) (base : Nat) :
    ∀ k (consumed : Nat), input.size - consumed = k → ∀ horigin h,
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexStringLiteralFrom
          (ops := o₁) input consumed origin horigin tokenStart
        base h)
      (Lexer.Internal.WRustPort.lexStringLiteralFrom
          (ops := o₂) input consumed origin horigin tokenStart
        base h) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro consumed hk horigin h
  rw [Lexer.Internal.WRustPort.lexStringLiteralFrom.eq_def (ops := o₁),
    Lexer.Internal.WRustPort.lexStringLiteralFrom.eq_def (ops := o₂)]
  dsimp only
  split
  · rename_i _ c hc h1
    have := Lexer.Internal.WRustPort.Slice.lt_size_of_get? hc
    refine Core.getCore_bind_P fun s t hs => ?_
    refine SimR.ite (by rw [hs.1.state]) (fun _ => ?_) fun _ => ?_
    · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · unfold Lexer.Internal.WRustPort.finishStringLiteral
        refine Core.SimR.of_srl fun l ls => ?_
        refine SimR.seq (Core.expectDelimiter_sim l ls _ _) ?_
        refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
        finished
      · content_step (fun l ls => Core.pushContent_sim l ls _ _)
        content_step (fun l ls => Core.setTokenState_sim l ls _ _ _ _ _)
        string_run (consumed + 1)
    · string_run consumed
  · exact SimR.pure fun s t h => ⟨rfl, h⟩

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexStringLiteralLegacy_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (origin : Nat) (tokenStart : Span.Location) (base : Nat) :
    ∀ k (consumed : Nat), input.size - consumed = k → ∀ horigin h,
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexStringLiteralLegacy (ops := o₁) input consumed origin horigin
        tokenStart base h)
      (Lexer.Internal.WRustPort.lexStringLiteralLegacy (ops := o₂) input consumed origin horigin
        tokenStart base h) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro consumed hk horigin h
  rw [Lexer.Internal.WRustPort.lexStringLiteralLegacy.eq_def (ops := o₁),
    Lexer.Internal.WRustPort.lexStringLiteralLegacy.eq_def (ops := o₂)]
  dsimp only
  split
  · rename_i _ c hc h1
    have := Lexer.Internal.WRustPort.Slice.lt_size_of_get? hc
    refine Core.getCore_bind_P fun s t hs => ?_
    rw [hs.1.state]
    split
    · unfold Lexer.Internal.WRustPort.finishStringLiteral
      refine Core.SimR.of_srl fun l ls => ?_
      refine SimR.seq (Core.expectDelimiter_sim l ls _ _) ?_
      refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
      finished
    · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · content_step (fun l ls => Core.pushContent_sim l ls _ _)
        content_step (fun l ls => Core.setTokenState_sim l ls _ _ _ _ _)
        legacy_run (consumed + 1)
      · content_step (fun l ls => Core.pushContent_sim l ls _ _)
        content_step (fun l ls => Core.setTokenState_sim l ls _ _ _ _ _)
        legacy_run consumed
    · legacy_run consumed
  · exact SimR.pure fun s t h => ⟨rfl, h⟩

omit [Token.Consume H R E] [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexStringLiteral_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (tokenStart : Span.Location) (base : Nat) (h) :
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexStringLiteral (ops := o₁) input start tokenStart base h)
      (Lexer.Internal.WRustPort.lexStringLiteral (ops := o₂) input start tokenStart base h) := by
  unfold Lexer.Internal.WRustPort.lexStringLiteral
  refine Core.getCore_bind_P fun s t hs => ?_
  refine SimR.ite (by rw [hs.1.version]) (fun _ => ?_) fun _ => ?_
  · exact lexStringLiteralLegacy_sim ho input start tokenStart base _ start rfl _ _
  · exact lexStringLiteralFrom_sim ho input start tokenStart base _ start rfl _ _

omit [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexComment_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (hstart : start ≤ input.size) (tokenStart : Span.Location) (base : Nat) (h) :
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexComment (ops := o₁) input start hstart tokenStart base h)
      (Lexer.Internal.WRustPort.lexComment (ops := o₂) input start hstart tokenStart base h) := by
  unfold Lexer.Internal.WRustPort.lexComment
  simp only [Lexer.Internal.WRustPort.consumesWhitespaceAndComments, pure_bind]
  generalize Token.Consume.isConcrete (H := H) = cw
  split
  · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine Core.SimR.of_srl fun l ls => ?_
      refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
      exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    · exact SimR.pure fun s t h => ⟨rfl, h⟩
  · rename_i c h1
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (Core.markLineFeedAt_sim _ _) ?_
      refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine Core.SimR.of_srl fun l ls => ?_
        refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
        refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
        finished
      · refine Core.SimR.of_srl fun l ls => ?_
        finished
    · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine Core.SimR.of_srl fun l ls => ?_
        refine SimR.seq (Core.extendContent_sim l ls _ _ _ _) ?_
        refine SimR.seq (fin (sinkStored_sim ho l ls _ _ _ _ _)) ?_
        finished
      · refine Core.SimR.of_srl fun l ls => ?_
        finished

omit [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem afterStep_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (next next' : {next : Nat // start ≤ next})
    (e : next.val = next'.val) :
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.afterStep (ops := o₁) input start hstart next)
      (Lexer.Internal.WRustPort.afterStep (ops := o₂) input start hstart next') := by
  unfold Lexer.Internal.WRustPort.afterStep
  refine SimR.dite (by rw [e]) (fun _ _ => SimR.pure fun s t h => ⟨e, h⟩) fun _ _ => ?_
  exact lexNormal_sim ho input start hstart

omit [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] in
theorem lexStep_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (state : Lexer.Helpers.LexerState) (tokenStart : Span.Location)
    (base : Nat) (hpending) :
    Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (Core.SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.Internal.WRustPort.lexStep (ops := o₁) input start hstart state tokenStart base
          hpending)
      (Lexer.Internal.WRustPort.lexStep (ops := o₂) input start hstart state tokenStart base
        hpending) := by
  have after : ∀ {f g}, Core.LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor)
      (low := low) (Core.SRb true) (StepQ (·.val) (·.val)) f g →
      Core.LSim true (Core.SRb true) (StepQ (·.val) (·.val))
        (f >>= Lexer.Internal.WRustPort.afterStep (ops := o₁) input start hstart)
        (g >>= Lexer.Internal.WRustPort.afterStep (ops := o₂) input start hstart) := fun hf =>
    SimR.bind hf fun a b => SimR.of_fact' (Er := Core.ErS true) fun e =>
      afterStep_sim ho input start hstart a b e
  cases state <;> unfold Lexer.Internal.WRustPort.lexStep <;> dsimp only
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

end BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Steps

import BSmtLib.Proofs.X1BatchInCoreX2Contents.Loop

/-!
# The steps of a token in progress, in both lexers

Each step that lexes on a token in progress is the same code in both lexers but for the leading
zero test of a numeral, which reads the content (`isZero_stored`). The content is extended by
runs of the slice, which end within it or are empty (`runEnd_range`).
-/

namespace BSmtLib.Proofs.X1BatchInCoreX2Contents

open BSmtLib.Proofs.Simulation

theorem coreMap_state (c : Core2) : (coreMap c).state = c.state := rfl

/-- A run that ends at a byte ends within the slice, at or after its start. -/
theorem run_of_get? {input : ByteSlice} {p : Nat} {mask c : UInt8}
    (h : Lexer.Slice.get? input (Lexer.Slice.runEnd input p mask) = some c) :
    p ≤ Lexer.Slice.runEnd input p mask ∧ Lexer.Slice.runEnd input p mask < input.size :=
  ⟨Lexer.Slice.le_runEnd input p mask, Lexer.Slice.lt_size_of_get? h⟩

theorem runAll_of_get? {input : ByteSlice} {p : Nat} {mask c : UInt8}
    (h : Lexer.Slice.get? input (Lexer.Slice.runEndAll input p mask) = some c) :
    p ≤ Lexer.Slice.runEndAll input p mask ∧ Lexer.Slice.runEndAll input p mask < input.size :=
  ⟨Lexer.Slice.le_runEndAll input p mask, Lexer.Slice.lt_size_of_get? h⟩

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} (hblind : ContentBlind H m R E)
include hblind

theorem lexFractionFrom_sim (input : ByteSlice) (start : Nat) (s : Location) (base : Nat)
    (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.lexFractionFrom (H := H) (m := m) (R := R) (E := E) input start s base h)
      (Lexer.X1BatchInCore.lexFractionFrom input start s base h') := by
  unfold Lexer.X2Contents.lexFractionFrom Lexer.X1BatchInCore.lexFractionFrom
  refine SimF.seq (extendContent_sim input _ _ (runEnd_range _ _ _)) fun _ => ?_
  refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimF.seq (finishDecimal_sim hblind _ _ _ _ _ _) fun _ => ?_
    refine SimF.seq setNormal_sim fun _ => ?_
    exact SimF.pure (fun _ h => h) rfl
  · refine SimF.seq (setTokenState_sim _ _ _ _) fun _ => ?_
    exact SimF.pure (fun _ h => h) rfl

theorem lexNumeralOrDecimal_sim (input : ByteSlice) (start : Nat) (s : Location) (base : Nat)
    (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.lexNumeralOrDecimal (H := H) (m := m) (R := R) (E := E) input start s
        base h)
      (Lexer.X1BatchInCore.lexNumeralOrDecimal input start s base h') := by
  unfold Lexer.X2Contents.lexNumeralOrDecimal Lexer.X1BatchInCore.lexNumeralOrDecimal
  refine getCore_bind fun cc hcc => ?_
  refine SimF.ite (by rw [coreMap_tokenContent, isZero_stored hcc]) (fun _ =>
    SimF.bind (failAt_sim id _ _ (fun _ => BFits)) fun _ => ?_) fun _ => ?_
  all_goals
    refine SimF.seq (extendContent_sim input _ _ (runEnd_range _ _ _)) fun _ => ?_
    split
    · rename_i nx2 hn2
      refine SimF.hide_left fun F hF => ?_
      split
      · rename_i nx1 hn1
        obtain rfl : nx1 = nx2 := Option.some.inj (hn1.symm.trans hn2)
        subst hF
        refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
        · refine SimF.seq (pushContent_sim _) fun _ => ?_
          refine SimF.bind (lexFractionFrom_sim hblind _ _ _ _ _ _) fun _ => ?_
          exact SimF.pure (fun _ h => h) rfl
        · refine SimF.seq (expectDelimiter_sim _ _) fun _ => ?_
          refine SimF.seq (finishNumeral_sim hblind _ _ _ _ _) fun _ => ?_
          refine SimF.seq setNormal_sim fun _ => ?_
          exact SimF.pure (fun _ h => h) rfl
      · rename_i hn1
        exact absurd (hn1.symm.trans hn2) (by simp)
    · rename_i hn2
      refine SimF.hide_left fun F hF => ?_
      split
      · rename_i nx1 hn1
        exact absurd (hn1.symm.trans hn2) (by simp)
      · subst hF
        exact SimF.pure (fun _ h => h) rfl

omit [Consume H m R E] hblind in
theorem lexBaseSelection_sim (input : ByteSlice) (start : Nat) (s : Location) (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.lexBaseSelection (H := H) (m := m) (R := R) (E := E) input start s h)
      (Lexer.X1BatchInCore.lexBaseSelection input start s h') := by
  unfold Lexer.X2Contents.lexBaseSelection Lexer.X1BatchInCore.lexBaseSelection
  refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimF.seq (setTokenState_sim _ _ _ _) fun _ => ?_
    exact SimF.pure (fun _ h => h) rfl
  refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimF.seq (setTokenState_sim _ _ _ _) fun _ => ?_
    exact SimF.pure (fun _ h => h) rfl
  · refine SimF.bind (failAt_sim id _ _ (fun _ => BFits)) fun _ => ?_
    exact SimF.pure (fun _ h => h) rfl

theorem lexDigitRun_sim (input : ByteSlice) (start : Nat) (run : Lexer.DigitRun)
    (hrun hrun') (s : Location) (base : Nat) (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.lexDigitRun (H := H) (m := m) (R := R) (E := E) input start run hrun s
        base h)
      (Lexer.X1BatchInCore.lexDigitRun input start run hrun' s base h') := by
  unfold Lexer.X2Contents.lexDigitRun Lexer.X1BatchInCore.lexDigitRun
  refine SimF.seq (extendContent_sim input _ _ (runEnd_range _ _ _)) fun _ => ?_
  refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => SimF.pure (fun _ h => h) rfl
  refine SimF.seq (finishDigitRun_sim hblind _ _ _ _ _ _ _ _ _) fun _ => ?_
  refine SimF.seq setNormal_sim fun _ => ?_
  exact SimF.pure (fun _ h => h) rfl

theorem lexSimpleSymbol_sim (input : ByteSlice) (start : Nat) (s : Location) (base : Nat)
    (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.lexSimpleSymbol (H := H) (m := m) (R := R) (E := E) input start s base h)
      (Lexer.X1BatchInCore.lexSimpleSymbol input start s base h') := by
  unfold Lexer.X2Contents.lexSimpleSymbol Lexer.X1BatchInCore.lexSimpleSymbol
  refine SimF.seq (extendContent_sim input _ _ (runEnd_range _ _ _)) fun _ => ?_
  refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => SimF.pure (fun _ h => h) rfl
  refine SimF.seq (expectDelimiter_sim _ _) fun _ => ?_
  refine SimF.seq (finishSimpleSymbol_sim hblind _ _ _ _ _) fun _ => ?_
  refine SimF.seq setNormal_sim fun _ => ?_
  exact SimF.pure (fun _ h => h) rfl

theorem lexKeyword_sim (input : ByteSlice) (start : Nat) (s : Location) (base : Nat) (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.lexKeyword (H := H) (m := m) (R := R) (E := E) input start s base h)
      (Lexer.X1BatchInCore.lexKeyword input start s base h') := by
  unfold Lexer.X2Contents.lexKeyword Lexer.X1BatchInCore.lexKeyword
  refine SimF.seq (extendContent_sim input _ _ (runEnd_range _ _ _)) fun _ => ?_
  refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => SimF.pure (fun _ h => h) rfl
  refine SimF.seq (finishKeyword_sim hblind _ _ _ _ _ _) fun _ => ?_
  refine SimF.seq setNormal_sim fun _ => ?_
  exact SimF.pure (fun _ h => h) rfl

theorem lexQuotedSymbolClosed_sim (input : ByteSlice) (start : Nat) (s : Location) (base : Nat)
    (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.lexQuotedSymbolClosed (H := H) (m := m) (R := R) (E := E) input start s
        base h)
      (Lexer.X1BatchInCore.lexQuotedSymbolClosed input start s base h') := by
  unfold Lexer.X2Contents.lexQuotedSymbolClosed Lexer.X1BatchInCore.lexQuotedSymbolClosed
  refine SimF.seq (expectDelimiter_sim _ _) fun _ => ?_
  refine SimF.seq (sinkStored_sim hblind _ _ _ _ _ _ _ _) fun _ => ?_
  refine SimF.seq setNormal_sim fun _ => ?_
  exact SimF.pure (fun _ h => h) rfl

theorem lexComment_sim (input : ByteSlice) (start : Nat) (hstart hstart') (s : Location)
    (base : Nat) (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.lexComment (H := H) (m := m) (R := R) (E := E) input start hstart s base h)
      (Lexer.X1BatchInCore.lexComment input start hstart' s base h') := by
  unfold Lexer.X2Contents.lexComment Lexer.X1BatchInCore.lexComment
  conv => arg 6; zeta
  conv => arg 7; zeta
  split
  · rename_i hc2
    refine SimF.hide_left fun F hF => ?_
    split
    · subst hF
      refine SimF.bind consumes_sim fun w => ?_
      refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => SimF.pure (fun _ h => h) rfl
      refine SimF.seq (extendContent_sim input _ _ (.inl (Nat.le_refl _))) fun _ => ?_
      exact SimF.pure (fun _ h => h) rfl
    · rename_i c1 hc1
      exact absurd (hc1.symm.trans hc2) (by simp)
  · rename_i c2 hc2
    have hlt := Lexer.Slice.lt_size_of_get? hc2
    refine SimF.hide_left fun F hF => ?_
    split
    · rename_i hc1
      exact absurd (hc1.symm.trans hc2) (by simp)
    · rename_i c1 hc1
      obtain rfl : c1 = c2 := Option.some.inj (hc1.symm.trans hc2)
      subst hF
      refine SimF.ite Iff.rfl (fun _ => SimF.seq (markLineFeedAt_sim _) fun _ => ?_) fun _ => ?_
      all_goals
        refine SimF.bind consumes_sim fun w => ?_
        refine SimF.ite Iff.rfl (fun _ => SimF.seq (extendContent_sim input _ _ (.inl hlt))
          fun _ => SimF.seq (sinkStored_sim hblind _ _ _ _ _ _ _ _) fun _ => ?_) fun _ => ?_
      all_goals
        refine SimF.seq setNormal_sim fun _ => ?_
        exact SimF.pure (fun _ h => h) rfl

theorem lexWhitespace_sim (input : ByteSlice) (origin : Nat) (s : Location) (base : Nat)
    (h h') :
    ∀ k start, input.size - start = k → ∀ horigin horigin' hstart hstart',
      SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
        (Lexer.X2Contents.lexWhitespace (H := H) (m := m) (R := R) (E := E) input start origin
          horigin hstart s base h)
        (Lexer.X1BatchInCore.lexWhitespace input start origin horigin' hstart' s base h') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro start hk horigin horigin' hstart hstart'
  rw [Lexer.X2Contents.lexWhitespace, Lexer.X1BatchInCore.lexWhitespace]
  conv => arg 6; zeta
  conv => arg 7; zeta
  have hle := Lexer.Slice.le_runEnd input start Lexer.RUN_NON_LF_WHITESPACE
  split
  · rename_i c2 hc2
    have hlt := Lexer.Slice.lt_size_of_get? hc2
    refine SimF.hide_left fun F hF => ?_
    split
    · rename_i c1 hc1
      obtain rfl : c1 = c2 := Option.some.inj (hc1.symm.trans hc2)
      subst hF
      refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine SimF.seq (markLineFeedAt_sim _) fun _ => ?_
        refine SimF.seq (extendContent_sim input _ _ (.inl hlt)) fun _ => ?_
        exact ih _ (by omega) _ rfl _ _ _ _
      · refine SimF.seq (extendContent_sim input _ _ (.inl (Nat.le_of_lt hlt))) fun _ => ?_
        refine SimF.seq (finishWhitespace_sim hblind _ _ _ _ _) fun _ => ?_
        refine SimF.seq setNormal_sim fun _ => ?_
        exact SimF.pure (fun _ h => h) rfl
    · rename_i hc1
      exact absurd (hc1.symm.trans hc2) (by simp)
  · rename_i hc2
    refine SimF.hide_left fun F hF => ?_
    split
    · rename_i c1 hc1
      exact absurd (hc1.symm.trans hc2) (by simp)
    · subst hF
      refine SimF.seq (extendContent_sim input _ _ (.inl (Nat.le_refl _))) fun _ => ?_
      exact SimF.pure (fun _ h => h) rfl

theorem lexQuotedSymbol_sim (input : ByteSlice) (origin : Nat) (s : Location) (base : Nat)
    (h h') :
    ∀ k consumed, input.size - consumed = k → ∀ horigin horigin' hconsumed hconsumed',
      SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
        (Lexer.X2Contents.lexQuotedSymbol (H := H) (m := m) (R := R) (E := E) input consumed
          origin horigin hconsumed s base h)
        (Lexer.X1BatchInCore.lexQuotedSymbol input consumed origin horigin' hconsumed' s base
          h') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro consumed hk horigin horigin' hconsumed hconsumed'
  rw [Lexer.X2Contents.lexQuotedSymbol, Lexer.X1BatchInCore.lexQuotedSymbol]
  conv => arg 6; zeta
  conv => arg 7; zeta
  have hle := Lexer.Slice.le_runEnd input consumed Lexer.RUN_QUOTED_PLAIN
  split
  · rename_i c2 hc2
    have hlt := Lexer.Slice.lt_size_of_get? hc2
    refine SimF.hide_left fun F hF => ?_
    split
    · rename_i c1 hc1
      obtain rfl : c1 = c2 := Option.some.inj (hc1.symm.trans hc2)
      subst hF
      refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · -- the closing pipe
        refine SimF.seq (extendContent_sim input _ _ (.inl (Nat.le_of_lt hlt))) fun _ => ?_
        split
        · rename_i nx2 hn2
          refine SimF.hide_left fun F hF => ?_
          split
          · rename_i nx1 hn1
            obtain rfl : nx1 = nx2 := Option.some.inj (hn1.symm.trans hn2)
            subst hF
            refine SimF.seq (expectDelimiter_sim _ _) fun _ => ?_
            refine SimF.seq (sinkStored_sim hblind _ _ _ _ _ _ _ _) fun _ => ?_
            refine SimF.seq setNormal_sim fun _ => ?_
            exact SimF.pure (fun _ h => h) rfl
          · rename_i hn1
            exact absurd (hn1.symm.trans hn2) (by simp)
        · rename_i hn2
          refine SimF.hide_left fun F hF => ?_
          split
          · rename_i nx1 hn1
            exact absurd (hn1.symm.trans hn2) (by simp)
          · subst hF
            refine SimF.seq (setTokenState_sim _ _ _ _) fun _ => ?_
            exact SimF.pure (fun _ h => h) rfl
      refine SimF.ite Iff.rfl (fun _ => failAt_sim id _ _ _) fun _ => ?_
      refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => failAt_sim id _ _ _
      refine SimF.seq (markLineFeedAt_sim _) fun _ => ?_
      refine SimF.seq (extendContent_sim input _ _ (.inl hlt)) fun _ => ?_
      exact ih _ (by omega) _ rfl _ _ _ _
    · rename_i hc1
      exact absurd (hc1.symm.trans hc2) (by simp)
  · rename_i hc2
    refine SimF.hide_left fun F hF => ?_
    split
    · rename_i c1 hc1
      exact absurd (hc1.symm.trans hc2) (by simp)
    · subst hF
      refine SimF.seq (extendContent_sim input _ _ (.inl (Nat.le_refl _))) fun _ => ?_
      exact SimF.pure (fun _ h => h) rfl

theorem lexStringLiteralFrom_sim (input : ByteSlice) (origin : Nat) (s : Location) (base : Nat)
    (h h') :
    ∀ k consumed, input.size - consumed = k → ∀ horigin horigin',
      SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
        (Lexer.X2Contents.lexStringLiteralFrom (H := H) (m := m) (R := R) (E := E) input consumed
          origin horigin s base h)
        (Lexer.X1BatchInCore.lexStringLiteralFrom input consumed origin horigin' s base h') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro consumed hk horigin horigin'
  rw [Lexer.X2Contents.lexStringLiteralFrom, Lexer.X1BatchInCore.lexStringLiteralFrom]
  conv => arg 6; zeta
  conv => arg 7; zeta
  split
  · rename_i c2 hc2 heq2
    refine SimF.hide_left fun F hF => ?_
    split
    · rename_i c1 hc1 heq1
      have e := heq1.symm.trans heq2
      simp only [Option.some.injEq, Subtype.mk.injEq] at e
      subst e hF
      refine getCore_bind fun cc _ => ?_
      refine SimF.ite Iff.rfl (fun _ => SimF.ite Iff.rfl (fun _ => ?_) fun _ =>
        SimF.seq (pushContent_sim _) fun _ => SimF.seq (setTokenState_sim _ _ _ _) fun _ => ?_)
        fun _ => ?_
      · refine SimF.seq (expectDelimiter_sim _ _) fun _ => ?_
        refine SimF.seq (finishStringLiteral_sim hblind _ _ _ _ _) fun _ => ?_
        refine SimF.seq setNormal_sim fun _ => ?_
        exact SimF.pure (fun _ h => h) rfl
      all_goals
        split
        · rename_i c2' hc2'
          obtain ⟨hle, hlt⟩ := run_of_get? hc2'
          refine SimF.hide_left fun F hF => ?_
          split
          · rename_i c1' hc1'
            obtain rfl : c1' = c2' := Option.some.inj (hc1'.symm.trans hc2')
            subst hF
            refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
            · refine SimF.seq (markLineFeedAt_sim _) fun _ => ?_
              refine SimF.seq (extendContent_sim input _ _ (.inl hlt)) fun _ => ?_
              exact ih _ (by dsimp only at *; omega) _ rfl _ _
            refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => failAt_sim id _ _ _
            refine SimF.seq (extendContent_sim input _ _ (runEnd_range _ _ _)) fun _ => ?_
            refine SimF.seq (setTokenState_sim _ _ _ _) fun _ => ?_
            exact ih _ (by dsimp only at *; omega) _ rfl _ _
          · rename_i hc1'
            exact absurd (hc1'.symm.trans hc2') (by simp)
        · rename_i hc2'
          refine SimF.hide_left fun F hF => ?_
          split
          · rename_i c1' hc1'
            exact absurd (hc1'.symm.trans hc2') (by simp)
          · subst hF
            refine SimF.seq (extendContent_sim input _ _ (.inl (Nat.le_refl _))) fun _ => ?_
            exact SimF.pure (fun _ h => h) rfl
    · rename_i hno
      exact absurd heq2 (hno _ _)
  · rename_i hno
    split
    · rename_i c1 hc1 heq1
      exact absurd heq1 (hno _ _)
    · exact SimF.pure (fun _ h => h) rfl

omit [Consume H m R E] hblind in
/-- A value returned by both lexers. -/
theorem pure_sim {α : Type} (a : α) :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (pure a : Lexer.X2Contents.LexM H m R E floor low α)
      (pure a : Lexer.X1BatchInCore.LexM H m R E floor low α) :=
  SimF.pure (fun _ h => h) rfl

set_option hygiene false in
/-- The run of the 2.0 string literal after its first byte, in both lexers: the byte that ends
the run decides what is done with it, and the loop goes on after it. It names the slice `input`
and the induction hypothesis `ih` of the proof it is used in. -/
local macro "legacy_tail" : tactic => `(tactic| (
  split
  · rename_i c2' hc2' heq2'
    refine SimF.hide_left fun F hF => ?_
    split
    · rename_i c1' hc1' heq1'
      have e := heq1'.symm.trans heq2'
      simp only [Option.some.injEq, Subtype.mk.injEq] at e
      subst e hF
      obtain ⟨hle', hlt'⟩ := runAll_of_get? hc1'
      -- a line feed, a quote, a backslash, a pipe, or a byte that is not allowed
      refine SimF.ite Iff.rfl (fun _ => SimF.seq (markLineFeedAt_sim _) fun _ => ?_) fun _ => ?_
      rotate_left
      refine SimF.ite Iff.rfl (fun _ => SimF.seq (setTokenState_sim _ _ _ _) fun _ => ?_)
        fun _ => ?_
      rotate_left
      refine SimF.ite Iff.rfl (fun _ => SimF.seq (setTokenState_sim _ _ _ _) fun _ => ?_)
        fun _ => ?_
      rotate_left
      refine SimF.ite Iff.rfl (fun _ => ?_) fun _ =>
        SimF.bind (failAt_sim id _ _ (fun _ => BFits)) fun _ => ?_
      -- then the run is added to the content, with the byte if it belongs to it
      all_goals try (with_reducible refine SimF.bind (pure_sim _) fun _ => ?_)
      all_goals
        refine SimF.seq (extendContent_sim input _ _ (runEndAll_range _ _ _)) fun _ => ?_
        refine SimF.ite Iff.rfl (fun _ => SimF.seq (pushContent_sim _) fun _ => ?_) fun _ => ?_
      all_goals exact ih _ (by dsimp only at *; omega) _ rfl _ _
    · rename_i hno
      exact absurd heq2' (hno _ _)
  · rename_i hno
    refine SimF.hide_left fun F hF => ?_
    split
    · rename_i c1' hc1' heq1'
      exact absurd heq1' (hno _ _)
    · subst hF
      refine SimF.seq (extendContent_sim input _ _ (.inl (Nat.le_refl _))) fun _ => ?_
      exact SimF.pure (fun _ h => h) rfl))

theorem lexStringLiteralLegacy_sim (input : ByteSlice) (origin : Nat) (s : Location)
    (base : Nat) (h h') :
    ∀ k consumed, input.size - consumed = k → ∀ horigin horigin',
      SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
        (Lexer.X2Contents.lexStringLiteralLegacy (H := H) (m := m) (R := R) (E := E) input
          consumed origin horigin s base h)
        (Lexer.X1BatchInCore.lexStringLiteralLegacy input consumed origin horigin' s base h') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro consumed hk horigin horigin'
  rw [Lexer.X2Contents.lexStringLiteralLegacy, Lexer.X1BatchInCore.lexStringLiteralLegacy]
  conv => arg 6; zeta
  conv => arg 7; zeta
  split
  · rename_i c2 hc2 heq2
    refine SimF.hide_left fun F hF => ?_
    split
    · rename_i c1 hc1 heq1
      have e := heq1.symm.trans heq2
      simp only [Option.some.injEq, Subtype.mk.injEq] at e
      subst e hF
      refine getCore_bind fun cc _ => ?_
      rw [coreMap_state]
      split
      all_goals
        rename_i hs2
        refine SimF.hide_left fun F hF => ?_
        split
      all_goals
        rename_i hs1
        subst hF
      all_goals first
        | (exfalso; exact Lexer.LexerState.noConfusion (hs1.symm.trans hs2))
        | (exfalso; exact hs1 hs2)
        | (exfalso; exact hs2 hs1)
        | (rename_i hs2' hs1'; exfalso; exact hs1' hs2)
        | (rename_i hs2' hs1'; exfalso; exact hs2' hs1)
        | skip
      · -- the quote that ended the literal
        refine SimF.seq (expectDelimiter_sim _ _) fun _ => ?_
        refine SimF.seq (finishStringLiteral_sim hblind _ _ _ _ _) fun _ => ?_
        refine SimF.seq setNormal_sim fun _ => ?_
        exact SimF.pure (fun _ h => h) rfl
      · -- after a backslash
        refine SimF.ite Iff.rfl (fun _ => SimF.seq (pushContent_sim _) fun _ =>
          SimF.seq (setTokenState_sim _ _ _ _) fun _ => ?_) fun _ =>
          SimF.seq (pushContent_sim _) fun _ => SimF.seq (setTokenState_sim _ _ _ _) fun _ => ?_
        all_goals legacy_tail
      · legacy_tail
    · rename_i hno
      exact absurd heq2 (hno _ _)
  · rename_i hno
    split
    · rename_i c1 hc1 heq1
      exact absurd heq1 (hno _ _)
    · exact SimF.pure (fun _ h => h) rfl

theorem lexStringLiteral_sim (input : ByteSlice) (start : Nat) (s : Location) (base : Nat)
    (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.lexStringLiteral (H := H) (m := m) (R := R) (E := E) input start s base h)
      (Lexer.X1BatchInCore.lexStringLiteral input start s base h') := by
  unfold Lexer.X2Contents.lexStringLiteral Lexer.X1BatchInCore.lexStringLiteral
  refine getCore_bind fun _ _ => ?_
  exact SimF.ite Iff.rfl
    (fun _ => lexStringLiteralLegacy_sim hblind input start s base h h' _ start rfl _ _)
    fun _ => lexStringLiteralFrom_sim hblind input start s base h h' _ start rfl _ _

theorem afterStep_sim (input : ByteSlice) (start : Nat) (hstart hstart')
    (next : {next : Nat // start ≤ next}) :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.afterStep (H := H) (m := m) (R := R) (E := E) input start hstart next)
      (Lexer.X1BatchInCore.afterStep input start hstart' next) := by
  unfold Lexer.X2Contents.afterStep Lexer.X1BatchInCore.afterStep
  exact SimF.dite Iff.rfl (fun _ _ => SimF.pure (fun _ h => h) rfl)
    fun _ _ => lexNormal_sim hblind input start _ _

theorem lexStep_sim (input : ByteSlice) (start : Nat) (hstart hstart')
    (state : Lexer.LexerState) (s : Location) (base : Nat) (hp hp') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.lexStep (H := H) (m := m) (R := R) (E := E) input start hstart state s
        base hp)
      (Lexer.X1BatchInCore.lexStep input start hstart' state s base hp') := by
  unfold Lexer.X2Contents.lexStep Lexer.X1BatchInCore.lexStep
  cases state
  · exact lexNormal_sim hblind input start _ _
  · exact SimF.bind (lexNumeralOrDecimal_sim hblind _ _ _ _ _ _) fun _ =>
      afterStep_sim hblind _ _ _ _ _
  · exact SimF.bind (lexFractionFrom_sim hblind _ _ _ _ _ _) fun _ =>
      afterStep_sim hblind _ _ _ _ _
  · exact SimF.bind (lexBaseSelection_sim _ _ _ _ _) fun _ => afterStep_sim hblind _ _ _ _ _
  · exact SimF.bind (lexDigitRun_sim hblind _ _ _ _ _ _ _ _ _) fun _ =>
      afterStep_sim hblind _ _ _ _ _
  · exact SimF.bind (lexDigitRun_sim hblind _ _ _ _ _ _ _ _ _) fun _ =>
      afterStep_sim hblind _ _ _ _ _
  · exact SimF.bind (lexStringLiteral_sim hblind _ _ _ _ _ _) fun _ =>
      afterStep_sim hblind _ _ _ _ _
  · exact SimF.bind (lexStringLiteral_sim hblind _ _ _ _ _ _) fun _ =>
      afterStep_sim hblind _ _ _ _ _
  · exact SimF.bind (lexStringLiteral_sim hblind _ _ _ _ _ _) fun _ =>
      afterStep_sim hblind _ _ _ _ _
  · exact SimF.bind (lexSimpleSymbol_sim hblind _ _ _ _ _ _) fun _ =>
      afterStep_sim hblind _ _ _ _ _
  · exact SimF.bind (lexQuotedSymbol_sim hblind _ _ _ _ _ _ _ _ rfl _ _ _ _) fun _ =>
      afterStep_sim hblind _ _ _ _ _
  · exact SimF.bind (lexKeyword_sim hblind _ _ _ _ _ _) fun _ =>
      afterStep_sim hblind _ _ _ _ _
  · exact SimF.bind (lexComment_sim hblind _ _ _ _ _ _ _ _) fun _ =>
      afterStep_sim hblind _ _ _ _ _
  · exact SimF.bind (lexWhitespace_sim hblind _ _ _ _ _ _ _ _ rfl _ _ _ _) fun _ =>
      afterStep_sim hblind _ _ _ _ _
  · exact SimF.bind (lexQuotedSymbolClosed_sim hblind _ _ _ _ _ _) fun _ =>
      afterStep_sim hblind _ _ _ _ _

end

end BSmtLib.Proofs.X1BatchInCoreX2Contents

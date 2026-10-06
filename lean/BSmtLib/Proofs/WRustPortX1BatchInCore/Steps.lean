import BSmtLib.Proofs.WRustPortX1BatchInCore.Normal

/-!
# The steps per state

The steps of the two lexers for a token in progress are the same code, but for the errors,
which the Rust port makes and throws where the other fails at once, and the hand-overs and the
loop of the normal state shown alike before. The steps run inside a slice, where the simulation
is strict.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation (M runM)
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)
open BSmtLib.Proofs.Lexer.Slice (get? get runEnd runEndAll)

set_option hygiene false in
/-- The run of a string literal from the index `P`, from states with `SRb true`: a line feed or
a quote goes on with the loop by `ih`, any other byte that ends the run fails. The names are
those of `lexStringLiteralFrom_sim`; `hP` says that `P` is at or after `consumed`. -/
local macro "string_run " P:term:max : tactic => `(tactic| (
  have hle := Lexer.Slice.le_runEnd input $P Lexer.RUN_STRING_PLAIN
  split_both
  · rename_i c2 h3 c2' h4
    obtain rfl : c2' = c2 := Option.some.inj (h4.symm.trans h3)
    have := Lexer.Slice.lt_size_of_get? h3
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (markLineFeedAt_sim _ _) ?_
      refine SimR.seq (LSim.of_srl fun l ls => SimR.post (Q' := fun _ _ => SRb true)
        (fun _ _ s t h => ⟨h.1.1, h.2⟩) (extendContent_sim l ls _ _ _ _)) ?_
      exact ih _ (by omega) _ rfl _ _ _
    · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine SimR.seq (LSim.of_srl fun l ls => SimR.post (Q' := fun _ _ => SRb true)
          (fun _ _ s t h => ⟨h.1.1, h.2⟩) (extendContent_sim l ls _ _ _ _)) ?_
        refine SimR.seq (LSim.of_srl fun l ls => SimR.post (Q' := fun _ _ => SRb true)
          (fun _ _ s t h => ⟨h.1.1, h.2⟩) (setTokenState_sim l ls _ _ _ _ _)) ?_
        exact ih _ (by omega) _ rfl _ _ _
      · exact LSim.of_srl fun l ls => errorAt_sim l ls _ _ _
  · rename_i c2 h3 h4
    exact absurd (h3.symm.trans h4) (by simp)
  · rename_i h3 c2 h4
    exact absurd (h3.symm.trans h4) (by simp)
  · refine LSim.of_srl fun l ls => ?_
    refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩))

/-- A change of the content buffer of both lexers, from states with `SRb true`. -/
local macro "content_step " lemma:term:max : tactic => `(tactic|
  refine SimR.seq (LSim.of_srl fun l ls => SimR.post (Q' := fun _ _ => SRb true)
    (fun _ _ s t h => ⟨h.1.1, h.2⟩) ($lemma l ls)) ?_)

set_option hygiene false in
/-- The end of a run of a string literal in the legacy mode: whether the byte that ends it goes
into the content, the run, the byte, and the loop by `ih`. The names are those of
`lexStringLiteralLegacy_sim`. -/
local macro "legacy_tail" : tactic => `(tactic| (
  refine SimR.bind_eq (P' := SRb true) (SimR.pure fun s t h => ⟨rfl, h⟩) fun ar => ?_
  content_step (fun l ls => extendContent_sim l ls _ _ _ _)
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · content_step (fun l ls => pushContent_sim l ls _ _)
    exact ih _ (by omega) _ rfl _ _ _
  · exact ih _ (by omega) _ rfl _ _ _))

set_option hygiene false in
/-- The run of a string literal in the legacy mode from the index `P`, from states with
`SRb true`. -/
local macro "legacy_run " P:term:max : tactic => `(tactic| (
  have hle := Lexer.Slice.le_runEndAll input $P (Lexer.RUN_STRING_PLAIN ||| Lexer.RUN_QUOTED_PLAIN)
  split_both
  · rename_i _ c2 hc2 h3 _ c2' hc2' h4
    obtain rfl : c2' = c2 := congrArg Subtype.val (Option.some.inj (h4.symm.trans h3))
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
    · simp only [bind_assoc, throw_bind, failAt_bind]
      exact LSim.of_srl fun l ls => errorAt_sim l ls _ _ _
  · rename_i _ c2 hc2 h3 _ h4
    exact (h4 c2 hc2 h3).elim
  · rename_i _ h3 _ c2 hc2 h4
    exact (h3 c2 hc2 h4).elim
  · refine LSim.of_srl fun l ls => ?_
    refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩))

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat}

/-- What a step gives back: the same index, from states with `SRb true`. -/
abbrev StepQ {α β : Type} (val : α → Nat) (val' : β → Nat) (a : α) (b : β) (s : WS floor low)
    (t : XS floor low) : Prop :=
  val a = val' b ∧ SRb true s t

theorem lexFractionFrom_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) (start : Nat)
    (tokenStart : Location) (base : Nat) (h h') :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexFractionFrom input start tokenStart base h)
      (Lexer.X1BatchInCore.lexFractionFrom input start tokenStart base h') := by
  unfold Lexer.WRustPort.lexFractionFrom Lexer.X1BatchInCore.lexFractionFrom
  refine LSim.of_srl fun l ls => ?_
  dsimp only
  refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimR.seq (finishDecimal_sim hcons l ls _ _ _ _ _ _) ?_
    refine SimR.seq (setNormal_sim l ls _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  · refine SimR.seq (setTokenState_sim l ls _ _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

theorem lexNumeralOrDecimal_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice)
    (start : Nat) (tokenStart : Location) (base : Nat) (h h') :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexNumeralOrDecimal input start tokenStart base h)
      (Lexer.X1BatchInCore.lexNumeralOrDecimal input start tokenStart base h') := by
  unfold Lexer.WRustPort.lexNumeralOrDecimal Lexer.X1BatchInCore.lexNumeralOrDecimal
  refine LSim.of_srl fun l ls => ?_
  dsimp only
  refine getCore_bind_P fun s t hs => ?_
  simp only [throw_bind, failAt_bind]
  refine SimR.ite (by rw [hs.1.1.tokenContent]) (fun _ => errorAt_sim l ls _ _ _) fun _ => ?_
  refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
  split_both
  · rename_i _ next h1 _ next' h2
    obtain rfl : next' = next := Option.some.inj (h2.symm.trans h1)
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (pushContent_sim l ls _ _) ?_
      refine SimR.bind (SimR.pre (fun s t h => ⟨h.1.1, h.2⟩)
        (lexFractionFrom_sim hcons input _ tokenStart base _ _)) fun x y => ?_
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      exact SimR.pure fun s t h => h
    · refine SimR.seq (expectDelimiter_sim l ls _ _) ?_
      refine SimR.seq (finishNumeral_sim hcons l ls _ _ _ _ _) ?_
      refine SimR.seq (setNormal_sim l ls _) ?_
      exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  · rename_i _ next h1 _ h2
    exact absurd (h1.symm.trans h2) (by simp)
  · rename_i _ h1 _ next h2
    exact absurd (h1.symm.trans h2) (by simp)
  · exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

omit [Consume H m R E] in
theorem lexBaseSelection_sim (input : ByteSlice) (start : Nat) (tokenStart : Location) (h h') :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexBaseSelection input start tokenStart h)
      (Lexer.X1BatchInCore.lexBaseSelection input start tokenStart h') := by
  unfold Lexer.WRustPort.lexBaseSelection Lexer.X1BatchInCore.lexBaseSelection
  refine LSim.of_srl fun l ls => ?_
  dsimp only
  simp only [throw_bind, failAt_bind]
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimR.seq (setTokenState_sim l ls _ _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimR.seq (setTokenState_sim l ls _ _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  · exact errorAt_sim l ls _ _ _

theorem lexDigitRun_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) (start : Nat)
    (run : Lexer.DigitRun) (hrun) (tokenStart : Location) (base : Nat) (h h') :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexDigitRun input start run hrun tokenStart base h)
      (Lexer.X1BatchInCore.lexDigitRun input start run hrun tokenStart base h') := by
  unfold Lexer.WRustPort.lexDigitRun Lexer.X1BatchInCore.lexDigitRun
  refine LSim.of_srl fun l ls => ?_
  dsimp only
  refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimR.seq (finishDigitRun_sim hcons l ls _ _ _ _ _ _ _ _) ?_
    refine SimR.seq (setNormal_sim l ls _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  · exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

theorem lexSimpleSymbol_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) (start : Nat)
    (tokenStart : Location) (base : Nat) (h h') :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexSimpleSymbol input start tokenStart base h)
      (Lexer.X1BatchInCore.lexSimpleSymbol input start tokenStart base h') := by
  unfold Lexer.WRustPort.lexSimpleSymbol Lexer.X1BatchInCore.lexSimpleSymbol
  refine LSim.of_srl fun l ls => ?_
  dsimp only
  refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimR.seq (expectDelimiter_sim l ls _ _) ?_
    refine SimR.seq (finishSimpleSymbol_sim hcons l ls _ _ _ _ _) ?_
    refine SimR.seq (setNormal_sim l ls _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  · exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

theorem lexKeyword_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) (start : Nat)
    (tokenStart : Location) (base : Nat) (h h') :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexKeyword input start tokenStart base h)
      (Lexer.X1BatchInCore.lexKeyword input start tokenStart base h') := by
  unfold Lexer.WRustPort.lexKeyword Lexer.X1BatchInCore.lexKeyword
  refine LSim.of_srl fun l ls => ?_
  dsimp only
  refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · refine SimR.seq (finishKeyword_sim hcons l ls _ _ _ _ _ _) ?_
    refine SimR.seq (setNormal_sim l ls _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  · exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

theorem lexQuotedSymbolClosed_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice)
    (start : Nat) (tokenStart : Location) (base : Nat) (h h') :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexQuotedSymbolClosed input start tokenStart base h)
      (Lexer.X1BatchInCore.lexQuotedSymbolClosed input start tokenStart base h') := by
  unfold Lexer.WRustPort.lexQuotedSymbolClosed Lexer.X1BatchInCore.lexQuotedSymbolClosed
  refine LSim.of_srl fun l ls => ?_
  refine SimR.seq (expectDelimiter_sim l ls _ _) ?_
  refine SimR.seq (sinkStored_sim' hcons l ls _ _ _ _ _ _ _) ?_
  refine SimR.seq (setNormal_sim l ls _) ?_
  exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

theorem lexWhitespace_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) (origin : Nat)
    (tokenStart : Location) (base : Nat) :
    ∀ k (start : Nat), input.size - start = k → ∀ horigin hstart h h',
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexWhitespace input start origin horigin hstart tokenStart base h)
      (Lexer.X1BatchInCore.lexWhitespace input start origin horigin hstart tokenStart base h') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro start hk horigin hstart h h'
  rw [Lexer.WRustPort.lexWhitespace, Lexer.X1BatchInCore.lexWhitespace]
  dsimp only
  have hle := Lexer.Slice.le_runEnd input start Lexer.RUN_NON_LF_WHITESPACE
  split_both
  · rename_i c h1 c' h2
    obtain rfl : c' = c := Option.some.inj (h2.symm.trans h1)
    have := Lexer.Slice.lt_size_of_get? h1
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (markLineFeedAt_sim _ _) ?_
      refine SimR.seq (LSim.of_srl fun l ls => SimR.post (Q' := fun _ _ => SRb true)
        (fun _ _ s t h => ⟨h.1.1, h.2⟩)
        (extendContent_sim l ls _ _ _ _)) ?_
      exact ih _ (by omega) _ rfl _ _ _ _
    · refine LSim.of_srl fun l ls => ?_
      refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
      refine SimR.seq (finishWhitespace_sim hcons l ls _ _ _ _ _) ?_
      refine SimR.seq (setNormal_sim l ls _) ?_
      exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
  · rename_i c h1 h2
    exact absurd (h1.symm.trans h2) (by simp)
  · rename_i h1 c h2
    exact absurd (h1.symm.trans h2) (by simp)
  · refine LSim.of_srl fun l ls => ?_
    refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

theorem lexQuotedSymbol_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) (origin : Nat)
    (tokenStart : Location) (base : Nat) :
    ∀ k (consumed : Nat), input.size - consumed = k → ∀ horigin hconsumed h h',
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexQuotedSymbol input consumed origin horigin hconsumed tokenStart base h)
      (Lexer.X1BatchInCore.lexQuotedSymbol input consumed origin horigin hconsumed tokenStart
        base h') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro consumed hk horigin hconsumed h h'
  rw [Lexer.WRustPort.lexQuotedSymbol, Lexer.X1BatchInCore.lexQuotedSymbol]
  dsimp only
  have hle := Lexer.Slice.le_runEnd input consumed Lexer.RUN_QUOTED_PLAIN
  split_both
  · rename_i c h1 c' h2
    obtain rfl : c' = c := Option.some.inj (h2.symm.trans h1)
    have := Lexer.Slice.lt_size_of_get? h1
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine LSim.of_srl fun l ls => ?_
      refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
      split_both
      · rename_i _ next h3 _ next' h4
        obtain rfl : next' = next := Option.some.inj (h4.symm.trans h3)
        refine SimR.seq (expectDelimiter_sim l ls _ _) ?_
        refine SimR.seq (sinkStored_sim' hcons l ls _ _ _ _ _ _ _) ?_
        refine SimR.seq (setNormal_sim l ls _) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
      · rename_i _ next h3 _ h4
        exact absurd (h3.symm.trans h4) (by simp)
      · rename_i _ h3 _ next h4
        exact absurd (h3.symm.trans h4) (by simp)
      · refine SimR.seq (setTokenState_sim l ls _ _ _ _ _) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · exact LSim.of_srl fun l ls => errorAt_sim l ls _ _ _
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (markLineFeedAt_sim _ _) ?_
      refine SimR.seq (LSim.of_srl fun l ls => SimR.post (Q' := fun _ _ => SRb true)
        (fun _ _ s t h => ⟨h.1.1, h.2⟩)
        (extendContent_sim l ls _ _ _ _)) ?_
      exact ih _ (by omega) _ rfl _ _ _ _
    · exact LSim.of_srl fun l ls => errorAt_sim l ls _ _ _
  · rename_i c h1 h2
    exact absurd (h1.symm.trans h2) (by simp)
  · rename_i h1 c h2
    exact absurd (h1.symm.trans h2) (by simp)
  · refine LSim.of_srl fun l ls => ?_
    refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
    exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

theorem lexStringLiteralFrom_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice)
    (origin : Nat) (tokenStart : Location) (base : Nat) :
    ∀ k (consumed : Nat), input.size - consumed = k → ∀ horigin h h',
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexStringLiteralFrom input consumed origin horigin tokenStart base h)
      (Lexer.X1BatchInCore.lexStringLiteralFrom input consumed origin horigin tokenStart base
        h') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro consumed hk horigin h h'
  rw [Lexer.WRustPort.lexStringLiteralFrom, Lexer.X1BatchInCore.lexStringLiteralFrom]
  dsimp only
  split_both
  · rename_i _ c hc h1 _ c' hc' h2
    obtain rfl : c' = c := congrArg Subtype.val (Option.some.inj (h2.symm.trans h1))
    have := Lexer.Slice.lt_size_of_get? hc
    refine getCore_bind_P fun s t hs => ?_
    refine SimR.ite (by rw [hs.1.state]) (fun _ => ?_) fun _ => ?_
    · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine LSim.of_srl fun l ls => ?_
        refine SimR.seq (expectDelimiter_sim l ls _ _) ?_
        refine SimR.seq (finishStringLiteral_sim hcons l ls _ _ _ _ _) ?_
        refine SimR.seq (setNormal_sim l ls _) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
      · refine SimR.seq (LSim.of_srl fun l ls => SimR.post (Q' := fun _ _ => SRb true)
          (fun _ _ s t h => ⟨h.1.1, h.2⟩) (pushContent_sim l ls _ _)) ?_
        refine SimR.seq (LSim.of_srl fun l ls => SimR.post (Q' := fun _ _ => SRb true)
          (fun _ _ s t h => ⟨h.1.1, h.2⟩) (setTokenState_sim l ls _ _ _ _ _)) ?_
        string_run (consumed + 1)
    · string_run consumed
  · rename_i _ c hc h1 _ h2
    exact (h2 c hc h1).elim
  · rename_i _ h1 _ c hc h2
    exact (h1 c hc h2).elim
  · exact SimR.pure fun s t h => ⟨rfl, h⟩


theorem lexStringLiteralLegacy_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice)
    (origin : Nat) (tokenStart : Location) (base : Nat) :
    ∀ k (consumed : Nat), input.size - consumed = k → ∀ horigin h h',
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexStringLiteralLegacy input consumed origin horigin tokenStart base h)
      (Lexer.X1BatchInCore.lexStringLiteralLegacy input consumed origin horigin tokenStart base
        h') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro consumed hk horigin h h'
  rw [Lexer.WRustPort.lexStringLiteralLegacy, Lexer.X1BatchInCore.lexStringLiteralLegacy]
  dsimp only
  split_both
  · rename_i _ c hc h1 _ c' hc' h2
    obtain rfl : c' = c := congrArg Subtype.val (Option.some.inj (h2.symm.trans h1))
    have := Lexer.Slice.lt_size_of_get? hc
    refine getCore_bind_P fun s t hs => ?_
    rw [hs.1.state]
    split_both
    all_goals (try (first | contradiction |
      (rename_i _ h3 _ h4; have e := h3.symm.trans h4; cases e; done)))
    · refine LSim.of_srl fun l ls => ?_
      refine SimR.seq (expectDelimiter_sim l ls _ _) ?_
      refine SimR.seq (finishStringLiteral_sim hcons l ls _ _ _ _ _) ?_
      refine SimR.seq (setNormal_sim l ls _) ?_
      exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · content_step (fun l ls => pushContent_sim l ls _ _)
        content_step (fun l ls => setTokenState_sim l ls _ _ _ _ _)
        legacy_run (consumed + 1)
      · content_step (fun l ls => pushContent_sim l ls _ _)
        content_step (fun l ls => setTokenState_sim l ls _ _ _ _ _)
        legacy_run consumed
    · legacy_run consumed
  · rename_i _ c hc h1 _ h2
    exact (h2 c hc h1).elim
  · rename_i _ h1 _ c hc h2
    exact (h1 c hc h2).elim
  · exact SimR.pure fun s t h => ⟨rfl, h⟩

theorem lexStringLiteral_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) (start : Nat)
    (tokenStart : Location) (base : Nat) (h h') :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexStringLiteral input start tokenStart base h)
      (Lexer.X1BatchInCore.lexStringLiteral input start tokenStart base h') := by
  unfold Lexer.WRustPort.lexStringLiteral Lexer.X1BatchInCore.lexStringLiteral
  refine getCore_bind_P fun s t hs => ?_
  refine SimR.ite (by rw [hs.1.version]) (fun _ => ?_) fun _ => ?_
  · exact lexStringLiteralLegacy_sim hcons input start tokenStart base _ start rfl _ _ _
  · exact lexStringLiteralFrom_sim hcons input start tokenStart base _ start rfl _ _ _

theorem lexComment_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) (start : Nat)
    (hstart : start ≤ input.size) (tokenStart : Location) (base : Nat) (h h') :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexComment input start hstart tokenStart base h)
      (Lexer.X1BatchInCore.lexComment input start hstart tokenStart base h') := by
  unfold Lexer.WRustPort.lexComment Lexer.X1BatchInCore.lexComment
  simp only [Lexer.WRustPort.consumesWhitespaceAndComments,
    Lexer.X1BatchInCore.consumesWhitespaceAndComments, pure_bind]
  generalize Consume.consumesWhitespaceAndComments (H := H) = cw
  split_both
  · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine LSim.of_srl fun l ls => ?_
      refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
      exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    · exact SimR.pure fun s t h => ⟨rfl, h⟩
  · rename_i h1 c h2
    exact absurd (h1.symm.trans h2) (by simp)
  · rename_i c h1 h2
    exact absurd (h1.symm.trans h2) (by simp)
  · rename_i c h1 c' h2
    obtain rfl : c' = c := Option.some.inj (h2.symm.trans h1)
    refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · refine SimR.seq (markLineFeedAt_sim _ _) ?_
      refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine LSim.of_srl fun l ls => ?_
        refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
        refine SimR.seq (sinkStored_sim' hcons l ls _ _ _ _ _ _ _) ?_
        refine SimR.seq (setNormal_sim l ls _) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
      · refine LSim.of_srl fun l ls => ?_
        refine SimR.seq (setNormal_sim l ls _) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
    · refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_
      · refine LSim.of_srl fun l ls => ?_
        refine SimR.seq (extendContent_sim l ls _ _ _ _) ?_
        refine SimR.seq (sinkStored_sim' hcons l ls _ _ _ _ _ _ _) ?_
        refine SimR.seq (setNormal_sim l ls _) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩
      · refine LSim.of_srl fun l ls => ?_
        refine SimR.seq (setNormal_sim l ls _) ?_
        exact SimR.pure fun s t h => ⟨rfl, h.1.1, h.2⟩

theorem afterStep_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (next : {next : Nat // start ≤ next})
    (next' : {next : Nat // start ≤ next}) (e : next.val = next'.val) :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.afterStep input start hstart next)
      (Lexer.X1BatchInCore.afterStep input start hstart next') := by
  unfold Lexer.WRustPort.afterStep Lexer.X1BatchInCore.afterStep
  refine SimR.dite (by rw [e]) (fun _ _ => SimR.pure fun s t h => ⟨e, h⟩) fun _ _ => ?_
  exact lexNormal_sim hcons input start hstart

theorem lexStep_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (state : Lexer.LexerState) (tokenStart : Location)
    (base : Nat) (hpending hpending') :
    LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRb true)
      (StepQ (·.val) (·.val))
      (Lexer.WRustPort.lexStep input start hstart state tokenStart base hpending)
      (Lexer.X1BatchInCore.lexStep input start hstart state tokenStart base hpending') := by
  have after : ∀ {f g}, LSim true (H := H) (m := m) (R := R) (E := E) (floor := floor)
      (low := low) (SRb true) (StepQ (·.val) (·.val)) f g →
      LSim true (SRb true) (StepQ (·.val) (·.val))
        (f >>= Lexer.WRustPort.afterStep input start hstart)
        (g >>= Lexer.X1BatchInCore.afterStep input start hstart) := fun hf =>
    SimR.bind hf fun a b => SimR.of_fact' (Er := ErS true) fun e =>
      afterStep_sim hcons input start hstart a b e
  cases state <;> unfold Lexer.WRustPort.lexStep Lexer.X1BatchInCore.lexStep <;> dsimp only
  · exact lexNormal_sim hcons input start hstart
  · exact after (lexNumeralOrDecimal_sim hcons _ _ _ _ _ _)
  · exact after (lexFractionFrom_sim hcons _ _ _ _ _ _)
  · exact after (lexBaseSelection_sim _ _ _ _ _)
  · exact after (lexDigitRun_sim hcons _ _ _ _ _ _ _ _)
  · exact after (lexDigitRun_sim hcons _ _ _ _ _ _ _ _)
  · exact after (lexStringLiteral_sim hcons _ _ _ _ _ _)
  · exact after (lexStringLiteral_sim hcons _ _ _ _ _ _)
  · exact after (lexStringLiteral_sim hcons _ _ _ _ _ _)
  · exact after (lexSimpleSymbol_sim hcons _ _ _ _ _ _)
  · exact after (lexQuotedSymbol_sim hcons _ _ _ _ _ start rfl _ _ _ _)
  · exact after (lexKeyword_sim hcons _ _ _ _ _ _)
  · exact after (lexComment_sim hcons _ _ _ _ _ _ _)
  · exact after (lexWhitespace_sim hcons _ _ _ _ _ start rfl _ _ _ _)
  · exact after (lexQuotedSymbolClosed_sim hcons _ _ _ _ _ _)

end

end BSmtLib.Proofs.WRustPortX1BatchInCore

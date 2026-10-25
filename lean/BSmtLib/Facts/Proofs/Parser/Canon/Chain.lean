module

public import BSmtLib.Facts.Proofs.PublicApi.Resets
public import BSmtLib.Facts.Proofs.Reader.Param.Adapter
import all BSmtLib.Lexer

@[expose] public section

/-!
# Lexers related through one Rust port's lexer, for a consumer in `Id`

`PublicApi.Resets` relates two library's lexers with the collector through one Rust port's lexer
(`ZRel`). The relation and its steps hold for any consumer in `Id` that reads the cursors only
below the length of their batches (`ConsumesAlike`): related lexers lex alike, with related
lexers after.
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Parser.Canon.Chain

open BSmtLib.Lexer
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Facts.Proofs.Lexer BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
open BSmtLib.Facts.Proofs.Lexer.Simulation.Couple
open BSmtLib.Facts.Proofs.Reader.Param.Adapter (id_bind_eq)

theorem mcouple_id {α β : Type} {Rel : α → β → Prop} {a : Id α} {b : Id β}
    (h : MCouple Rel a b) : Rel a b := by
  obtain ⟨y, h1, h2⟩ := h
  subst h1 h2
  exact y.property

section

variable {H R E : Type} [Token.Consume H R E] [∀ b, Token.ConsumeFrom H (LexerCursor b) Id]

/-- Two library's lexers, each related to a lexer with the batch in its state as the library's
lexer is to it, and both of these to one Rust port's lexer. -/
def ZRelG (l₁ l₂ : BSmtLib.Lexer H) : Prop :=
  ∃ x₁ x₂ w : Lexer.Internal.WRustPort.Lexer H Lexer.Recovery.FailFast,
    X1BatchInCoreLexer.Top.LexerRel l₁ x₁ ∧ WRustPortX1BatchInCore.Calls.LexRel w x₁ ∧
    WRustPortX1BatchInCore.Calls.LexRel w x₂ ∧ X1BatchInCoreLexer.Top.LexerRel l₂ x₂

/-- What a fresh lexer gives up after failing. -/
abbrev abandonI := Recovery.LexerRecovery.abandon (H := H) (m := Id) Recovery.FailFast

/-- What a fresh lexer reports after recovering. -/
abbrev recoverI := Recovery.LexerRecovery.recover (H := H) (m := Id) Recovery.FailFast

variable (hcons : ConsumesAlike H Id R E)
include hcons

theorem step_fit {l₁ l₂ : BSmtLib.Lexer H} (h : ZRelG l₁ l₂) (slice : ByteSlice)
    (hs : slice.stop < USize.size) :
    (Internal.run l₁ (Internal.lexSliceStep (R := R) (E := E) abandonI recoverI slice)).1 =
      (Internal.run l₂ (Internal.lexSliceStep (R := R) (E := E) abandonI recoverI slice)).1 ∧
    ZRelG (Internal.run l₁ (Internal.lexSliceStep (R := R) (E := E) abandonI recoverI slice)).2
      (Internal.run l₂ (Internal.lexSliceStep (R := R) (E := E) abandonI recoverI slice)).2 := by
  obtain ⟨x₁, x₂, w, h₁, hw₁, hw₂, h₂⟩ := h
  obtain ⟨a1, a2⟩ := mcouple_id (X1BatchInCoreLexer.X1BatchInCore.lexSliceStep_sim_lexer
    abandonI recoverI l₁ x₁ h₁ slice hs)
  obtain ⟨b1, b2⟩ := mcouple_id (X1BatchInCoreLexer.X1BatchInCore.lexSliceStep_sim_lexer
    abandonI recoverI l₂ x₂ h₂ slice hs)
  obtain ⟨c1, c2⟩ := mcouple_id
    (WRustPortX1BatchInCore.WRustPort.run_lexSliceStep_sim_x1BatchInCore hcons
      abandonI recoverI slice w x₁ hw₁)
  obtain ⟨d1, d2⟩ := mcouple_id
    (WRustPortX1BatchInCore.WRustPort.run_lexSliceStep_sim_x1BatchInCore hcons
      abandonI recoverI slice w x₂ hw₂)
  exact ⟨a1.trans (c1.symm.trans (d1.trans b1.symm)), _, _, _, a2, c2, d2, b2⟩

theorem step_eof {l₁ l₂ : BSmtLib.Lexer H} (h : ZRelG l₁ l₂) :
    (Internal.run l₁ (Internal.lexEofStep (R := R) (E := E) abandonI recoverI)).1 =
      (Internal.run l₂ (Internal.lexEofStep (R := R) (E := E) abandonI recoverI)).1 ∧
    ZRelG (Internal.run l₁ (Internal.lexEofStep (R := R) (E := E) abandonI recoverI)).2
      (Internal.run l₂ (Internal.lexEofStep (R := R) (E := E) abandonI recoverI)).2 := by
  obtain ⟨x₁, x₂, w, h₁, hw₁, hw₂, h₂⟩ := h
  obtain ⟨a1, a2⟩ := mcouple_id (X1BatchInCoreLexer.X1BatchInCore.lexEofStep_sim_lexer
    abandonI recoverI l₁ x₁ h₁)
  obtain ⟨b1, b2⟩ := mcouple_id (X1BatchInCoreLexer.X1BatchInCore.lexEofStep_sim_lexer
    abandonI recoverI l₂ x₂ h₂)
  obtain ⟨c1, c2⟩ := mcouple_id
    (WRustPortX1BatchInCore.WRustPort.run_lexEofStep_sim_x1BatchInCore hcons
      abandonI recoverI w x₁ hw₁)
  obtain ⟨d1, d2⟩ := mcouple_id
    (WRustPortX1BatchInCore.WRustPort.run_lexEofStep_sim_x1BatchInCore hcons
      abandonI recoverI w x₂ hw₂)
  exact ⟨a1.trans (c1.symm.trans (d1.trans b1.symm)), _, _, _, a2, c2, d2, b2⟩

omit hcons [∀ b, Token.ConsumeFrom H (LexerCursor b) Id] in
theorem run_bind {α β : Type} (l : BSmtLib.Lexer H) (f : InnerM H Id α)
    (k : α → InnerM H Id β) :
    Internal.run l (f >>= k) = Internal.run (Internal.run l f).2 (k (Internal.run l f).1) :=
  (rfl)

omit hcons [∀ b, Token.ConsumeFrom H (LexerCursor b) Id] in
theorem run_pure {α : Type} (l : BSmtLib.Lexer H) (a : α) :
    Internal.run l (Pure.pure a : InnerM H Id α) = (a, l) := (rfl)

/-- Related lexers lex the chunks of a slice from a position alike. -/
theorem step_chunks (slice : ByteSlice) : ∀ (n position : Nat), slice.size - position < n →
    ∀ (held : Option (Span.Located R)) {l₁ l₂ : BSmtLib.Lexer H}, ZRelG l₁ l₂ →
    (Internal.run l₁ (Internal.lexChunks (R := R) (E := E) abandonI recoverI slice position
        held)).1 =
      (Internal.run l₂ (Internal.lexChunks (R := R) (E := E) abandonI recoverI slice position
        held)).1 ∧
    ZRelG (Internal.run l₁ (Internal.lexChunks (R := R) (E := E) abandonI recoverI slice position
        held)).2
      (Internal.run l₂ (Internal.lexChunks (R := R) (E := E) abandonI recoverI slice position
        held)).2
  | 0, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, position, hn => by
    intro held l₁ l₂ h
    rw [Internal.lexChunks.eq_def]
    by_cases hp : position < slice.size
    · simp only [hp, dite_true]
      rw [run_bind, run_bind]
      have hfit : ∀ (s : ByteSlice) (hs : s.stop < USize.size),
          Internal.lexSliceFitting (H := H) (m := Id) (R := R) (E := E)
            abandonI recoverI s hs =
          Internal.lexSliceStep abandonI recoverI s := by
        intro s hs
        unfold Internal.lexSliceStep
        rw [dite_eq_left_of_eq_true (eq_true hs)]
      rw [hfit]
      generalize hch : (slice.byteArray.extract (slice.start + position)
        (min (slice.start + position + Internal.CHUNK_SIZE) slice.stop)).toByteSlice = chunk
      have hsize : chunk.stop < USize.size := by
        rw [← hch, Internal.stop_toByteSlice]
        have := USize.le_size
        simp only [ByteArray.size_extract, Internal.CHUNK_SIZE]
        omega
      obtain ⟨e1, hz⟩ := step_fit hcons h chunk hsize
      generalize Internal.run l₁ (Internal.lexSliceStep (R := R) (E := E) abandonI
        recoverI chunk) = A at e1 hz ⊢
      generalize Internal.run l₂ (Internal.lexSliceStep (R := R) (E := E) abandonI
        recoverI chunk) = B at e1 hz ⊢
      obtain ⟨r₁, l₁'⟩ := A
      obtain ⟨r₂, l₂'⟩ := B
      dsimp only at e1 hz ⊢
      subst e1
      cases r₁ with
      | ok held' =>
        exact step_chunks slice n _ (by simp only [Internal.CHUNK_SIZE] at *; omega) _ hz
      | error err =>
        simp only
        rw [run_pure, run_pure]
        exact ⟨rfl, hz⟩
    · simp only [hp, dite_false]
      rw [run_pure, run_pure]
      exact ⟨rfl, h⟩

/-- Related lexers lex a slice alike. -/
theorem step_slice {l₁ l₂ : BSmtLib.Lexer H} (h : ZRelG l₁ l₂) (slice : ByteSlice) :
    (Internal.run l₁ (Internal.lexSliceStep (R := R) (E := E) abandonI recoverI slice)).1 =
      (Internal.run l₂ (Internal.lexSliceStep (R := R) (E := E) abandonI recoverI slice)).1 ∧
    ZRelG (Internal.run l₁ (Internal.lexSliceStep (R := R) (E := E) abandonI recoverI slice)).2
      (Internal.run l₂ (Internal.lexSliceStep (R := R) (E := E) abandonI recoverI slice)).2 := by
  by_cases hs : slice.stop < USize.size
  · exact step_fit hcons h slice hs
  · unfold Internal.lexSliceStep
    rw [dite_eq_right_of_eq_false (eq_false hs)]
    exact step_chunks hcons slice _ 0 (Nat.lt_succ_self _) none h

end

section

variable {H R E : Type} [Token.Consume H R E]

theorem ZRelG.held {l₁ l₂ : BSmtLib.Lexer H} (h : ZRelG l₁ l₂) :
    Internal.held l₁ = Internal.held l₂ := by
  obtain ⟨x₁, x₂, w, h₁, hw₁, hw₂, h₂⟩ := h
  exact h₁.2.2.symm.trans (hw₁.2.2.symm.trans (hw₂.2.2.trans h₂.2.2))

theorem ZRelG.handler {l₁ l₂ : BSmtLib.Lexer H} (h : ZRelG l₁ l₂) :
    Internal.handler l₁ = Internal.handler l₂ := by
  obtain ⟨x₁, x₂, w, h₁, hw₁, hw₂, h₂⟩ := h
  exact h₁.1.symm.trans (hw₁.1.symm.trans (hw₂.1.trans h₂.1))
theorem ZRelG.discardedFrom {l₁ l₂ : BSmtLib.Lexer H} (h : ZRelG l₁ l₂) :
    (Internal.core l₁).discardedFrom = (Internal.core l₂).discardedFrom := by
  obtain ⟨x₁, x₂, w, h₁, hw₁, hw₂, h₂⟩ := h
  have e₁ : (x₁.core).discardedFrom = (Internal.core l₁).discardedFrom :=
    congrArg (fun x => x.discardedFrom) (h₁.2.1 : X1BatchInCoreLexer.Outer.zb _ = _)
  have e₂ : (x₂.core).discardedFrom = (Internal.core l₂).discardedFrom :=
    congrArg (fun x => x.discardedFrom) (h₂.2.1 : X1BatchInCoreLexer.Outer.zb _ = _)
  exact e₁.symm.trans (hw₁.2.1.1.discardedFrom.symm.trans (hw₂.2.1.1.discardedFrom.trans e₂))


theorem ZRelG.withHeld {l₁ l₂ : BSmtLib.Lexer H} (h : ZRelG l₁ l₂)
    (held : Option (Span.Located R)) :
    ZRelG (Internal.withHeld l₁ held) (Internal.withHeld l₂ held) := by
  obtain ⟨x₁, x₂, w, h₁, hw₁, hw₂, h₂⟩ := h
  exact ⟨{ x₁ with held }, { x₂ with held }, { w with held }, ⟨h₁.1, h₁.2.1, rfl⟩,
    ⟨hw₁.1, hw₁.2.1, rfl⟩, ⟨hw₂.1, hw₂.2.1, rfl⟩, ⟨h₂.1, h₂.2.1, rfl⟩⟩

end

end BSmtLib.Facts.Proofs.Parser.Canon.Chain

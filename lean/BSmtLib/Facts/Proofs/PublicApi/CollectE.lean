module

public import BSmtLib.Facts.Proofs.PublicApi.Collector
public import BSmtLib.Facts.Proofs.Lexer.Consumers.RunE
import all BSmtLib.Lexer
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor

@[expose] public section

/-!
# The collector's run against the adapter's feeding, keeping the error

`collect_runInputE`: the collector's run on slices and the adapter's feeding of the library's
lexer with the concrete collector (`RunE.runInputE`), from lexers with the same state and related
held results, take the same entries and end alike: with the same result, or with errors of the
same lexical kind, span and continuation, or both of the consumer.
-/

namespace BSmtLib.Facts.Proofs.PublicApi.CollectE

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Facts.PublicApi.Adapters
open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Reader.Param.Basic BSmtLib.Facts.Proofs.Reader.Param.HandOver
open BSmtLib.Facts.Proofs.PublicApi.Collector
open BSmtLib.Facts.Proofs.Lexer.Consumers.RunE
open BSmtLibSpec.Lexer (Handed)

theorem eofResult_rel {α β : Type} {Q : α → β → Prop} {h₁ : Option (Span.Located α)}
    {h₂ : Option (Span.Located β)} {f₁ : ControlFlow (Span.Located α)}
    {f₂ : ControlFlow (Span.Located β)} (hh : ORel (LocRel Q) h₁ h₂)
    (hf : FlowRel (LocRel Q) f₁ f₂) :
    ORel (LocRel Q) (eofResult h₁ f₁) (eofResult h₂ f₂) := by
  match h₁, h₂, hh with
  | some _, some _, hh => exact hh
  | none, none, _ =>
    match f₁, f₂, hf with
    | .continue, .continue, _ => trivial
    | .break _, .break _, hf => exact hf

/-- The collector's run and the adapter's feeding of the library's lexer with the concrete
collector, from lexers with the same state and related held results: the collector writes down
the entries the other consumer takes, and ends with the same result, or with a related error. -/
theorem collect_runInputE : ∀ (slices : List ByteList) (lC : BSmtLib.Lexer Collector)
    (lA : BSmtLib.Lexer (Answering concreteCollector)) (taken : List Handed),
    Internal.core lC = Internal.core lA →
    ORel (LocRel link.rr) (Internal.held lC) (Internal.held lA) →
    ((collectWith lC slices).run (taken.map entryOf)).2 =
        ((runInputE BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps (consumer := concreteCollector) lA
          true slices).run taken).2.map entryOf ∧
      ERel (LexErrRel link.re) (ORel (LocRel link.rr))
        (resultOf ((collectWith lC slices).run (taken.map entryOf)).1)
        ((runInputE BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps (consumer := concreteCollector) lA
          true slices).run taken).1.1
  | [], lC, lA, taken, hcore, hheld => by
    have hsim := Reader.Param.Calls.lexEofStep_sim consumers
      (Recovery.LexerRecovery.abandon (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexerRecovery.recover (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexerRecovery.abandon (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast)
      (Recovery.LexerRecovery.recover (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast)
      abandon_link recover_link (Internal.core lC) (Internal.handler lC) (Internal.handler lA)
      taken
    obtain ⟨⟨hr, -⟩, ht⟩ := hsim
    rw [collectWith_nil]
    simp only [runInputE, ↓reduceIte, BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps]
    simp only [StateT.run_bind, run_collectM, BSmtLib.Facts.Proofs.Reader.Param.Flagged.run_answerM]
    rw [← hcore]
    generalize StateT.run (((Internal.lexEofStep (H := Collector) (m := CollectM) (R := Unit)
      (E := Empty) (Recovery.LexerRecovery.abandon Recovery.FailFast)
      (Recovery.LexerRecovery.recover Recovery.FailFast)).run (Internal.core lC)).run
        (Internal.handler lC)) (taken.map entryOf) = R1 at hr ht ⊢
    generalize StateT.run (((Internal.lexEofStep (H := Answering concreteCollector)
      (m := AnswerM) (R := concreteCollector.Result) (E := Option concreteCollector.Error)
      (Recovery.LexerRecovery.abandon Recovery.FailFast)
      (Recovery.LexerRecovery.recover Recovery.FailFast)).run (Internal.core lC)).run
        (Internal.handler lA)) taken = R2 at hr ht ⊢
    obtain ⟨⟨⟨r1, c1⟩, h1⟩, e1⟩ := R1
    obtain ⟨⟨⟨r2, c2⟩, h2⟩, e2⟩ := R2
    dsimp only at hr ht ⊢
    subst ht
    rcases r1 with e₁ | f1 <;> rcases r2 with e₂ | f2 <;> try exact absurd hr id
    · exact ⟨rfl, hr⟩
    · simp only [id_bind]
      refine ⟨rfl, ?_⟩
      simp only [resultOf, BSmtLib.Facts.Proofs.Reader.Param.Flagged.held_ofParts]
      exact eofResult_rel hheld hr
  | slice :: slices, lC, lA, taken, hcore, hheld => by
    have hsim := Reader.Param.Calls.lexSliceStep_sim consumers
      (Recovery.LexerRecovery.abandon (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexerRecovery.recover (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexerRecovery.abandon (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast)
      (Recovery.LexerRecovery.recover (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast)
      abandon_link recover_link slice.toByteArray.toByteSlice (Internal.core lC)
      (Internal.handler lC) (Internal.handler lA) taken
    obtain ⟨⟨hr, hc⟩, ht⟩ := hsim
    rw [collectWith_cons]
    simp only [runInputE, BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps]
    simp only [StateT.run_bind, run_collectM,
      BSmtLib.Facts.Proofs.Reader.Param.Flagged.run_answerM]
    rw [← hcore]
    generalize StateT.run (((Internal.lexSliceStep (H := Collector) (m := CollectM) (R := Unit)
      (E := Empty) (Recovery.LexerRecovery.abandon Recovery.FailFast)
      (Recovery.LexerRecovery.recover Recovery.FailFast) slice.toByteArray.toByteSlice).run
        (Internal.core lC)).run (Internal.handler lC)) (taken.map entryOf) = R1 at hr hc ht ⊢
    generalize StateT.run (((Internal.lexSliceStep (H := Answering concreteCollector)
      (m := AnswerM) (R := concreteCollector.Result) (E := Option concreteCollector.Error)
      (Recovery.LexerRecovery.abandon Recovery.FailFast)
      (Recovery.LexerRecovery.recover Recovery.FailFast) slice.toByteArray.toByteSlice).run
        (Internal.core lC)).run (Internal.handler lA)) taken = R2 at hr hc ht ⊢
    obtain ⟨⟨⟨r1, c1⟩, h1⟩, e1⟩ := R1
    obtain ⟨⟨⟨r2, c2⟩, h2⟩, e2⟩ := R2
    dsimp only at hr hc ht ⊢
    subst ht
    simp only [id_bind]
    rcases r1 with e₁ | d1 <;> rcases r2 with e₂ | d2 <;> try exact absurd hr id
    · exact ⟨rfl, hr⟩
    · exact collect_runInputE slices _ _ e2 hc
        (oRel_or hr (by
          simp only [BSmtLib.Facts.Proofs.Reader.Param.Flagged.held_ofParts]
          exact hheld))

end BSmtLib.Facts.Proofs.PublicApi.CollectE

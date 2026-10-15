module

public import BSmtLib.Facts.Proofs.PublicApi.CollectorW
public import BSmtLib.Facts.Proofs.PublicApi.VCollectE
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The Rust port with the collector against the adapter's feeding

The Rust port hands its batches over to the collector and to the adapter's consumer for the
concrete collector alike (`CollectorW.consumersW`). So the Rust port with the collector, fed
slices by its public calls (`Chain.collectBy`), takes the entries the Rust port with the
adapter's consumer takes fed them by the adapter (`RunE.runInputE`), and ends alike
(`collectW_runInputE`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.WCollectE

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Facts.PublicApi.Adapters BSmtLib.Facts.PublicApi.Adapters.Chain
open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Facts.Proofs.PublicApi.Collector BSmtLib.Facts.Proofs.PublicApi.CollectorW
open BSmtLib.Facts.Proofs.PublicApi.VCollectE (hrec₁ habandon₁)
open BSmtLib.Facts.Proofs.Lexer.Consumers.RunE BSmtLib.Facts.Proofs.PublicApi.CollectE
open BSmtLib.Facts.Proofs.Reader.ParamW.Calls
open BSmtLib.Lexer.Internal.WRustPort
open BSmtLibSpec.Lexer (Handed)

theorem eofResult_w {α : Type} (held : Option (Span.Located α))
    (flow : ControlFlow (Span.Located α)) :
    Lexer.Internal.WRustPort.Lexer.eofResult held flow =
      BSmtLib.Facts.Lexer.Adapters.eofResult held flow := by
  cases held <;> cases flow <;> rfl

abbrev WOps := BSmtLib.Facts.Lexer.Adapters.WRustPort.lexOps

/-- The Rust port with the collector fed slices by its public calls, and the Rust port with the
adapter's consumer for the concrete collector fed them by the adapter, from lexers with the same
state and related held results: the collector writes down the entries the other takes, and the
two end alike. -/
theorem collectW_runInputE : ∀ (slices : List ByteList)
    (L₁ : Lexer.Internal.WRustPort.Lexer Collector)
    (L₂ : Lexer.Internal.WRustPort.Lexer (Answering concreteCollector))
    (taken : List Handed), L₁.core = L₂.core → ORel (LocRel link.rr) L₁.held L₂.held →
    ((collectBy (fun lexer slice => Lexer.Internal.WRustPort.Lexer.lexSlice lexer slice)
        (fun lexer => Lexer.Internal.WRustPort.Lexer.lexEof lexer) L₁ slices).run
        (taken.map entryOf)).2 =
        ((runInputE WOps L₂ true slices).run taken).2.map entryOf ∧
      ERel (LexErrRel link.re) (ORel (LocRel link.rr))
        ((collectBy (fun lexer slice => Lexer.Internal.WRustPort.Lexer.lexSlice lexer slice)
          (fun lexer => Lexer.Internal.WRustPort.Lexer.lexEof lexer) L₁ slices).run
          (taken.map entryOf)).1
        ((runInputE WOps L₂ true slices).run taken).1.1
  | [], L₁, L₂, taken, hcore, hheld => by
    have hsim := lexEofStep_sim consumersW
      (Recovery.LexRecovery.abandon (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexRecovery.recover (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexRecovery.abandon (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast)
      (Recovery.LexRecovery.recover (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast) habandon₁ hrec₁ L₁.core L₁.handler L₂.handler taken
    simp only [collectBy, runInputE, ↓reduceIte, WOps, WRustPort.lexOps,
      Lexer.Internal.WRustPort.Lexer.lexEof, Lexer.Internal.WRustPort.Lexer.run, StateT.run_bind]
    rw [← hcore]
    obtain ⟨hr, he⟩ := hsim
    generalize StateT.run (((lexEofStep (H := Collector) (m := CollectM) (ops := Rust.ops)
      (Recovery.LexRecovery.abandon Recovery.FailFast) (Recovery.LexRecovery.recover
        Recovery.FailFast)).run L₁.core).run L₁.handler) (taken.map entryOf) = R1 at hr he ⊢
    generalize StateT.run (((lexEofStep (H := Answering concreteCollector) (m := AnswerM)
      (ops := Rust.ops) (Recovery.LexRecovery.abandon Recovery.FailFast)
        (Recovery.LexRecovery.recover Recovery.FailFast)).run L₁.core).run L₂.handler) taken = R2
        at hr he ⊢
    obtain ⟨⟨⟨r1, c1⟩, h1⟩, e1⟩ := R1
    obtain ⟨⟨⟨r2, c2⟩, h2⟩, e2⟩ := R2
    obtain ⟨hres, hcc⟩ := hr
    dsimp only at hres hcc he ⊢
    subst hcc he
    match r1, r2, hres with
    | .ok f1, .ok f2, hf =>
      refine ⟨rfl, ?_⟩
      show ORel _ (Lexer.Internal.WRustPort.Lexer.eofResult _ _) _
      rw [eofResult_w]
      exact eofResult_rel hheld hf
    | .error x1, .error x2, hx => exact ⟨rfl, hx⟩
  | slice :: slices, L₁, L₂, taken, hcore, hheld => by
    have hsim := lexSliceStep_sim consumersW
      (Recovery.LexRecovery.abandon (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexRecovery.recover (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexRecovery.abandon (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast)
      (Recovery.LexRecovery.recover (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast) habandon₁ hrec₁ slice.toByteArray.toByteSlice L₁.core L₁.handler
        L₂.handler taken
    simp only [collectBy, runInputE, WOps, WRustPort.lexOps,
      Lexer.Internal.WRustPort.Lexer.lexSlice, Lexer.Internal.WRustPort.Lexer.run,
      StateT.run_bind]
    rw [← hcore]
    obtain ⟨hr, he⟩ := hsim
    generalize StateT.run (((lexSliceStep (H := Collector) (m := CollectM) (ops := Rust.ops)
      (Recovery.LexRecovery.abandon Recovery.FailFast) (Recovery.LexRecovery.recover
        Recovery.FailFast) slice.toByteArray.toByteSlice).run L₁.core).run L₁.handler)
        (taken.map entryOf) = R1 at hr he ⊢
    generalize StateT.run (((lexSliceStep (H := Answering concreteCollector) (m := AnswerM)
      (ops := Rust.ops) (Recovery.LexRecovery.abandon Recovery.FailFast)
        (Recovery.LexRecovery.recover Recovery.FailFast)
          slice.toByteArray.toByteSlice).run L₁.core).run L₂.handler) taken = R2 at hr he ⊢
    obtain ⟨⟨⟨r1, c1⟩, h1⟩, e1⟩ := R1
    obtain ⟨⟨⟨r2, c2⟩, h2⟩, e2⟩ := R2
    obtain ⟨hres, hcc⟩ := hr
    dsimp only at hres hcc he ⊢
    subst hcc he
    match r1, r2, hres with
    | .ok d1, .ok d2, hd =>
      exact collectW_runInputE slices _ _ e2 rfl (oRel_or hd hheld)
    | .error x1, .error x2, hx => exact ⟨rfl, hx⟩

end BSmtLib.Facts.Proofs.PublicApi.WCollectE

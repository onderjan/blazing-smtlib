module

public import BSmtLib.Facts.Proofs.PublicApi.VLink
public import BSmtLib.Facts.Proofs.PublicApi.CollectE
public import BSmtLib.Facts.PublicApi.Adapters.Chain
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor

@[expose] public section

/-!
# The naive lexer with the collector against the adapter's feeding

The collector and the adapter's consumer for the concrete collector take the token of a cursor
over a lexeme alone alike: the same answer and the same cursor back, the collector writing down
the entry the other takes (`vConsumers`). So the naive lexer with the collector, fed slices by
its public calls (`Chain.collectBy`), takes the entries the naive lexer with the adapter's
consumer takes fed them by the adapter (`RunE.runInputE`), and ends alike (`collectV_runInputE`).
-/

namespace BSmtLib.Facts.Proofs.PublicApi.VCollectE

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Facts.PublicApi.Adapters BSmtLib.Facts.PublicApi.Adapters.Chain
open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Reader.Param.Basic
open BSmtLib.Facts.Proofs.PublicApi.Collector BSmtLib.Facts.Proofs.PublicApi.VLink
open BSmtLib.Facts.Proofs.Lexer.Consumers.RunE BSmtLib.Facts.Proofs.PublicApi.CollectE
open BSmtLib.Lexer.Internal.VNaive
open BSmtLibSpec.Lexer (Handed)

theorem len_batch (l : Lexeme) (h : l.Valid) : (l.batch h).len = 1 := by
  unfold Lexeme.batch Token.Internal.TokenBatch.pushLocated
  exact Token.Internal.TokenBatch.len_push ..

/-- The cursor over a lexeme alone has no token after its first. -/
theorem single_next (version : Version) (l : Lexeme) (h : l.Valid)
    (hn : (Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).HasNext) :
    ¬ ((Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).next hn).2.1.HasNext := by
  have := len_batch l h
  simp only [Lexer.Cursor.LexerCursor.HasNext, Lexer.Cursor.LexerCursor.next, Lexer.Cursor.LexerCursor.Internal.new,
    this]
  omega

/-- The two consumers take the token of a cursor over a lexeme alone alike. -/
theorem vConsumers : VConsumers link where
  concrete := rfl
  consume version l h := by
    intro a b taken
    rw [collector_consume_run]
    have e : ((Token.ConsumeFrom.consume (H := Answering concreteCollector) (m := AnswerM)
        (Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)) (l.hasNext h version)).run b).run
          taken =
        ((((Answering.consume concreteCollector (Lexer.Cursor.LexerCursor.Internal.new version (l.batch h))
          (l.hasNext h version)).run taken).1, b),
          ((Answering.consume concreteCollector (Lexer.Cursor.LexerCursor.Internal.new version (l.batch h))
          (l.hasNext h version)).run taken).2) := rfl
    rw [e, answering_step]
    have hs := single_next version l h (l.hasNext h version)
    by_cases he : (Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).category
        ((Lexer.Cursor.LexerCursor.Internal.new version (l.batch h)).peek (l.hasNext h version)) ==
          .endOfFile
    · simp only [he, ↓reduceIte, List.map_append, List.map_cons, List.map_nil,
        entryOf_handedAt]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> first | rfl | trivial
    · simp only [he, Bool.false_eq_true, ↓reduceIte, hs, ↓reduceDIte, List.map_append,
        List.map_cons, List.map_nil, entryOf_handedAt]
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> first | rfl | trivial

theorem eofResult_v {α : Type} (held : Option (Span.Located α))
    (flow : ControlFlow (Span.Located α)) :
    Lexer.Internal.VNaive.Lexer.eofResult held flow =
      BSmtLib.Facts.Lexer.Adapters.eofResult held flow := by
  cases held <;> cases flow <;> rfl

abbrev VOps := BSmtLib.Facts.Lexer.Adapters.VNaive.lexOps

theorem hrec₁ (l : Span.Location) :
    link.rc.rel (· = ·)
      (Recovery.LexerRecovery.recover (H := Collector) (m := CollectM) Recovery.FailFast l)
      (Recovery.LexerRecovery.recover (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast l) :=
  rel_pure (L := link) rfl

theorem habandon₁ (l : Span.Location) :
    link.rc.rel (· = ·)
      (Recovery.LexerRecovery.abandon (H := Collector) (m := CollectM) Recovery.FailFast l)
      (Recovery.LexerRecovery.abandon (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast l) :=
  rel_pure (L := link) rfl

/-- The naive lexer with the collector fed slices by its public calls, and the naive lexer with
the adapter's consumer for the concrete collector fed them by the adapter, from lexers with the
same state and related held results: the collector writes down the entries the other takes, and
the two end alike. -/
theorem collectV_runInputE : ∀ (slices : List ByteList)
    (L₁ : Lexer.Internal.VNaive.Lexer Collector) (L₂ : VOps.Lexer concreteCollector)
    (taken : List Handed), L₁.core = L₂.core → ORel (LocRel link.rr) L₁.held L₂.held →
    ((collectBy (fun lexer slice => Lexer.Internal.VNaive.Lexer.lexSlice lexer slice)
        (fun lexer => Lexer.Internal.VNaive.Lexer.lexEof lexer) L₁ slices).run
        (taken.map entryOf)).2 =
        ((runInputE VOps L₂ true slices).run taken).2.map entryOf ∧
      ERel (LexErrRel link.re) (ORel (LocRel link.rr))
        ((collectBy (fun lexer slice => Lexer.Internal.VNaive.Lexer.lexSlice lexer slice)
          (fun lexer => Lexer.Internal.VNaive.Lexer.lexEof lexer) L₁ slices).run
          (taken.map entryOf)).1
        ((runInputE VOps L₂ true slices).run taken).1.1
  | [], L₁, L₂, taken, hcore, hheld => by
    have hsim := lexEofStep_sim vConsumers
      (Recovery.LexerRecovery.abandon (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexerRecovery.recover (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexerRecovery.abandon (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast)
      (Recovery.LexerRecovery.recover (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast) hrec₁ L₁.core L₁.handler L₂.handler taken
    simp only [collectBy, runInputE, ↓reduceIte, VOps, VNaive.lexOps,
      Lexer.Internal.VNaive.Lexer.lexEof, Lexer.Internal.VNaive.Lexer.run, StateT.run_bind]
    rw [← hcore]
    simp only [show Recovery.Recovers.recovers Recovery.FailFast = false from rfl]
    obtain ⟨hr, he⟩ := hsim
    generalize StateT.run ((lexEofStep (H := Collector) (m := CollectM) false
      (Recovery.LexerRecovery.abandon Recovery.FailFast) (Recovery.LexerRecovery.recover
        Recovery.FailFast) L₁.core).run L₁.handler) (taken.map entryOf) = R1 at hr he ⊢
    generalize StateT.run ((lexEofStep (H := Answering concreteCollector) (m := AnswerM) false
      (Recovery.LexerRecovery.abandon Recovery.FailFast) (Recovery.LexerRecovery.recover
        Recovery.FailFast) L₁.core).run L₂.handler) taken = R2 at hr he ⊢
    obtain ⟨⟨⟨r1, c1⟩, h1⟩, e1⟩ := R1
    obtain ⟨⟨⟨r2, c2⟩, h2⟩, e2⟩ := R2
    obtain ⟨hres, hcc⟩ := hr
    dsimp only at hres hcc he ⊢
    subst hcc he
    match r1, r2, hres with
    | .ok f1, .ok f2, hf =>
      refine ⟨rfl, ?_⟩
      show ORel _ (Lexer.Internal.VNaive.Lexer.eofResult _ _) _
      rw [eofResult_v]
      exact eofResult_rel hheld hf
    | .error x1, .error x2, hx => exact ⟨rfl, hx⟩
  | slice :: slices, L₁, L₂, taken, hcore, hheld => by
    have hsim := lexSliceStep_sim vConsumers
      (Recovery.LexerRecovery.abandon (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexerRecovery.recover (H := Collector) (m := CollectM) Recovery.FailFast)
      (Recovery.LexerRecovery.abandon (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast)
      (Recovery.LexerRecovery.recover (H := Answering concreteCollector) (m := AnswerM)
        Recovery.FailFast) hrec₁ slice.toByteArray.toByteSlice L₁.core L₁.handler L₂.handler taken
    simp only [collectBy, runInputE, VOps, VNaive.lexOps,
      Lexer.Internal.VNaive.Lexer.lexSlice, Lexer.Internal.VNaive.Lexer.run, StateT.run_bind]
    rw [← hcore]
    simp only [show Recovery.Recovers.recovers Recovery.FailFast = false from rfl]
    obtain ⟨hr, he⟩ := hsim
    generalize StateT.run ((lexSliceStep (H := Collector) (m := CollectM) false
      (Recovery.LexerRecovery.abandon Recovery.FailFast) (Recovery.LexerRecovery.recover
        Recovery.FailFast) slice.toByteArray.toByteSlice L₁.core).run L₁.handler)
        (taken.map entryOf) = R1 at hr he ⊢
    generalize StateT.run ((lexSliceStep (H := Answering concreteCollector) (m := AnswerM) false
      (Recovery.LexerRecovery.abandon Recovery.FailFast) (Recovery.LexerRecovery.recover
        Recovery.FailFast) slice.toByteArray.toByteSlice L₁.core).run L₂.handler) taken = R2
        at hr he ⊢
    obtain ⟨⟨⟨r1, c1⟩, h1⟩, e1⟩ := R1
    obtain ⟨⟨⟨r2, c2⟩, h2⟩, e2⟩ := R2
    obtain ⟨hres, hcc⟩ := hr
    dsimp only at hres hcc he ⊢
    subst hcc he
    match r1, r2, hres with
    | .ok d1, .ok d2, hd =>
      exact collectV_runInputE slices _ _ e2 rfl (oRel_or hd hheld)
    | .error x1, .error x2, hx => exact ⟨rfl, hx⟩

end BSmtLib.Facts.Proofs.PublicApi.VCollectE

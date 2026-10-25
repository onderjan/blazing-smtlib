module

public import BSmtLib.Facts.Proofs.PublicApi.Collector
public import BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore
public import BSmtLib.Facts.Proofs.Lexer.X1BatchInCoreLexer
public import BSmtLib.Facts.Proofs.Lexer.Consumers.Ports
import all BSmtLib.Token
import all BSmtLib.Version
import all BSmtLib.Lexer.Cursor
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# The library's lexer after the end of an input

After the end of an input, the library's lexer is in the state it was constructed in but for its
storage: its content buffer and its batch keep the bytes and the entries of earlier tokens beyond
their lengths. The lexer reads nothing of that storage, so it lexes what follows as a new lexer
does. The two lexers are related through the Rust port, which makes a fresh batch for every
slice: each is related to the lexer with the batch kept in its state (`X1BatchInCore`) as the
library's lexer is (`X1BatchInCoreLexer`), and that lexer to one Rust port's lexer, whose states
agree with it but for storage (`WRustPortX1BatchInCore`). One Rust port's lexer related to both
makes their calls give the same results (`ZRel`).
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.PublicApi.Resets

open BSmtLib.Lexer BSmtLib.Lexer.Error
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Facts.PublicApi.Adapters
open BSmtLib.Facts.Proofs.Lexer BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
open BSmtLib.Facts.Proofs.Lexer.Simulation.Couple

variable {g g' : Token.BatchTag}

/-! ## The collector reads only the tokens of a cursor -/

theorem collector_consume_agree (c : LexerCursor g) (d : LexerCursor g')
    (hc : c.HasNext) (hd : d.HasNext) (h : CursorAgree c d) (a : Collector)
    (entries : List Entry) :
    (((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) c hc).run a).run
        entries).1.1.1 =
      (((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) d hd).run a).run
        entries).1.1.1 ∧
    (((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) c hc).run a).run entries).2 =
      (((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) d hd).run a).run entries).2 ∧
    (((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) c hc).run a).run
        entries).1.2 = a ∧
    (((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) d hd).run a).run
        entries).1.2 = a ∧
    CursorAgree (((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) c hc).run a).run
        entries).1.1.2.val
      (((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) d hd).run a).run
        entries).1.1.2.val := by
  obtain ⟨et, hag⟩ := h.takeNext hc hd
  have hlt := tokenIndex_next_lt hc h.bounded
  rw [Collector.collector_consume_run, Collector.collector_consume_run]
  have hcat : c.category (c.peek hc) = d.category (d.peek hd) :=
    h.category (by rw [tokenIndex_peek, tokenIndex_peek, h.next]) (by
      rw [tokenIndex_peek]; have := (Simulation.Batch.hasNext_iff c).mp hc; have := h.bounded
      omega)
  have hspan : c.span (c.peek hc) = d.span (d.peek hd) := h.span_peek hc hd
  refine ⟨by simp only [hcat], by simp only [Collector.entryAt, hcat, hspan], rfl, rfl, hag⟩

/-- The collector reads the cursors only below the length of their batches. -/
theorem collector_consumesAlike : ConsumesAlike Collector CollectM Unit Empty := by
  intro _ _ c d hc hd h s
  have hag := fun entries => collector_consume_agree c d hc hd h s entries
  refine ⟨fun entries =>
    (⟨((((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) c hc).run s).run
        entries).1.1, (((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) d hd).run
          s).run entries).1.1, s), (hag entries).1, (hag entries).2.2.2.2⟩,
      (((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) c hc).run s).run
        entries).2), ?_, ?_⟩
  · funext entries
    rfl
  · funext entries
    show _ = (((((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) d hd).run s).run
        entries).1.1, s), (((Token.ConsumeFrom.consume (H := Collector) (m := CollectM) c hc).run
          s).run entries).2)
    rw [(hag entries).2.1]
    rfl

/-! ## Two library's lexers related through one Rust port's lexer -/

theorem mcouple_collectM {α β : Type} {Rel : α → β → Prop} {a : CollectM α} {b : CollectM β}
    (h : MCouple Rel a b) (entries : List Entry) :
    Rel (a.run entries).1 (b.run entries).1 ∧ (a.run entries).2 = (b.run entries).2 := by
  obtain ⟨y, h1, h2⟩ := h
  subst h1 h2
  exact ⟨(y.run entries).1.property, rfl⟩

/-- The lexer of the Rust port and the lexer with the batch in its state, with the collector. -/
abbrev WLexer := Lexer.Internal.WRustPort.Lexer Collector Lexer.Recovery.FailFast

/-- Two library's lexers with the collector, each related to a lexer with the batch in its state
as the library's lexer is to it, and both of these to one Rust port's lexer. -/
def ZRel (l₁ l₂ : BSmtLib.Lexer Collector) : Prop :=
  ∃ x₁ x₂ w : WLexer, X1BatchInCoreLexer.Top.LexerRel l₁ x₁ ∧
    WRustPortX1BatchInCore.Calls.LexRel w x₁ ∧ WRustPortX1BatchInCore.Calls.LexRel w x₂ ∧
    X1BatchInCoreLexer.Top.LexerRel l₂ x₂

/-- What a fresh lexer gives up after failing. -/
abbrev abandonC := Recovery.LexerRecovery.abandon (H := Collector) (m := CollectM) Recovery.FailFast

/-- What a fresh lexer reports after recovering. -/
abbrev recoverC := Recovery.LexerRecovery.recover (H := Collector) (m := CollectM) Recovery.FailFast

/-- Related lexers lex a slice that ends below `USize.size` alike: the same result, the same
entries written down, and related lexers again. -/
theorem step_fit {l₁ l₂ : BSmtLib.Lexer Collector} (h : ZRel l₁ l₂) (slice : ByteSlice)
    (hs : slice.stop < USize.size) (entries : List Entry) :
    ((Internal.run l₁ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC recoverC
        slice)).run entries).1.1 =
      ((Internal.run l₂ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC recoverC
        slice)).run entries).1.1 ∧
    ((Internal.run l₁ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC recoverC
        slice)).run entries).2 =
      ((Internal.run l₂ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC recoverC
        slice)).run entries).2 ∧
    ZRel ((Internal.run l₁ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC recoverC
        slice)).run entries).1.2
      ((Internal.run l₂ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC recoverC
        slice)).run entries).1.2 := by
  obtain ⟨x₁, x₂, w, h₁, hw₁, hw₂, h₂⟩ := h
  obtain ⟨⟨a1, a2⟩, a3⟩ := mcouple_collectM (X1BatchInCoreLexer.X1BatchInCore.lexSliceStep_sim_lexer
    abandonC recoverC l₁ x₁ h₁ slice hs) entries
  obtain ⟨⟨b1, b2⟩, b3⟩ := mcouple_collectM (X1BatchInCoreLexer.X1BatchInCore.lexSliceStep_sim_lexer
    abandonC recoverC l₂ x₂ h₂ slice hs) entries
  obtain ⟨⟨c1, c2⟩, c3⟩ := mcouple_collectM
    (WRustPortX1BatchInCore.WRustPort.run_lexSliceStep_sim_x1BatchInCore collector_consumesAlike
      abandonC recoverC slice w x₁ hw₁) entries
  obtain ⟨⟨d1, d2⟩, d3⟩ := mcouple_collectM
    (WRustPortX1BatchInCore.WRustPort.run_lexSliceStep_sim_x1BatchInCore collector_consumesAlike
      abandonC recoverC slice w x₂ hw₂) entries
  exact ⟨a1.trans (c1.symm.trans (d1.trans b1.symm)), a3.trans (c3.symm.trans (d3.trans b3.symm)),
    _, _, _, a2, c2, d2, b2⟩

/-- Related lexers lex the end of the input alike. -/
theorem step_eof {l₁ l₂ : BSmtLib.Lexer Collector} (h : ZRel l₁ l₂) (entries : List Entry) :
    ((Internal.run l₁ (Internal.lexEofStep (R := Unit) (E := Empty) abandonC recoverC)).run
        entries).1.1 =
      ((Internal.run l₂ (Internal.lexEofStep (R := Unit) (E := Empty) abandonC recoverC)).run
        entries).1.1 ∧
    ((Internal.run l₁ (Internal.lexEofStep (R := Unit) (E := Empty) abandonC recoverC)).run
        entries).2 =
      ((Internal.run l₂ (Internal.lexEofStep (R := Unit) (E := Empty) abandonC recoverC)).run
        entries).2 ∧
    ZRel ((Internal.run l₁ (Internal.lexEofStep (R := Unit) (E := Empty) abandonC
        recoverC)).run entries).1.2
      ((Internal.run l₂ (Internal.lexEofStep (R := Unit) (E := Empty) abandonC recoverC)).run
        entries).1.2 := by
  obtain ⟨x₁, x₂, w, h₁, hw₁, hw₂, h₂⟩ := h
  obtain ⟨⟨a1, a2⟩, a3⟩ := mcouple_collectM
    (X1BatchInCoreLexer.X1BatchInCore.lexEofStep_sim_lexer
      abandonC recoverC l₁ x₁ h₁) entries
  obtain ⟨⟨b1, b2⟩, b3⟩ := mcouple_collectM
    (X1BatchInCoreLexer.X1BatchInCore.lexEofStep_sim_lexer
      abandonC recoverC l₂ x₂ h₂) entries
  obtain ⟨⟨c1, c2⟩, c3⟩ := mcouple_collectM
    (WRustPortX1BatchInCore.WRustPort.run_lexEofStep_sim_x1BatchInCore
      collector_consumesAlike abandonC recoverC w x₁ hw₁) entries
  obtain ⟨⟨d1, d2⟩, d3⟩ := mcouple_collectM
    (WRustPortX1BatchInCore.WRustPort.run_lexEofStep_sim_x1BatchInCore
      collector_consumesAlike abandonC recoverC w x₂ hw₂) entries
  exact ⟨a1.trans (c1.symm.trans (d1.trans b1.symm)), a3.trans (c3.symm.trans (d3.trans b3.symm)),
    _, _, _, a2, c2, d2, b2⟩

theorem run_bind_collect {α β : Type} (x : CollectM α) (k : α → CollectM β)
    (entries : List Entry) : (x >>= k).run entries = (k (x.run entries).1).run (x.run entries).2 :=
  (rfl)

theorem run_bind {α β : Type} (l : BSmtLib.Lexer Collector) (f : InnerM Collector CollectM α)
    (k : α → InnerM Collector CollectM β) :
    Internal.run l (f >>= k) = (Internal.run l f >>= fun p => Internal.run p.2 (k p.1)) := (rfl)

theorem run_pure {α : Type} (l : BSmtLib.Lexer Collector) (a : α) :
    Internal.run l (Pure.pure a : InnerM Collector CollectM α) = Pure.pure (a, l) := (rfl)

/-- Related lexers lex the chunks of a slice from a position alike. -/
theorem step_chunks (slice : ByteSlice) : ∀ (n position : Nat), slice.size - position < n →
    ∀ (held : Option (Span.Located Unit)) {l₁ l₂ : BSmtLib.Lexer Collector}, ZRel l₁ l₂ →
    ∀ entries : List Entry,
    ((Internal.run l₁ (Internal.lexChunks (R := Unit) (E := Empty) abandonC recoverC slice
        position held)).run entries).1.1 =
      ((Internal.run l₂ (Internal.lexChunks (R := Unit) (E := Empty) abandonC recoverC slice
        position held)).run entries).1.1 ∧
    ((Internal.run l₁ (Internal.lexChunks (R := Unit) (E := Empty) abandonC recoverC slice
        position held)).run entries).2 =
      ((Internal.run l₂ (Internal.lexChunks (R := Unit) (E := Empty) abandonC recoverC slice
        position held)).run entries).2 ∧
    ZRel ((Internal.run l₁ (Internal.lexChunks (R := Unit) (E := Empty) abandonC recoverC slice
        position held)).run entries).1.2
      ((Internal.run l₂ (Internal.lexChunks (R := Unit) (E := Empty) abandonC recoverC slice
        position held)).run entries).1.2
  | 0, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, position, hn => by
    intro held l₁ l₂ h entries
    rw [Internal.lexChunks.eq_def]
    by_cases hp : position < slice.size
    · simp only [hp, dite_true]
      rw [run_bind, run_bind]
      have hfit : ∀ (s : ByteSlice) (hs : s.stop < USize.size),
          Internal.lexSliceFitting (H := Collector) (m := CollectM) (R := Unit) (E := Empty)
            abandonC recoverC s hs =
          Internal.lexSliceStep abandonC recoverC s := by
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
      obtain ⟨e1, e2, hz⟩ := step_fit h chunk hsize entries
      rw [run_bind_collect, run_bind_collect]
      generalize (Internal.run l₁ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC
        recoverC chunk)).run entries = A at e1 e2 hz ⊢
      generalize (Internal.run l₂ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC
        recoverC chunk)).run entries = B at e1 e2 hz ⊢
      obtain ⟨⟨r₁, l₁'⟩, t₁⟩ := A
      obtain ⟨⟨r₂, l₂'⟩, t₂⟩ := B
      dsimp only at e1 e2 hz ⊢
      subst e1 e2
      cases r₁ with
      | ok held' =>
        exact step_chunks slice n _ (by simp only [Internal.CHUNK_SIZE] at *; omega) _ hz t₁
      | error err =>
        simp only
        rw [run_pure, run_pure]
        exact ⟨rfl, rfl, hz⟩
    · simp only [hp, dite_false]
      rw [run_pure, run_pure]
      exact ⟨rfl, rfl, h⟩

/-- Related lexers lex a slice alike. -/
theorem step_slice {l₁ l₂ : BSmtLib.Lexer Collector} (h : ZRel l₁ l₂) (slice : ByteSlice)
    (entries : List Entry) :
    ((Internal.run l₁ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC recoverC
        slice)).run entries).1.1 =
      ((Internal.run l₂ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC recoverC
        slice)).run entries).1.1 ∧
    ((Internal.run l₁ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC recoverC
        slice)).run entries).2 =
      ((Internal.run l₂ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC recoverC
        slice)).run entries).2 ∧
    ZRel ((Internal.run l₁ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC recoverC
        slice)).run entries).1.2
      ((Internal.run l₂ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC recoverC
        slice)).run entries).1.2 := by
  by_cases hs : slice.stop < USize.size
  · exact step_fit h slice hs entries
  · unfold Internal.lexSliceStep
    rw [dite_eq_right_of_eq_false (eq_false hs)]
    exact step_chunks slice _ 0 (Nat.lt_succ_self _) none h entries

theorem ZRel.held {l₁ l₂ : BSmtLib.Lexer Collector} (h : ZRel l₁ l₂) :
    Internal.held l₁ = Internal.held l₂ := by
  obtain ⟨x₁, x₂, w, h₁, hw₁, hw₂, h₂⟩ := h
  exact h₁.2.2.symm.trans (hw₁.2.2.symm.trans (hw₂.2.2.trans h₂.2.2))

theorem ZRel.withHeld {l₁ l₂ : BSmtLib.Lexer Collector} (h : ZRel l₁ l₂)
    (held : Option (Span.Located Unit)) :
    ZRel (Internal.withHeld l₁ held) (Internal.withHeld l₂ held) := by
  obtain ⟨x₁, x₂, w, h₁, hw₁, hw₂, h₂⟩ := h
  exact ⟨{ x₁ with held }, { x₂ with held }, { w with held }, ⟨h₁.1, h₁.2.1, rfl⟩,
    ⟨hw₁.1, hw₁.2.1, rfl⟩, ⟨hw₂.1, hw₂.2.1, rfl⟩, ⟨h₂.1, h₂.2.1, rfl⟩⟩

theorem run_map_collect {α β : Type} (f : α → β) (x : CollectM α) (entries : List Entry) :
    (f <$> x).run entries = (f (x.run entries).1, (x.run entries).2) := (rfl)

/-- Related lexers with the collector, fed the same slices and then the end of the input, give
the same result and write down the same entries. -/
theorem collectWith_rel : ∀ (slices : List ByteList) {l₁ l₂ : BSmtLib.Lexer Collector},
    ZRel l₁ l₂ → ∀ entries : List Entry,
    (resultOf <$> collectWith l₁ slices).run entries =
      (resultOf <$> collectWith l₂ slices).run entries
  | [], l₁, l₂, h, entries => by
    rw [Collector.collectWith_nil, Collector.collectWith_nil, run_map_collect, run_map_collect,
      run_bind_collect, run_bind_collect]
    obtain ⟨e1, e2, hz⟩ := step_eof h entries
    generalize (Internal.run l₁ (Internal.lexEofStep (R := Unit) (E := Empty) abandonC
      recoverC)).run entries = A at e1 e2 hz ⊢
    generalize (Internal.run l₂ (Internal.lexEofStep (R := Unit) (E := Empty) abandonC
      recoverC)).run entries = B at e1 e2 hz ⊢
    obtain ⟨⟨r₁, l₁'⟩, t₁⟩ := A
    obtain ⟨⟨r₂, l₂'⟩, t₂⟩ := B
    simp only at e1 e2 hz
    subst e1 e2
    cases r₁ with
    | ok flow =>
      show (resultOf (.ok (eofResult (Internal.held l₁') flow, _)), t₁) =
        (resultOf (.ok (eofResult (Internal.held l₂') flow, _)), t₁)
      rw [hz.held]
      rfl
    | error e => rfl
  | slice :: slices, l₁, l₂, h, entries => by
    rw [Collector.collectWith_cons, Collector.collectWith_cons, run_map_collect, run_map_collect,
      run_bind_collect, run_bind_collect]
    obtain ⟨e1, e2, hz⟩ := step_slice h slice.toByteArray.toByteSlice entries
    generalize (Internal.run l₁ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC
      recoverC slice.toByteArray.toByteSlice)).run entries = A at e1 e2 hz ⊢
    generalize (Internal.run l₂ (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC
      recoverC slice.toByteArray.toByteSlice)).run entries = B at e1 e2 hz ⊢
    obtain ⟨⟨r₁, l₁'⟩, t₁⟩ := A
    obtain ⟨⟨r₂, l₂'⟩, t₂⟩ := B
    simp only at e1 e2 hz
    subst e1 e2
    cases r₁ with
    | ok held =>
      have hz' : ZRel (Internal.withHeld l₁' (held.or (Internal.held l₁')))
          (Internal.withHeld l₂' (held.or (Internal.held l₂'))) := by
        rw [← hz.held]
        exact hz.withHeld _
      exact collectWith_rel slices hz' t₁
    | error e => rfl

/-! ## What the end of an input leaves of the lexer's fields

The lexer never changes the version it was constructed with nor whether it recovers. That is read
off the chain of lexers with the adapter's consumer for the concrete collector: the Rust port's
state corresponds to the naive lexer's (`VNaiveWRustPort.Calls.CR`), which keeps both. -/

open BSmtLib.Facts.Lexer.Adapters (Answering AnswerM)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Alike BSmtLib.Facts.Proofs.Lexer.Consumers.AlikeF
open BSmtLib.Facts.Proofs.PublicApi.Collector (concreteCollector)

abbrev ZOps := BSmtLib.Facts.Lexer.Adapters.Lexer.lexOps
abbrev XOps := BSmtLib.Facts.Lexer.Adapters.X1BatchInCore.lexOps
abbrev WOps := BSmtLib.Facts.Lexer.Adapters.WRustPort.lexOps
abbrev VOps := BSmtLib.Facts.Lexer.Adapters.VNaive.lexOps

/-- The library's lexer with the adapter's consumer for the concrete collector, fed an input to
the end without failing, has the version it was constructed with as its initial one, and does not
recover. -/
theorem fields_after (version : Version) (slices : List BSmtLibSpec.Regex.Chars)
    (hok : ((ZOps.runInput (ZOps.new concreteCollector {} version) true slices).run
      []).1.1.isFailed = false) :
    (Internal.core ((ZOps.runInput (ZOps.new concreteCollector {} version) true slices).run
        []).1.2).recovers = false ∧
      (Internal.core ((ZOps.runInput (ZOps.new concreteCollector {} version) true slices).run
        []).1.2).initialVersion = version := by
  -- the library's lexer and the lexer with the batch in its state, fed the input cut
  obtain ⟨z1, -, -, z4⟩ := BSmtLib.Facts.Proofs.Lexer.Consumers.ChainZ.runInput_cut true slices
    (ZOps.new concreteCollector {} version) (XOps.new concreteCollector {} version) []
    (X1BatchInCoreLexer.Handed.lexerRel_new _ _)
  have hz := z4 hok
  -- the Rust port and the lexer with the batch in its state
  obtain ⟨x1, x2, -⟩ := runInput_alike WOps XOps
    WRustPortX1BatchInCore.Calls.LexRel
    (BSmtLib.Facts.Proofs.Lexer.Consumers.ChainX1.slice_alike concreteCollector)
    (BSmtLib.Facts.Proofs.Lexer.Consumers.ChainX1.eof_alike concreteCollector)
    (fun _ _ h => h.2.2) (fun _ _ _ h => ⟨h.1, h.2.1, rfl⟩) true
    (X1BatchInCoreLexer.Chunks.cutAll slices)
    (WOps.new concreteCollector {} version) (XOps.new concreteCollector {} version) []
    (WRustPortX1BatchInCore.Handed.new_rel _ _)
  -- the Rust port and the naive lexer
  obtain ⟨v1, -, v3, -⟩ := runInput_alikeF WOps VOps
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.WVRel concreteCollector)
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.WVWeak concreteCollector)
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wv_slice concreteCollector)
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wv_eof concreteCollector)
    (fun _ _ h => h.1) (fun _ _ _ h => ⟨rfl, h.2⟩)
    (fun _ _ h => ⟨h.2.version, BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.cr_weak h.2⟩)
    true (X1BatchInCoreLexer.Chunks.cutAll slices)
    (WOps.new concreteCollector {} version) (VOps.new concreteCollector {} version) []
    (BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls.wvRel_new _ _)
  have hw := v3 (by rw [x1, ← z1]; exact hok)
  have hv := BSmtLib.Facts.Proofs.Lexer.Consumers.VReset.runInput_reset concreteCollector
    (X1BatchInCoreLexer.Chunks.cutAll slices)
    (Lexer.Internal.VNaive.Core.initial version) none [] trivial
  have hrel := hz.2.1
  have hr1 := congrArg (·.recovers) hrel
  have hr2 := congrArg (·.initialVersion) hrel
  simp only [X1BatchInCoreLexer.Outer.zb,
    X1BatchInCoreLexer.Outer.zm,
    X1BatchInCoreLexer.Core.coreMap] at hr1 hr2
  refine ⟨hr1.symm.trans ((x2.2.1.1.recovers).symm.trans hw.2.recovers), ?_⟩
  exact hr2.symm.trans ((x2.2.1.1.initialVersion).symm.trans (hw.2.initial.trans hv.2.1))

/-! ## The state after the end of the input -/

/-- The state that the end of the input leaves: `Internal.reset` applied. -/
def resetOf (c : LexerCore) : LexerCore :=
  { c with
    version := c.initialVersion
    state := .normal
    discardedFrom := none
    holding := false
    consumedDepth := 0
    lexedDepth := 0
    recoveryState := none
    tokenStart := Span.Location.initial
    tokenContent := c.tokenContent.clear
    offset := 0
    line := 0
    base := 0
    lineStart := 0
    batch := c.batch.clear 0
    tokenStarted := .inl rfl
    batchEnded := Nat.le_of_eq (Token.Internal.TokenBatch.lastEnd_clear _ _) }

abbrev irun {α : Type} (x : InnerM Collector CollectM α) (c : LexerCore) (h : Collector)
    (entries : List Entry) :=
  ((x.run c).run h).run entries

theorem irun_bind {α β : Type} (x : InnerM Collector CollectM α)
    (k : α → InnerM Collector CollectM β) (c h entries) :
    irun (x >>= k) c h entries =
      irun (k (irun x c h entries).1.1.1) (irun x c h entries).1.1.2 (irun x c h entries).1.2
        (irun x c h entries).2 := (rfl)

theorem irun_reset (c h entries) :
    irun (Internal.reset (H := Collector) (m := CollectM)) c h entries =
      ((((), resetOf c), h), entries) := (rfl)

/-- What the end of the input does after its inner step, ending successfully only where it
resets the state. -/
theorem tail_ok (x : InnerM Collector CollectM
      (Except (Failure Empty) (ControlFlow (Span.Located Unit))))
    (K : Except (Failure Empty) (ControlFlow (Span.Located Unit)) →
      InnerM Collector CollectM (Except (LexerError Empty) (ControlFlow (Span.Located Unit))))
    (hok : ∀ flow, K (.ok flow) = (Internal.reset >>= fun _ => Pure.pure (.ok flow)))
    (herr : ∀ f c h entries, ∃ e, (irun (K (.error f)) c h entries).1.1.1 = .error e)
    {c : LexerCore} {h : Collector} {entries : List Entry}
    {flow : ControlFlow (Span.Located Unit)} {c' : LexerCore} {h' : Collector}
    {entries' : List Entry}
    (hrun : irun (x >>= K) c h entries = (((.ok flow, c'), h'), entries')) :
    ∃ c₀, c' = resetOf c₀ := by
  rw [irun_bind] at hrun
  generalize irun x c h entries = R at hrun
  obtain ⟨⟨⟨r, c₁⟩, h₁⟩, e₁⟩ := R
  cases r with
  | ok f =>
    simp only at hrun
    rw [hok, irun_bind, irun_reset] at hrun
    exact ⟨c₁, (congrArg (·.1.1.2) hrun).symm⟩
  | error failure =>
    simp only at hrun
    obtain ⟨e, he⟩ := herr failure c₁ h₁ e₁
    rw [hrun] at he
    cases he

/-- A successful end of the input leaves the lexer's state reset. -/
theorem eofStep_ok {c : LexerCore} {h : Collector} {entries : List Entry}
    {flow : ControlFlow (Span.Located Unit)} {c' : LexerCore} {h' : Collector}
    {entries' : List Entry}
    (hrun : irun (Internal.lexEofStep (R := Unit) (E := Empty) abandonC recoverC) c h entries =
      (((.ok flow, c'), h'), entries')) : ∃ c₀, c' = resetOf c₀ := by
  unfold Internal.lexEofStep at hrun
  rw [irun_bind] at hrun
  simp only at hrun
  split at hrun
  · rw [irun_bind, irun_bind, irun_bind] at hrun
    exact tail_ok _ _ (fun _ => rfl) (fun _ _ _ _ => ⟨_, rfl⟩) hrun
  · exact tail_ok _ _ (fun _ => rfl) (fun _ _ _ _ => ⟨_, rfl⟩) hrun

theorem run_parts {α : Type} (l : BSmtLib.Lexer Collector) (x : InnerM Collector CollectM α)
    (entries : List Entry) :
    (Internal.run l x).run entries =
      (((irun x (Internal.core l) (Internal.handler l) entries).1.1.1,
        Internal.ofParts (irun x (Internal.core l) (Internal.handler l) entries).1.2
          (irun x (Internal.core l) (Internal.handler l) entries).1.1.2 (Internal.held l)),
        (irun x (Internal.core l) (Internal.handler l) entries).2) := (rfl)

/-- A run that reads an input to the end ends with a successful end of the input, which leaves
the lexer reset and holding nothing. -/
theorem collectWith_ok : ∀ (slices : List ByteList) (l : BSmtLib.Lexer Collector)
    (entries : List Entry) (result : Option (Span.Located Unit)) (lexer : BSmtLib.Lexer Collector)
    (entries' : List Entry),
    (collectWith l slices).run entries = (.ok (result, lexer), entries') →
    (∃ c₀, Internal.core lexer = resetOf c₀) ∧ Internal.held lexer = none
  | [], l, entries, result, lexer, entries', h => by
    rw [Collector.collectWith_nil, run_bind_collect, run_parts] at h
    generalize hR : irun (Internal.lexEofStep (R := Unit) (E := Empty) abandonC recoverC)
      (Internal.core l) (Internal.handler l) entries = R at h
    obtain ⟨⟨⟨r, c'⟩, h'⟩, e'⟩ := R
    cases r with
    | ok flow =>
      simp only at h
      cases h
      exact ⟨eofStep_ok hR, rfl⟩
    | error e =>
      simp only at h
      cases h
  | slice :: slices, l, entries, result, lexer, entries', h => by
    rw [Collector.collectWith_cons, run_bind_collect] at h
    generalize (Internal.run l (Internal.lexSliceStep (R := Unit) (E := Empty) abandonC recoverC
      slice.toByteArray.toByteSlice)).run entries = R at h
    obtain ⟨⟨r, l'⟩, e'⟩ := R
    cases r with
    | ok held => exact collectWith_ok slices _ _ _ _ _ h
    | error e =>
      simp only at h
      cases h

/-! ## The lexer after the end of an input, and a new one -/

/-- A reset state of a lexer constructed with the version, which does not recover, corresponds
to the state of a new Rust port's lexer but for its storage. -/
theorem coreRel_reset (version : Version) (c₀ : LexerCore)
    (hiv : c₀.initialVersion = version) (hrec : c₀.recovers = false) :
    WRustPortX1BatchInCore.Core.CoreRel
      (Lexer.Internal.WRustPort.Lexer.new Collector.mk version).core
      (X1BatchInCoreLexer.Core.coreMap 0 (resetOf c₀)) where
  initialVersion := hiv.symm
  state := rfl
  discardedFrom := rfl
  holding := rfl
  recovers := hrec.symm
  consumedDepth := rfl
  lexedDepth := rfl
  recoveryState := rfl
  tokenStart := rfl
  tokenContent := ContentAgree.empty_clear _
  offset := rfl
  base := rfl
  line := rfl
  lineStart := rfl
  version := hiv.symm
  batch := agree_of_len_zero rfl rfl
  capacity := WRustPortX1BatchInCore.Core.zero_lt_capacity

/-- The library's lexer with the collector after an input it read to the end, and a new one
constructed with the same version, are related. -/
theorem zRel_after (version : Version) (first : List ByteList)
    (result : Option (Span.Located Unit)) (lexer : BSmtLib.Lexer Collector) (log : List Entry)
    (h : (collectWith (BSmtLib.Lexer.new Collector.mk version) first).run [] =
      (.ok (result, lexer), log)) :
    ZRel lexer (BSmtLib.Lexer.new Collector.mk version) := by
  obtain ⟨⟨c₀, hc₀⟩, hheld⟩ := collectWith_ok first _ [] _ _ _ h
  obtain ⟨-, hb, hcore⟩ := Collector.collect_runInput first (BSmtLib.Lexer.new Collector.mk version)
    (ZOps.new concreteCollector {} version) [] (rfl) trivial
  simp only [List.map_nil, h] at hb hcore
  have hok : ((ZOps.runInput (ZOps.new concreteCollector {} version) true first).run
      []).1.1.isFailed = false := by
    revert hb
    cases ((ZOps.runInput (ZOps.new concreteCollector {} version) true first).run
      []).1.1.isFailed <;> simp [resultOf, Except.toBool]
  obtain ⟨hrec, hiv⟩ := fields_after version first hok
  rw [← hcore result lexer rfl, hc₀] at hrec hiv
  refine ⟨⟨Internal.handler lexer, X1BatchInCoreLexer.Core.coreMap 0 (Internal.core lexer),
    Internal.held lexer⟩, Lexer.Internal.WRustPort.Lexer.new Collector.mk version,
    Lexer.Internal.WRustPort.Lexer.new Collector.mk version,
    ⟨rfl, X1BatchInCoreLexer.Outer.rel_coreMap 0 _, rfl⟩, ⟨rfl, ⟨?_, rfl⟩, ?_⟩,
    WRustPortX1BatchInCore.Handed.new_rel _ _, X1BatchInCoreLexer.Handed.lexerRel_new _ _⟩
  · rw [hc₀]
    exact coreRel_reset version c₀ hiv hrec
  · exact hheld.symm

/-- The library's lexer with the collector, after an input it read to the end, lexes the next
input as a new lexer constructed with the same version does. -/
theorem resets (version : Version) (first : List ByteList) (log : List Entry)
    (result : Option (Span.Located Unit)) (lexer : BSmtLib.Lexer Collector)
    (h : (collectWith (BSmtLib.Lexer.new Collector.mk version) first).run [] =
      (.ok (result, lexer), log))
    (next : List ByteList) :
    (resultOf <$> collectWith lexer next).run [] =
      (resultOf <$> collectWith (BSmtLib.Lexer.new Collector.mk version) next).run [] :=
  collectWith_rel next (zRel_after version first result lexer log h) []

end BSmtLib.Facts.Proofs.PublicApi.Resets

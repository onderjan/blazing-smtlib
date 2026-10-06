import BSmtLib.Proofs.V1NaiveV2Batched.Cursor

/-!
# Handing a batch over to the adapter's consumer

The adapter's consumer `Collector`, handed a cursor over a batch of lexemes, records the
lexemes as the naive lexer's hand-overs of each alone would (`handOverCursor_batch`,
`flush_batch`), or fails if one of them is whitespace or a comment.
-/

namespace BSmtLib.Proofs.Lexer.V1NaiveV2Batched

open BSmtLib.Lexer.Internal (intoBatch)
open BSmtLib.Proofs.Adapter V1Naive V2Batched

variable {g : BatchTag}

theorem drop_eq_cons (b : Array Lexeme) (j : Nat) (hj : j < b.size) :
    b.toList.drop j = b[j] :: b.toList.drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simpa using hj)]
  simp

theorem takeRest_batch (b : Array Lexeme) (hb0 : Ordered 0 b.toList) :
    ∀ n (c : BatchCursor g), c.remaining = n →
    intoBatch c = toTokenBatch b hb0 → idx c + c.remaining = b.size →
    (takeRest c).1 = (b.toList.drop (idx c)).mapM (lexemeHanded c.version) ∧
    ((takeRest c).1 ≠ none → (takeRest c).2.1.remaining = 0) ∧
    (takeRest c).2.1.version = c.version ∧
    (takeRest c).2.1.relexRequested = c.relexRequested := by
  intro n
  induction n with
  | zero =>
    intro c hn hb hs
    have hnh : ¬ c.HasNext := by rw [hasNext_iff]; omega
    rw [takeRest]
    simp only [hnh, dite_false]
    rw [List.drop_eq_nil_of_le (by simp; omega)]
    simp [hn]
  | succ n ih =>
    intro c hn hb hs
    have hh : c.HasNext := by rw [hasNext_iff]; omega
    have hr := remaining_next c hh
    have hi := idx_next c hh
    have hj : idx c < b.size := by omega
    obtain ⟨i1, i2, i3, i4⟩ := ih (c.next hh).2.1 (by omega) (by rw [intoBatch_next]; exact hb)
      (by omega)
    rw [takeRest]
    simp only [hh, dite_true]
    rw [toHanded_batch b hb0 c hh hb hj, drop_eq_cons b _ hj, List.mapM_cons]
    cases hl : lexemeHanded c.version b[idx c] with
    | none =>
      exact ⟨rfl, fun h => absurd rfl h, rfl, rfl⟩
    | some x =>
      rw [version_next, hi] at i1
      rw [version_next] at i3
      rw [relex_next] at i4
      refine ⟨?_, ?_, i3, i4⟩
      · rw [i1]
        cases (b.toList.drop (idx c + 1)).mapM (lexemeHanded c.version) <;> rfl
      · intro hne
        apply i2
        intro hn'
        rw [hn'] at hne
        exact hne rfl

/-- What the consumer does with a cursor over a batch of lexemes. -/
theorem consume_batch (b : Array Lexeme) (hb0 : Ordered 0 b.toList) (c : BatchCursor g)
    (h : c.HasNext) (hb : intoBatch c = toTokenBatch b hb0) (hs : idx c + c.remaining = b.size)
    (coll : Collector) :
    (∀ hs', (b.toList.drop (idx c)).mapM (lexemeHanded c.version) = some hs' →
      ((Consume.consume (H := Collector) c h).run coll).1.1 = .ok .continue ∧
      ((Consume.consume (H := Collector) c h).run coll).2.handed = coll.handed ++ hs' ∧
      ((Consume.consume (H := Collector) c h).run coll).1.2.1.remaining = 0 ∧
      ((Consume.consume (H := Collector) c h).run coll).1.2.1.version = c.version ∧
      ((Consume.consume (H := Collector) c h).run coll).1.2.1.relexRequested =
        c.relexRequested) ∧
    ((b.toList.drop (idx c)).mapM (lexemeHanded c.version) = none →
      ((Consume.consume (H := Collector) c h).run coll).1.1 = .error ()) := by
  have hr := remaining_next c h
  have hi := idx_next c h
  have hj : idx c < b.size := by rw [hasNext_iff] at h; omega
  obtain ⟨i1, i2, i3, i4⟩ := takeRest_batch b hb0 _ (c.next h).2.1 rfl
    (by rw [intoBatch_next]; exact hb) (by omega)
  rw [version_next, hi] at i1
  rw [version_next] at i3
  rw [relex_next] at i4
  simp only [Consume.consume]
  rw [toHanded_batch b hb0 c h hb hj, drop_eq_cons b _ hj, List.mapM_cons]
  cases hl : lexemeHanded c.version b[idx c] with
  | none =>
    refine ⟨fun hs' h' => ?_, fun _ => rfl⟩
    simp at h'
  | some x =>
    generalize hrest : takeRest (c.next h).2.1 = rest at i1 i2 i3 i4
    obtain ⟨res, last, hf⟩ := rest
    simp only at i1 i2 i3 i4
    subst i1
    cases hm : (b.toList.drop (idx c + 1)).mapM (lexemeHanded c.version) with
    | none =>
      refine ⟨fun hs' h' => ?_, fun _ => rfl⟩
      simp at h'
    | some ys =>
      refine ⟨fun hs' h' => ?_, fun h' => ?_⟩
      · have h'' : x :: ys = hs' := by simpa using h'
        subst h''
        exact ⟨rfl, rfl, i2 (by simp [hm]), i3, i4⟩
      · simp at h'

theorem len_toTokenBatch (b : Array Lexeme) (hb0 : Ordered 0 b.toList) :
    (toTokenBatch b hb0).len = b.size := by
  simpa using (batchOf_toTokenBatch b hb0).len

/-- What the batched lexer's hand-over of a cursor over a batch does with the consumer. -/
theorem handOverCursor_batch {floor : Nat} (v : Version) (b : Array Lexeme)
    (hb0 : Ordered 0 b.toList) (ha : (BatchCursor.new v (toTokenBatch b hb0)).EndsAfter floor)
    (coll : Collector) :
    (∀ hs, handedAll v b.toList = some hs →
      ((handOverCursor (H := Collector) (m := Id) (R := Empty) (E := Unit)
          (BatchCursor.new v (toTokenBatch b hb0)) ha).run coll).1.1 = none ∧
      ((handOverCursor (H := Collector) (m := Id) (R := Empty) (E := Unit)
          (BatchCursor.new v (toTokenBatch b hb0)) ha).run coll).1.2.version = v ∧
      ((handOverCursor (H := Collector) (m := Id) (R := Empty) (E := Unit)
          (BatchCursor.new v (toTokenBatch b hb0)) ha).run coll).2.handed =
        coll.handed ++ hs) ∧
    (handedAll v b.toList = none → ∃ f,
      ((handOverCursor (H := Collector) (m := Id) (R := Empty) (E := Unit)
          (BatchCursor.new v (toTokenBatch b hb0)) ha).run coll).1.1 = some (.failed f)) := by
  rw [handOverCursor]
  by_cases h : (BatchCursor.new v (toTokenBatch b hb0)).HasNext
  · have hc := consume_batch b hb0 _ h rfl
      (by rw [idx_new, remaining_new, len_toTokenBatch b hb0]; omega) coll
    simp only [idx_new, List.drop_zero] at hc
    simp only [h, dite_true, StateT.run_bind]
    have hv : (BatchCursor.new v (toTokenBatch b hb0)).version = v := rfl
    have hrl : (BatchCursor.new v (toTokenBatch b hb0)).relexRequested = false := rfl
    rw [hv, hrl] at hc
    generalize (Consume.consume (BatchCursor.new v (toTokenBatch b hb0)) h).run coll = X at hc ⊢
    obtain ⟨⟨answer, next, hnext⟩, coll'⟩ := X
    obtain ⟨hok, herr⟩ := hc
    refine ⟨fun hs hhs => ?_, fun hn => ?_⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hok hs hhs
      simp only at h1 h2 h3 h4 h5
      subst h1
      simp only [id_bind, h5, Bool.false_eq_true, ite_false]
      rw [handOverCursor]
      have hnn : ¬ next.resetConsumed.HasNext := by
        rw [hasNext_iff, BatchCursor.remaining_resetConsumed]; omega
      simp only [hnn, dite_false]
      exact ⟨rfl, h4, h2⟩
    · have h1 := herr hn
      simp only at h1
      subst h1
      exact ⟨_, rfl⟩
  · have h0 : b.size = 0 := by
      rw [hasNext_iff, remaining_new, len_toTokenBatch b hb0] at h; omega
    simp only [h, dite_false]
    have hl : b.toList = [] := by simpa using h0
    rw [hl]
    refine ⟨fun hs hhs => ?_, fun hn => ?_⟩
    · simp only [handedAll, List.mapM_nil] at hhs
      cases hhs
      exact ⟨rfl, rfl, (List.append_nil _).symm⟩
    · simp [handedAll] at hn

/-- What the batched lexer's hand-over of a batch does with the consumer. -/
theorem flush_batch {floor : Nat} (core : Core) (b : Array Lexeme) (hb0 : Ordered 0 b.toList)
    (ha : EndsAfter floor b.toList) (coll : Collector) :
    (∀ hs, handedAll core.version b.toList = some hs →
      (StateT.run (flush (H := Collector) (m := Id) (R := Empty) (E := Unit) core b hb0 ha)
        coll).1.1 = none ∧
      (∃ d, (StateT.run (flush (H := Collector) (m := Id) (R := Empty) (E := Unit) core b hb0 ha)
        coll).1.2 = { core with depth := d }) ∧
      (StateT.run (flush (H := Collector) (m := Id) (R := Empty) (E := Unit) core b hb0 ha)
        coll).2.handed = coll.handed ++ hs) ∧
    (handedAll core.version b.toList = none → ∃ f,
      (StateT.run (flush (H := Collector) (m := Id) (R := Empty) (E := Unit) core b hb0 ha)
        coll).1.1 = some (.failed f)) := by
  have hc := BatchCursor.endsAfter_new (endsAfter_toTokenBatch hb0 ha) core.version
  obtain ⟨hok, herr⟩ := handOverCursor_batch core.version b hb0 hc coll
  simp only [flush, StateT.run_bind]
  generalize (handOverCursor (H := Collector) (m := Id) (R := Empty) (E := Unit)
    (BatchCursor.new core.version (toTokenBatch b hb0)) hc).run coll = X at hok herr ⊢
  obtain ⟨⟨stop, cursor⟩, coll'⟩ := X
  refine ⟨fun hs hhs => ?_, fun hn => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hok hs hhs
    simp only at h1 h2 h3
    subst h1
    simp only [id_bind]
    refine ⟨rfl, ⟨cursor.foldConsumedCategories core.depth depthAfter, ?_⟩, h3⟩
    rw [h2]
    rfl
  · obtain ⟨f, hf⟩ := herr hn
    simp only at hf
    subst hf
    exact ⟨f, rfl⟩

end BSmtLib.Proofs.Lexer.V1NaiveV2Batched

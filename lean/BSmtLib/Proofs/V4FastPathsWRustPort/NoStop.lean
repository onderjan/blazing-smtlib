import BSmtLib.Proofs.V4FastPathsWRustPort.HandOver

/-!
# The adapter's consumer never stops a hand-over

The adapter's consumer `Collector` never asks to relex and has no result to finish with, so a
hand-over of any batch is either done or interrupted by an error (`flushBatch_noStop`), whatever
the batch holds. The loop over a slice relies on it after an error, when it hands over the
batch as it was left.
-/

namespace BSmtLib.Proofs.Lexer.V4FastPathsWRustPort

open BSmtLib.Proofs.Adapter V1NaiveV2Batched

/-- Taking the rest of a cursor keeps its request to relex. -/
theorem takeRest_relex : ∀ (n : Nat) (c : BatchCursor), c.remaining = n →
    (takeRest c).2.1.relexRequested = c.relexRequested := by
  intro n
  induction n with
  | zero =>
    intro c hn
    have hnh : ¬ c.HasNext := by rw [hasNext_iff]; omega
    rw [takeRest]
    simp only [hnh, dite_false]
  | succ n ih =>
    intro c hn
    have hh : c.HasNext := by rw [hasNext_iff]; omega
    have hr := remaining_next c hh
    have i := ih (c.next hh).2.1 (by omega)
    have i2 := relex_next c hh
    rw [takeRest]
    simp only [hh, dite_true]
    generalize c.next hh = r at i i2 ⊢
    obtain ⟨token, next, consumed⟩ := r
    dsimp only at i i2 ⊢
    cases toHanded c token with
    | none => exact i2
    | some handed =>
      dsimp only
      generalize takeRest next = t at i ⊢
      obtain ⟨rest, last, follows⟩ := t
      exact i.trans i2

/-- The adapter's consumer keeps the cursor's request to relex. -/
theorem consume_relex (c : BatchCursor) (h : c.HasNext) (coll : Collector) :
    ((Consume.consume (H := Collector) c h).run coll).1.2.1.relexRequested =
      c.relexRequested := by
  have i := takeRest_relex _ (c.next h).2.1 rfl
  have i2 := relex_next c h
  simp only [Consume.consume]
  generalize c.next h = r at i i2 ⊢
  obtain ⟨token, next, consumed⟩ := r
  dsimp only at i i2 ⊢
  cases toHanded c token with
  | none => exact i2
  | some handed =>
    dsimp only
    generalize takeRest next = t at i ⊢
    obtain ⟨rest, last, follows⟩ := t
    cases rest with
    | none => exact i.trans i2
    | some rest => exact i.trans i2

/-- Takes the steps of the lexer that only read and change the lexer state, and throws an
error, for the postconditions `True`. -/
local macro "wp_walk_true" : tactic =>
  `(tactic| repeat (first
    | (apply wp_throw; exact ⟨_, rfl⟩)
    | apply wp_modifyCore
    | apply wp_getCore
    | apply wp_pure
    | apply wp_bind
    | trivial))

section

variable {floor : Option Nat} {low : Nat}

/-- The hand-over of a cursor that has not asked to relex is done or interrupted by an
error. -/
theorem flushCursor_noStop : ∀ (n : Nat) (cursor : BatchCursor), cursor.remaining < n →
    cursor.relexRequested = false →
    ∀ (hfloor : ∀ p, floor = some p → cursor.EndsAfter p) (s : BS floor low) (coll : Collector),
    WP (Lexer.WRustPort.flushCursor (H := Collector) (m := Id) (R := Empty) (E := Unit) cursor
      hfloor) s coll (fun _ _ _ => True) (fun _ _ _ => True) := by
  intro n
  induction n with
  | zero => intro cursor h; omega
  | succ n ih =>
  intro cursor hn hrel hfloor s coll
  rw [Lexer.WRustPort.flushCursor]
  apply wp_dite
  · intro h
    have hc := consume_relex cursor h coll
    apply wp_bind
    apply wp_callConsumer
    generalize (Consume.consume (H := Collector) cursor h).run coll = X at hc
    obtain ⟨⟨answer, next, hnext⟩, coll'⟩ := X
    simp only at hc
    dsimp only
    apply wp_bind
    apply wp_modifyCore
    cases answer with
    | error e =>
      dsimp only
      apply wp_bind
      apply wp_getCore
      apply wp_ite <;> intro _ <;> wp_walk_true
    | ok flow =>
      cases flow with
      | «break» r => exact r.elim
      | «continue» =>
        dsimp only
        apply wp_ite
        · intro h'
          rw [hc, hrel] at h'
          cases h'
        · intro _
          refine ih _ ?_ (by rw [← hrel, ← hc]; rfl) _ _ _
          rw [BatchCursor.remaining_resetConsumed]
          have := hnext.remaining_lt
          omega
  · intro _
    apply wp_bind
    apply wp_getCore
    apply wp_ite <;> intro _ <;> wp_walk_true

/-- The hand-over of the batch of the lexer state is done or interrupted by an error. -/
theorem flushBatch_noStop (s : BS floor low) (coll : Collector) :
    WP (Lexer.WRustPort.flushBatch (H := Collector) (m := Id) (R := Empty) (E := Unit)) s coll
      (fun _ _ _ => True) (fun _ _ _ => True) := by
  unfold Lexer.WRustPort.flushBatch
  apply wp_bind
  apply wp_modifyGetThe
  dsimp only
  apply wp_ite
  · intro _
    exact wp_pure _ trivial
  · intro _
    apply wp_bind
    apply wp_getCore
    exact flushCursor_noStop _ _ (Nat.lt_succ_self _) rfl _ _ _

end

end BSmtLib.Proofs.Lexer.V4FastPathsWRustPort

import BSmtLib.Proofs.WRustPortX1BatchInCore.Calls
import BSmtLib.Proofs.Adapter

/-!
# The adapter's consumer

The adapter's consumer `Collector` reads the tokens of the cursor from the next one on, up to its
stop, which is below the length of the batch: on cursors that agree it records the same tokens
and returns cursors that agree (`collector_consumesAlike`).
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Lexer.Internal (intoBatch)
open BSmtLib.Proofs.Adapter

variable {g g' : BatchTag}

/-- A token below the length of the batches is recorded alike. -/
theorem toHanded_eq {c : BatchCursor g} {d : BatchCursor g'} (h : CursorAgree c d)
    {t : Token g} {t' : Token g'} (et : tokenIndex t = tokenIndex t')
    (ht : tokenIndex t < (intoBatch c).len) : toHanded c t = toHanded d t' := by
  unfold toHanded BatchCursor.syntax SyntaxToken.fromToken
  rw [h.category et ht, h.span et ht, h.content et ht, h.version]

theorem takeRest_agree : ∀ n (c : BatchCursor g) (d : BatchCursor g'), c.remaining = n →
    CursorAgree c d →
    (takeRest c).1 = (takeRest d).1 ∧ CursorAgree (takeRest c).2.val (takeRest d).2.val := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro c d hn h
  rw [takeRest, takeRest]
  by_cases hc : c.HasNext
  · have hd := h.hasNext_iff.mp hc
    simp only [hc, hd, dite_true]
    obtain ⟨et, hag⟩ := h.takeNext hc hd
    have hlt := tokenIndex_next_lt hc h.bounded
    have hrem : (c.next hc).2.1.remaining < n := hn ▸ (c.next hc).2.2.remaining_lt
    generalize c.next hc = p at et hag hlt hrem
    generalize d.next hd = q at et hag
    obtain ⟨t, next, consumed⟩ := p
    obtain ⟨t', next', consumed'⟩ := q
    dsimp only at et hag hlt hrem
    dsimp only
    rw [toHanded_eq h et hlt]
    cases toHanded d t' with
    | none => exact ⟨rfl, hag⟩
    | some x =>
      obtain ⟨e1, e2⟩ := ih _ hrem next next' rfl hag
      dsimp only
      generalize takeRest next = r at e1 e2
      generalize takeRest next' = r' at e1 e2
      obtain ⟨rest, last, f⟩ := r
      obtain ⟨rest', last', f'⟩ := r'
      dsimp only at e1 e2 ⊢
      subst e1
      exact ⟨rfl, e2⟩
  · have hd : ¬d.HasNext := mt h.hasNext_iff.mpr hc
    simp only [hc, hd, dite_false]
    exact ⟨trivial, h⟩

theorem consume_agree (c : BatchCursor g) (d : BatchCursor g') (hc : c.HasNext) (hd : d.HasNext)
    (h : CursorAgree c d) (s : Collector) :
    ((Consume.consume (H := Collector) c hc).run s).1.1 =
        ((Consume.consume (H := Collector) d hd).run s).1.1 ∧
      CursorAgree ((Consume.consume (H := Collector) c hc).run s).1.2.val
        ((Consume.consume (H := Collector) d hd).run s).1.2.val ∧
      ((Consume.consume (H := Collector) c hc).run s).2 =
        ((Consume.consume (H := Collector) d hd).run s).2 := by
  obtain ⟨et, hag⟩ := h.takeNext hc hd
  have hlt := tokenIndex_next_lt hc h.bounded
  simp only [Consume.consume]
  generalize c.next hc = p at et hag hlt
  generalize d.next hd = q at et hag
  obtain ⟨t, next, consumed⟩ := p
  obtain ⟨t', next', consumed'⟩ := q
  dsimp only at et hag hlt
  dsimp only
  rw [toHanded_eq h et hlt]
  cases toHanded d t' with
  | none => exact ⟨rfl, hag, rfl⟩
  | some x =>
    obtain ⟨e1, e2⟩ := takeRest_agree _ next next' rfl hag
    dsimp only
    generalize takeRest next = r at e1 e2
    generalize takeRest next' = r' at e1 e2
    obtain ⟨rest, last, f⟩ := r
    obtain ⟨rest', last', f'⟩ := r'
    dsimp only at e1 e2 ⊢
    subst e1
    cases rest with
    | none => exact ⟨rfl, e2, rfl⟩
    | some l => exact ⟨rfl, e2, rfl⟩

/-- The adapter's consumer reads the cursors it is handed only below the length of their
batches. -/
theorem collector_consumesAlike : ConsumesAlike Collector Id Empty Unit := by
  intro _ _ c d hc hd h s
  obtain ⟨e1, e2, e3⟩ := consume_agree c d hc hd h s
  refine ⟨⟨(((Consume.consume (H := Collector) c hc).run s).1,
    ((Consume.consume (H := Collector) d hd).run s).1,
    ((Consume.consume (H := Collector) c hc).run s).2), e1, e2⟩, rfl, ?_⟩
  show _ = (_, _)
  rw [e3]
  rfl

end BSmtLib.Proofs.WRustPortX1BatchInCore

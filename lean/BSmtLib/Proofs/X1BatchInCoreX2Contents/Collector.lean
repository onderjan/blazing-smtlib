import BSmtLib.Proofs.X1BatchInCoreX2Contents.Cursor
import BSmtLib.Proofs.Adapter

/-!
# The adapter's consumer does not tell twin cursors apart

The consumer `Adapter.Collector` reads a token's content as its bytes only (`toContent`, and the
lookup of reserved words `Reserved.fromBytes?`), so it records the same tokens from a cursor and
from its twin, and leaves twin cursors (`collector_contentBlind`).
-/

namespace BSmtLib.Proofs.X1BatchInCoreX2Contents

open BSmtLib.Proofs.Adapter

variable {γ γ' : BatchTag}

theorem size_toByteArray (s : ByteSlice) : s.toByteArray.size = s.size := by
  have := s.stop_le_size_byteArray
  have := s.start_le_stop
  simp only [ByteSlice.toByteArray, ByteArray.size_extract, ByteSlice.size]
  omega

theorem getD_eq (s : ByteSlice) (i : Nat) : s.getD i 0 = s.toByteArray[i]! := by
  unfold ByteSlice.getD
  split
  · rename_i hi
    rw [getElem!_pos _ _ (by rw [size_toByteArray]; exact hi)]
    simp only [ByteSlice.toByteArray, ByteArray.getElem_extract]
    rfl
  · rename_i hi
    rw [getElem!_neg _ _ (by rw [size_toByteArray]; exact hi)]
    rfl

/-- The lookup of reserved words reads the bytes of the view only. -/
theorem fromBytes?_congr {s s' : ByteSlice} (h : s.toByteArray = s'.toByteArray) (v : Version) :
    Reserved.fromBytes? s v = Reserved.fromBytes? s' v := by
  have hsize : s.size = s'.size := by rw [← size_toByteArray, h, size_toByteArray]
  have hget : ∀ i, s.get! i = s'.get! i := fun i => by
    show s.getD i 0 = s'.getD i 0
    rw [getD_eq, getD_eq, h]
  have hslot : Reserved.Internal.reservedSlot s = Reserved.Internal.reservedSlot s' := by
    simp only [Reserved.Internal.reservedSlot, hsize, hget]
  have hbeq : ∀ w : ByteSlice, (w == s) = (w == s') := fun w => by
    show (w.toByteArray == s.toByteArray) = (w.toByteArray == s'.toByteArray)
    rw [h]
  unfold Reserved.fromBytes?
  rw [hsize, hslot]
  simp only [hbeq]

/-- A token is recorded from what the cursor reports of it, reading its content as its bytes. -/
theorem toHanded_congr {c : BatchCursor γ} {c' : BatchCursor γ'} {token : Token γ}
    {token' : Token γ'}
    (hcat : c.category token = c'.category token') (hspan : c.span token = c'.span token')
    (hversion : c.version = c'.version)
    (hcontent : (c.content token).toByteArray = (c'.content token').toByteArray) :
    toHanded c token = toHanded c' token' := by
  unfold toHanded toContent
  rw [hcat, hspan, hcontent]
  congr 1
  funext type
  congr 1
  simp only [BatchCursor.syntax, SyntaxToken.fromToken, hcat, hversion]
  cases c'.category token' <;> try rfl
  simp only [fromBytes?_congr hcontent]
  split <;> rfl

/-- The tokens next in twin cursors are recorded alike, and the cursors after them are twins. -/
theorem twin_next {c : BatchCursor γ} {c' : BatchCursor γ'} (t : Twin c c') (h : c.HasNext)
    (h' : c'.HasNext) :
    toHanded c (c.next h).1 = toHanded c' (c'.next h').1 ∧
      Twin (c.next h).2.1 (c'.next h').2.1 := by
  obtain ⟨v, b, tg, f, s, n, r, hb⟩ := c
  obtain ⟨v', ⟨len', bytes', types', cs', ce', so', sl', sc', eo', el', ec', origin', ord'⟩, tg',
    f', s', n', r', hb'⟩ := c'
  obtain ⟨ev, ef, es, en, er, hs, hc⟩ := t
  subst ev ef es en er
  cases hs
  have hn : n' < s' := h
  exact ⟨toHanded_congr rfl rfl rfl (hc n' hn), rfl, rfl, rfl, rfl, rfl, rfl, hc⟩

theorem takeRest_twin : ∀ k (c : BatchCursor γ) (c' : BatchCursor γ'), c.remaining = k → Twin c c' →
    (takeRest c).1 = (takeRest c').1 ∧ Twin (takeRest c).2.val (takeRest c').2.val := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro c c' hk t
  rw [takeRest, takeRest]
  by_cases h : c.HasNext
  · have h' : c'.HasNext := t.hasNext.mpr h
    simp only [h, h', dite_true]
    obtain ⟨e, t'⟩ := twin_next t h h'
    have ih' := ih _ (by rw [← hk]; exact (c.next h).2.2.remaining_lt) _ _ rfl t'
    generalize c.next h = p at e t' ih'
    generalize c'.next h' = p' at e t' ih'
    obtain ⟨token, next, consumed⟩ := p
    obtain ⟨token', next', consumed'⟩ := p'
    dsimp only at e t' ih' ⊢
    rw [← e]
    cases toHanded c token with
    | none => exact ⟨by trivial, t'⟩
    | some x =>
      obtain ⟨e1, e2⟩ := ih'
      generalize takeRest next = q at e1 e2
      generalize takeRest next' = q' at e1 e2
      obtain ⟨rest, last, follows⟩ := q
      obtain ⟨rest', last', follows'⟩ := q'
      dsimp only at e1 e2 ⊢
      rw [e1]
      exact ⟨rfl, e2⟩
  · have h' : ¬c'.HasNext := fun h' => h (t.hasNext.mp h')
    simp only [h, h', dite_false]
    exact ⟨by trivial, t⟩

/-- What the adapter's consumer does with a cursor. -/
def collectorStep (c : BatchCursor γ) (h : c.HasNext) (s : Collector) :
    (Except Unit (ControlFlow Empty) × {d : BatchCursor γ // d.Consumed c}) × Collector :=
  match c.next h with
  | (token, ⟨next, consumed⟩) =>
    match toHanded c token with
    | none => ((.error (), ⟨next, consumed⟩), s)
    | some handed =>
      match takeRest next with
      | (none, ⟨last, follows⟩) => ((.error (), ⟨last, follows.trans_consumed consumed⟩), s)
      | (some rest, ⟨last, follows⟩) =>
        ((.ok .continue, ⟨last, follows.trans_consumed consumed⟩),
          { handed := s.handed ++ handed :: rest })

theorem collector_run (c : BatchCursor γ) (h : c.HasNext) (s : Collector) :
    (Consume.consume c h).run s = collectorStep c h s := by
  dsimp only [Consume.consume]
  unfold collectorStep
  obtain ⟨token, next, consumed⟩ := c.next h
  dsimp only
  cases toHanded c token with
  | none => rfl
  | some handed =>
    dsimp only
    obtain ⟨rest, last, follows⟩ := takeRest next
    cases rest <;> rfl

/-- The result of the consumer's step and the cursor it leaves do not depend on its state. -/
theorem collectorStep_state (c : BatchCursor γ) (h : c.HasNext) (s s' : Collector) :
    (collectorStep c h s).1 = (collectorStep c h s').1 := by
  unfold collectorStep
  obtain ⟨token, next, consumed⟩ := c.next h
  dsimp only
  cases toHanded c token with
  | none => rfl
  | some handed =>
    dsimp only
    obtain ⟨rest, last, follows⟩ := takeRest next
    cases rest <;> rfl

/-- The consumer's steps on twin cursors give the same result and state, and leave twin
cursors. -/
theorem collectorStep_twin {c : BatchCursor γ} {c' : BatchCursor γ'} (t : Twin c c') (h : c.HasNext)
    (h' : c'.HasNext) (s : Collector) :
    (collectorStep c h s).1.1 = (collectorStep c' h' s).1.1 ∧
      (collectorStep c h s).2 = (collectorStep c' h' s).2 ∧
      Twin (collectorStep c h s).1.2.val (collectorStep c' h' s).1.2.val := by
  obtain ⟨e, t'⟩ := twin_next t h h'
  have ih := takeRest_twin _ _ _ rfl t'
  unfold collectorStep
  generalize c.next h = p at e t' ih
  generalize c'.next h' = p' at e t' ih
  obtain ⟨token, next, consumed⟩ := p
  obtain ⟨token', next', consumed'⟩ := p'
  dsimp only at e t' ih ⊢
  rw [← e]
  cases toHanded c token with
  | none => exact ⟨rfl, rfl, t'⟩
  | some x =>
    obtain ⟨e1, e2⟩ := ih
    dsimp only
    generalize takeRest next = q at e1 e2
    generalize takeRest next' = q' at e1 e2
    obtain ⟨rest, last, follows⟩ := q
    obtain ⟨rest', last', follows'⟩ := q'
    dsimp only at e1 e2 ⊢
    rw [← e1]
    cases rest <;> exact ⟨rfl, rfl, e2⟩

/-- The adapter's consumer does not tell twin cursors apart. -/
theorem collector_contentBlind : ContentBlind Collector Id Empty Unit := by
  intro _ _ c c' h h' t
  refine ⟨fun x => (x.1, (collectorStep c' h' ⟨[]⟩).1.2), fun s => ?_⟩
  obtain ⟨e1, e2, e3⟩ := collectorStep_twin t h h' s
  have e4 := collectorStep_state c' h' ⟨[]⟩ s
  rw [collector_run, collector_run]
  refine ⟨?_, pure ⟨collectorStep c h s, ?_, ?_⟩, rfl⟩
  · show (((collectorStep c h s).1.1, (collectorStep c' h' ⟨[]⟩).1.2),
      (collectorStep c h s).2) = _
    rw [e4, e1, e2]
  · rfl
  · show Twin _ (collectorStep c' h' ⟨[]⟩).1.2.val
    rw [e4]
    exact e3

end BSmtLib.Proofs.X1BatchInCoreX2Contents

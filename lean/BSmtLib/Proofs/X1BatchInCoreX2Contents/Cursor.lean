import BSmtLib.Proofs.X1BatchInCoreX2Contents.Content

/-!
# Cursors that differ in the array of contents

The two lexers hand a token whose content is in the content buffer over in a batch whose array
of contents is the content: the buffer's whole array in the lexer with the content buffer,
the bytes of the token alone in the lexer with the batch kept in the lexer's state. The cursors
they hand over are then twins (`Twin`): the same but for the batch's array of contents, in which
each token the cursor can yield has the same content. Every other cursor they hand over is the
same in both.

A consumer can tell twin cursors apart, through the array of contents of the batch or of the
view of a token's content. The lexers lex alike for a consumer that does not: one that, handed a
cursor or its twin, does the same and leaves twin cursors (`ContentBlind`).
-/

namespace BSmtLib.Proofs.X1BatchInCoreX2Contents

/-- The batch `b'` is `b` with another array of contents, in which each of the first `n` tokens
has the same content. -/
def SameTokens (b b' : TokenBatch) (n : Nat) : Prop :=
  { b with bytes := b'.bytes } = b' ∧
    ∀ i < n, (b.bytes.toByteSlice b.contentStarts[i]! b.contentStops[i]!).toByteArray =
      (b'.bytes.toByteSlice b.contentStarts[i]! b.contentStops[i]!).toByteArray

theorem sameTokens_refl (b : TokenBatch) (n : Nat) : SameTokens b b n :=
  ⟨rfl, fun _ _ => rfl⟩

/-- The cursor `c'` is `c` over a batch with another array of contents, in which each token that
`c` can yield has the same content. -/
def Twin (c c' : BatchCursor) : Prop :=
  BatchCursor.casesOn (motive := fun _ => Prop) c fun v b f s n r _ =>
    BatchCursor.casesOn (motive := fun _ => Prop) c' fun v' b' f' s' n' r' _ =>
      v' = v ∧ f' = f ∧ s' = s ∧ n' = n ∧ r' = r ∧ SameTokens b b' s

/--
The consumer does not tell twin cursors apart: handed a cursor and its twin, it gives the same
result and changes its state alike, and the cursors it leaves are twins.
-/
def ContentBlind (H : Type) (m : Type → Type) (R E : Type) [Monad m] [Consume H m R E] : Prop :=
  ∀ (c c' : BatchCursor) (h : c.HasNext) (h' : c'.HasNext), Twin c c' →
    ∃ f : Except E (ControlFlow R) × {d : BatchCursor // d.Consumed c} →
        Except E (ControlFlow R) × {d : BatchCursor // d.Consumed c'},
      ∀ s : H,
        (fun y => (f y.1, y.2)) <$> (Consume.consume c h).run s = (Consume.consume c' h').run s ∧
        ∃ y : m {z : (Except E (ControlFlow R) × {d : BatchCursor // d.Consumed c}) × H //
            (f z.1).1 = z.1.1 ∧ Twin z.1.2.val (f z.1).2.val},
          (Consume.consume c h).run s = Subtype.val <$> y

theorem twin_refl (c : BatchCursor) : Twin c c := by
  obtain ⟨v, b, f, s, n, r, hb⟩ := c
  exact ⟨rfl, rfl, rfl, rfl, rfl, sameTokens_refl b s⟩

theorem twin_new (v : Version) {b b' : TokenBatch} (h : SameTokens b b' b.len) :
    Twin (BatchCursor.new v b) (BatchCursor.new v b') := by
  have hl : b'.len = b.len := by rw [← h.1]
  exact ⟨rfl, rfl, hl, rfl, rfl, h⟩

section

variable {c c' : BatchCursor} (t : Twin c c')
include t

theorem Twin.resetConsumed : Twin c.resetConsumed c'.resetConsumed := by
  obtain ⟨v, b, f, s, n, r, hb⟩ := c
  obtain ⟨v', b', f', s', n', r', hb'⟩ := c'
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hs⟩ := t
  exact ⟨rfl, rfl, rfl, rfl, rfl, hs⟩

theorem Twin.version : c'.version = c.version := by
  obtain ⟨v, b, f, s, n, r, hb⟩ := c
  obtain ⟨v', b', f', s', n', r', hb'⟩ := c'
  exact t.1

theorem Twin.relexRequested : c'.relexRequested = c.relexRequested := by
  obtain ⟨v, b, f, s, n, r, hb⟩ := c
  obtain ⟨v', b', f', s', n', r', hb'⟩ := c'
  exact t.2.2.2.2.1

theorem Twin.hasNext : c'.HasNext ↔ c.HasNext := by
  obtain ⟨v, b, f, s, n, r, hb⟩ := c
  obtain ⟨v', b', f', s', n', r', hb'⟩ := c'
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hs⟩ := t
  exact Iff.rfl

theorem Twin.remaining : c'.remaining = c.remaining := by
  obtain ⟨v, b, f, s, n, r, hb⟩ := c
  obtain ⟨v', b', f', s', n', r', hb'⟩ := c'
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hs⟩ := t
  rfl

theorem Twin.intoBatch (x : ByteArray) :
    { c'.intoBatch with bytes := x } = { c.intoBatch with bytes := x } := by
  obtain ⟨v, b, f, s, n, r, hb⟩ := c
  obtain ⟨v', b', f', s', n', r', hb'⟩ := c'
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hs, -⟩ := t
  rw [← hs]
  rfl

theorem Twin.foldConsumedCategories {β : Type} (init : β) (g : β → TokenCategory → β) :
    c'.foldConsumedCategories init g = c.foldConsumedCategories init g := by
  obtain ⟨v, b, f, s, n, r, hb⟩ := c
  obtain ⟨v', b', f', s', n', r', hb'⟩ := c'
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hs, -⟩ := t
  rw [← hs]
  rfl

theorem Twin.consumedEndOf {o o' : BatchCursor} (h : c.Consumed o) (h' : c'.Consumed o') :
    c'.consumedEndOf h' = c.consumedEndOf h := by
  obtain ⟨v, b, f, s, n, r, hb⟩ := c
  obtain ⟨v', b', f', s', n', r', hb'⟩ := c'
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hs, -⟩ := t
  unfold BatchCursor.consumedEndOf
  rw [← hs]
  rfl

end

/-! ## The batch of a token handed over alone -/

theorem len_pushLocated (b : TokenBatch) (ty : TokenCategory) (cs ce : Nat) (s e : Location)
    (after nonempty) : (b.pushLocated ty cs ce s e after nonempty).len = b.len + 1 := rfl

theorem bytes_pushLocated (b : TokenBatch) (ty : TokenCategory) (cs ce : Nat) (s e : Location)
    (after nonempty) : (b.pushLocated ty cs ce s e after nonempty).bytes = b.bytes := rfl

theorem contentStarts_pushLocated (b : TokenBatch) (ty : TokenCategory) (cs ce : Nat)
    (s e : Location) (after nonempty) (hb : b.len ≤ b.contentStarts.size) :
    (b.pushLocated ty cs ce s e after nonempty).contentStarts[b.len]! = cs := by
  show (if b.len < b.contentStarts.size then b.contentStarts.set! b.len cs
    else b.contentStarts.push cs)[b.len]! = cs
  split
  · rename_i h
    rw [getElem!_pos _ _
      (by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact h)]
    simp
  · rename_i h
    rw [getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
    simp [show b.len = b.contentStarts.size by omega]

theorem contentStops_pushLocated (b : TokenBatch) (ty : TokenCategory) (cs ce : Nat)
    (s e : Location) (after nonempty) (hb : b.len ≤ b.contentStops.size) :
    (b.pushLocated ty cs ce s e after nonempty).contentStops[b.len]! = ce := by
  show (if b.len < b.contentStops.size then b.contentStops.set! b.len ce
    else b.contentStops.push ce)[b.len]! = ce
  split
  · rename_i h
    rw [getElem!_pos _ _
      (by simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact h)]
    simp
  · rename_i h
    rw [getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
    simp [show b.len = b.contentStops.size by omega]

/-- The batch of a token handed over alone with its content in the buffer, and the batch of the
token with its content as a byte array: the second is the first with the content's bytes as
its array of contents, which give the token the same content. -/
theorem sameTokens_stored {buf : Lexer.ContentBuffer} (hfits : Fits buf) (batch : TokenBatch)
    (origin : Nat) (ty : TokenCategory) (s e : Location) (after nonempty after' nonempty') :
    SameTokens
      (({ batch.clear origin with bytes := buf.bytes } : TokenBatch).pushLocated ty 0 buf.len s e
        after nonempty)
      (({ batch.clear origin with bytes := contentBytes buf } : TokenBatch).pushLocated ty 0
        (contentBytes buf).size s e after' nonempty')
      (({ batch.clear origin with bytes := buf.bytes } : TokenBatch).pushLocated ty 0 buf.len s e
        after nonempty).len := by
  have hsize := size_contentBytes hfits
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [hsize]
    rfl
  · rw [len_pushLocated] at hi
    have hi0 : i = 0 := by simp [TokenBatch.clear] at hi; omega
    subst hi0
    have h0 : ({ batch.clear origin with bytes := buf.bytes } : TokenBatch).len = 0 := rfl
    have es := contentStarts_pushLocated
      ({ batch.clear origin with bytes := buf.bytes } : TokenBatch) ty 0 buf.len s e after
      nonempty (Nat.zero_le _)
    have ee := contentStops_pushLocated
      ({ batch.clear origin with bytes := buf.bytes } : TokenBatch) ty 0 buf.len s e after
      nonempty (Nat.zero_le _)
    rw [h0] at es ee
    rw [es, ee, bytes_pushLocated, bytes_pushLocated]
    unfold Fits at hfits
    have hl : buf.len ≤ (contentBytes buf).size := by omega
    show (buf.bytes.toByteSlice 0 buf.len).toByteArray =
      ((contentBytes buf).toByteSlice 0 buf.len).toByteArray
    simp only [ByteArray.toByteSlice, hfits, hl, dite_true, Nat.zero_le, ByteSlice.toByteArray,
      ByteSlice.byteArray, ByteSlice.start, ByteSlice.size, ByteSlice.stop, Nat.zero_add,
      Nat.sub_zero]
    unfold contentBytes at hsize ⊢
    rw [ByteArray.extract_extract, Nat.zero_add, Nat.zero_add, Nat.min_self]

end BSmtLib.Proofs.X1BatchInCoreX2Contents

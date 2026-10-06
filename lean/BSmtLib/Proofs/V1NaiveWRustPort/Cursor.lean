import BSmtLib.Proofs.V1Naive

/-!
# Cursors, contents, and what the consumer records

A cursor is observed through its public operations only: `idx` is the index of its next token,
counted by `BatchCursor.foldConsumedCategories`, and a step of the cursor reads the batch at that
index. The lookup of reserved words reads only the bytes of a content (`fromBytes_toByteArray`).
`pending` is what the adapter's consumer has recorded together with what it will record of
lexemes not yet handed over.
-/

namespace BSmtLib.Proofs.Lexer.V1NaiveWRustPort

open BSmtLib.Lexer.Internal (intoBatch)
open BSmtLib.Proofs.Adapter V1Naive BSmtLib.Proofs.Simulation

variable {g : BatchTag}

/-! ## Cursors -/

/-- The index of the next token of the cursor in its batch. -/
def idx (c : BatchCursor g) : Nat := c.foldConsumedCategories 0 (fun n _ => n + 1)

theorem fold_count (n : Nat) : (List.range n).foldl (fun acc (_ : Nat) => acc + 1) 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem idx_new (v : Version) (b : TokenBatch) : idx (BatchCursor.new v b) = 0 := rfl

theorem remaining_new (v : Version) (b : TokenBatch) :
    (BatchCursor.new v b).remaining = b.len := by
  simp only [BatchCursor.remaining, BatchCursor.new, Nat.sub_zero]

theorem idx_next (c : BatchCursor g) (h : c.HasNext) : idx (c.next h).2.1 = idx c + 1 := by
  simp only [idx, BatchCursor.foldConsumedCategories, BatchCursor.next, fold_count]

theorem remaining_next (c : BatchCursor g) (h : c.HasNext) :
    (c.next h).2.1.remaining + 1 = c.remaining := by
  have := h
  simp only [BatchCursor.HasNext] at this
  simp only [BatchCursor.remaining, BatchCursor.next]
  omega

theorem hasNext_iff (c : BatchCursor g) : c.HasNext ↔ 0 < c.remaining := by
  simp only [BatchCursor.HasNext, BatchCursor.remaining]
  omega

theorem intoBatch_next (c : BatchCursor g) (h : c.HasNext) :
    intoBatch (c.next h).2.1 = intoBatch c := rfl

theorem version_next (c : BatchCursor g) (h : c.HasNext) :
    (c.next h).2.1.version = c.version := rfl

theorem relex_next (c : BatchCursor g) (h : c.HasNext) :
    (c.next h).2.1.relexRequested = c.relexRequested := rfl

theorem category_next (c : BatchCursor g) (h : c.HasNext) :
    c.category (c.next h).1 = TokenCategory.ofUInt8 ((intoBatch c).types.get! (idx c)) := by
  simp only [idx, BatchCursor.foldConsumedCategories, fold_count]
  rfl

theorem content_next (c : BatchCursor g) (h : c.HasNext) :
    c.content (c.next h).1 = (intoBatch c).bytes.toByteSlice ((intoBatch c).contentStarts[idx c]!)
      ((intoBatch c).contentStops[idx c]!) := by
  simp only [idx, BatchCursor.foldConsumedCategories, fold_count]
  rfl

theorem span_next (c : BatchCursor g) (h : c.HasNext) :
    c.span (c.next h).1 = Span.ofNumbers ((intoBatch c).startOffsets[idx c]!)
      ((intoBatch c).startLines[idx c]!) ((intoBatch c).startColumns[idx c]!)
      ((intoBatch c).endOffsets[idx c]!) ((intoBatch c).endLines[idx c]!)
      ((intoBatch c).endColumns[idx c]!) := by
  simp only [idx, BatchCursor.foldConsumedCategories, fold_count]
  rfl

/-! ## Contents -/

theorem ofUInt8_toUInt8 (c : TokenCategory) : TokenCategory.ofUInt8 c.toUInt8 = c := by
  cases c <;> rfl

theorem reservedSlot_toByteArray (s : ByteSlice) :
    Reserved.Internal.reservedSlot s.toByteArray.toByteSlice =
      Reserved.Internal.reservedSlot s := by
  unfold Reserved.Internal.reservedSlot
  simp only [size_toByteArray_toByteSlice, get!_toByteArray]

/-- The lookup of reserved words reads only the bytes of the slice. -/
theorem fromBytes_toByteArray (s : ByteSlice) (v : Version) :
    Reserved.fromBytes? s.toByteArray.toByteSlice v = Reserved.fromBytes? s v := by
  unfold Reserved.fromBytes?
  rw [reservedSlot_toByteArray, size_toByteArray_toByteSlice]
  simp only [beq_toByteArray]

/-! ## What the consumer records -/

/-- What the consumer has recorded and will record of the lexemes, or none if it fails on one
of them. -/
def pending (v : Version) (coll : Collector) (ls : List Lexeme) : Option (List Spec.Lexer.Handed) :=
  (handedAll v ls).map (coll.handed ++ ·)

theorem pending_none_append {v : Version} {coll : Collector} {xs : List Lexeme}
    (h : pending v coll xs = none) (ys : List Lexeme) : pending v coll (xs ++ ys) = none := by
  simp only [pending, Option.map_eq_none_iff] at h ⊢
  rw [handedAll_append, h]
  rfl

theorem pending_congr_append {v : Version} {c₁ c₂ : Collector} {xs ys : List Lexeme}
    (h : pending v c₁ xs = pending v c₂ ys) (zs : List Lexeme) :
    pending v c₁ (xs ++ zs) = pending v c₂ (ys ++ zs) := by
  simp only [pending] at h ⊢
  rw [handedAll_append, handedAll_append]
  cases h1 : handedAll v xs with
  | none =>
    cases h2 : handedAll v ys with
    | none => rfl
    | some y => rw [h1, h2] at h; simp at h
  | some x =>
    cases h2 : handedAll v ys with
    | none => rw [h1, h2] at h; simp at h
    | some y =>
      rw [h1, h2] at h
      simp only [Option.map_some, Option.some.injEq] at h
      cases handedAll v zs with
      | none => rfl
      | some z =>
        simp only [Option.bind_some, Option.map_some, Option.some.injEq]
        rw [← List.append_assoc, h, List.append_assoc]

theorem collector_ws : Consume.consumesWhitespaceAndComments (H := Collector) = false := rfl

end BSmtLib.Proofs.Lexer.V1NaiveWRustPort

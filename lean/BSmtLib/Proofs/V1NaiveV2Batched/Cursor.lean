import BSmtLib.Proofs.V1Naive
import BSmtLib.Proofs.Lexer.V2Batched

/-!
# Batches and cursors

What the batched lexer's batch of lexemes (`V2Batched.toTokenBatch`) holds, and what a cursor
over it reports: each token of the batch is reported as the naive lexer reports the lexeme
alone (`toHanded_batch`). The cursor is observed through its public operations only: `idx` is
the index of its next token, counted by `BatchCursor.foldConsumedCategories`.
-/

namespace BSmtLib.Proofs.Lexer.V1NaiveV2Batched

open BSmtLib.Proofs.Adapter V1Naive V2Batched

/-! ## Cursors -/

/-- The index of the next token of the cursor in its batch. -/
def idx (c : BatchCursor) : Nat := c.foldConsumedCategories 0 (fun n _ => n + 1)

theorem fold_count (n : Nat) : (List.range n).foldl (fun acc (_ : Nat) => acc + 1) 0 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.foldl_append, ih]; rfl

theorem idx_new (v : Version) (b : TokenBatch) : idx (BatchCursor.new v b) = 0 := rfl

theorem remaining_new (v : Version) (b : TokenBatch) :
    (BatchCursor.new v b).remaining = b.len := by
  simp only [BatchCursor.remaining, BatchCursor.new, Nat.sub_zero]

theorem idx_next (c : BatchCursor) (h : c.HasNext) : idx (c.next h).2.1 = idx c + 1 := by
  simp only [idx, BatchCursor.foldConsumedCategories, BatchCursor.next, fold_count]

theorem remaining_next (c : BatchCursor) (h : c.HasNext) :
    (c.next h).2.1.remaining + 1 = c.remaining := by
  have := h
  simp only [BatchCursor.HasNext] at this
  simp only [BatchCursor.remaining, BatchCursor.next]
  omega

theorem hasNext_iff (c : BatchCursor) : c.HasNext ↔ 0 < c.remaining := by
  simp only [BatchCursor.HasNext, BatchCursor.remaining]
  omega

theorem intoBatch_next (c : BatchCursor) (h : c.HasNext) :
    (c.next h).2.1.intoBatch = c.intoBatch := rfl

theorem version_next (c : BatchCursor) (h : c.HasNext) :
    (c.next h).2.1.version = c.version := rfl

theorem relex_next (c : BatchCursor) (h : c.HasNext) :
    (c.next h).2.1.relexRequested = c.relexRequested := rfl

theorem category_next (c : BatchCursor) (h : c.HasNext) :
    c.category (c.next h).1 = TokenCategory.ofUInt8 (c.intoBatch.types.get! (idx c)) := by
  simp only [idx, BatchCursor.foldConsumedCategories, fold_count]
  rfl

theorem content_next (c : BatchCursor) (h : c.HasNext) :
    c.content (c.next h).1 = c.intoBatch.bytes.toByteSlice (c.intoBatch.contentStarts[idx c]!)
      (c.intoBatch.contentStops[idx c]!) := by
  simp only [idx, BatchCursor.foldConsumedCategories, fold_count]
  rfl

theorem span_next (c : BatchCursor) (h : c.HasNext) :
    c.span (c.next h).1 = Span.ofNumbers (c.intoBatch.startOffsets[idx c]!)
      (c.intoBatch.startLines[idx c]!) (c.intoBatch.startColumns[idx c]!)
      (c.intoBatch.endOffsets[idx c]!) (c.intoBatch.endLines[idx c]!)
      (c.intoBatch.endColumns[idx c]!) := by
  simp only [idx, BatchCursor.foldConsumedCategories, fold_count]
  rfl

/-! ## Batches -/

/-- The batch holds the lexemes: their categories, contents and spans, in order. -/
structure BatchOf (T : TokenBatch) (ls : List Lexeme) : Prop where
  len : T.len = ls.length
  types : T.types.size = ls.length
  contentStarts : T.contentStarts.size = ls.length
  contentStops : T.contentStops.size = ls.length
  startOffsets : T.startOffsets.size = ls.length
  startLines : T.startLines.size = ls.length
  startColumns : T.startColumns.size = ls.length
  endOffsets : T.endOffsets.size = ls.length
  endLines : T.endLines.size = ls.length
  endColumns : T.endColumns.size = ls.length
  entry : ∀ j (hj : j < ls.length),
    T.types.get! j = ls[j].category.toUInt8 ∧
    T.contentStarts[j]! ≤ T.contentStops[j]! ∧ T.contentStops[j]! ≤ T.bytes.size ∧
    T.bytes.extract (T.contentStarts[j]!) (T.contentStops[j]!) = ls[j].content ∧
    T.startOffsets[j]! = ls[j].start.offset ∧ T.startLines[j]! = ls[j].start.line ∧
    T.startColumns[j]! = ls[j].start.column ∧ T.endOffsets[j]! = ls[j].end.offset ∧
    T.endLines[j]! = ls[j].end.line ∧ T.endColumns[j]! = ls[j].end.column

theorem batchOf_empty (n : Nat) : BatchOf (TokenBatch.empty n) [] := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | rfl | (intro j hj; simp at hj)

theorem getElem!_push_lt (a : Array Nat) (v j : Nat) (h : j < a.size) :
    (a.push v)[j]! = a[j]! := by
  rw [getElem!_pos (a.push v) j (by simp; omega), getElem!_pos a j h, Array.getElem_push]
  simp [h]

theorem getElem!_push_eq (a : Array Nat) (v : Nat) : (a.push v)[a.size]! = v := by
  rw [getElem!_pos (a.push v) a.size (by simp)]
  simp

theorem get!_push_lt (a : ByteArray) (v : UInt8) (j : Nat) (h : j < a.size) :
    (a.push v).get! j = a.get! j := by
  simp only [ByteArray.get!, ByteArray.push]
  rw [getElem!_pos _ j (by simp; exact Nat.lt_succ_of_lt h), getElem!_pos _ j h,
    Array.getElem_push]
  have h' : j < a.data.size := h
  simp only [h', dite_true]

theorem get!_push_eq (a : ByteArray) (v : UInt8) : (a.push v).get! a.size = v := by
  simp only [ByteArray.get!, ByteArray.push]
  rw [getElem!_pos _ a.size (by simp only [Array.size_push]; exact Nat.lt_succ_self _),
    Array.getElem_push]
  have h' : ¬ (a.size < a.data.size) := Nat.lt_irrefl _
  simp only [h', dite_false]

theorem extract_append_left (a b : ByteArray) (i j : Nat) (h : j ≤ a.size) :
    (a ++ b).extract i j = a.extract i j := by
  apply ByteArray.ext
  simp only [ByteArray.data_extract, ByteArray.data_append, Array.extract_append]
  have hs : a.size = a.data.size := rfl
  have : j - a.data.size = 0 := by omega
  rw [this, Array.extract_zero, Array.append_empty]

theorem extract_append_right (a b : ByteArray) :
    (a ++ b).extract a.size (a.size + b.size) = b := by
  apply ByteArray.ext
  have ha : a.size = a.data.size := rfl
  have hb : b.size = b.data.size := rfl
  simp only [ByteArray.data_extract, ByteArray.data_append, Array.extract_append, ha, hb,
    Nat.sub_self, Nat.add_sub_cancel_left, Array.extract_size, Array.extract_size_left]
  rw [Array.empty_append]

/-- The step of `V2Batched.pushLexemes`. -/
def pushLexeme (batch : TokenBatch) (l : Lexeme)
    (after : ({ batch with bytes := batch.bytes ++ l.content } : TokenBatch).lastEnd ≤
      l.start.offset)
    (hv : l.Valid) : TokenBatch :=
  let start := batch.bytes.size
  ({ batch with bytes := batch.bytes ++ l.content } : TokenBatch).pushLocated l.category start
    (start + l.content.size) l.start l.end after hv

theorem batchOf_push {T : TokenBatch} {ls : List Lexeme} (h : BatchOf T ls) (l : Lexeme)
    (after : ({ T with bytes := T.bytes ++ l.content } : TokenBatch).lastEnd ≤ l.start.offset)
    (hv : l.Valid) : BatchOf (pushLexeme T l after hv) (ls ++ [l]) := by
  obtain ⟨hlen, ht, hcs, hce, hso, hsl, hsc, heo, hel, hec, hentry⟩ := h
  generalize hP : pushLexeme T l after hv = P
  have e : (P.len, P.bytes, P.types, P.contentStarts, P.contentStops, P.startOffsets,
      P.startLines, P.startColumns, P.endOffsets, P.endLines, P.endColumns) =
      (T.len + 1, T.bytes ++ l.content, T.types.push l.category.toUInt8,
        T.contentStarts.push T.bytes.size, T.contentStops.push (T.bytes.size + l.content.size),
        T.startOffsets.push l.start.offset, T.startLines.push l.start.line,
        T.startColumns.push l.start.column, T.endOffsets.push l.end.offset,
        T.endLines.push l.end.line, T.endColumns.push l.end.column) := by
    subst hP
    show (T.len + 1, T.bytes ++ l.content,
        (if T.len < T.types.size then T.types.set! T.len l.category.toUInt8
          else T.types.push l.category.toUInt8),
        (if T.len < T.contentStarts.size then T.contentStarts.set! T.len T.bytes.size
          else T.contentStarts.push T.bytes.size),
        (if T.len < T.contentStops.size then
          T.contentStops.set! T.len (T.bytes.size + l.content.size)
          else T.contentStops.push (T.bytes.size + l.content.size)),
        (if T.len < T.startOffsets.size then T.startOffsets.set! T.len l.start.offset
          else T.startOffsets.push l.start.offset),
        (if T.len < T.startLines.size then T.startLines.set! T.len l.start.line
          else T.startLines.push l.start.line),
        (if T.len < T.startColumns.size then T.startColumns.set! T.len l.start.column
          else T.startColumns.push l.start.column),
        (if T.len < T.endOffsets.size then T.endOffsets.set! T.len l.end.offset
          else T.endOffsets.push l.end.offset),
        (if T.len < T.endLines.size then T.endLines.set! T.len l.end.line
          else T.endLines.push l.end.line),
        (if T.len < T.endColumns.size then T.endColumns.set! T.len l.end.column
          else T.endColumns.push l.end.column)) = _
    simp [hlen, ht, hcs, hce, hso, hsl, hsc, heo, hel, hec]
  simp only [Prod.mk.injEq] at e
  obtain ⟨e0, eb, et, ecs, ece, eso, esl, esc, eeo, eel, eec⟩ := e
  have hbs : T.bytes.size + l.content.size = (T.bytes ++ l.content).size := by
    simp [ByteArray.size_append]
  refine ⟨by simp [e0, hlen], by simp [et, ht], by simp [ecs, hcs], by simp [ece, hce],
    by simp [eso, hso], by simp [esl, hsl], by simp [esc, hsc], by simp [eeo, heo],
    by simp [eel, hel], by simp [eec, hec], ?_⟩
  intro j hj
  rw [eb, et, ecs, ece, eso, esl, esc, eeo, eel, eec]
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < ls.length
  · obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hentry j hlt
    rw [List.getElem_append_left hlt]
    rw [get!_push_lt _ _ _ (by omega), getElem!_push_lt _ _ _ (by omega),
      getElem!_push_lt _ _ _ (by omega), getElem!_push_lt _ _ _ (by omega),
      getElem!_push_lt _ _ _ (by omega), getElem!_push_lt _ _ _ (by omega),
      getElem!_push_lt _ _ _ (by omega), getElem!_push_lt _ _ _ (by omega),
      getElem!_push_lt _ _ _ (by omega), extract_append_left _ _ _ _ e3]
    refine ⟨e1, e2, ?_, e4, e5, e6, e7, e8, e9, e10⟩
    rw [← hbs]; omega
  · have hj' : j = ls.length := by omega
    subst hj'
    rw [List.getElem_concat_length rfl]
    have et := get!_push_eq T.types l.category.toUInt8
    have e1 := getElem!_push_eq T.contentStarts T.bytes.size
    have e2 := getElem!_push_eq T.contentStops (T.bytes.size + l.content.size)
    have e3 := getElem!_push_eq T.startOffsets l.start.offset
    have e4 := getElem!_push_eq T.startLines l.start.line
    have e5 := getElem!_push_eq T.startColumns l.start.column
    have e6 := getElem!_push_eq T.endOffsets l.end.offset
    have e7 := getElem!_push_eq T.endLines l.end.line
    have e8 := getElem!_push_eq T.endColumns l.end.column
    rw [ht] at et
    rw [hcs] at e1
    rw [hce] at e2
    rw [hso] at e3
    rw [hsl] at e4
    rw [hsc] at e5
    rw [heo] at e6
    rw [hel] at e7
    rw [hec] at e8
    rw [et, e1, e2, e3, e4, e5, e6, e7, e8, extract_append_right]
    exact ⟨rfl, by omega, Nat.le_of_eq hbs, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem batchOf_pushLexemes (ls : List Lexeme) :
    ∀ (T : TokenBatch) (h : Ordered T.lastEnd ls) (done : List Lexeme), BatchOf T done →
      BatchOf (pushLexemes T ls h) (done ++ ls) := by
  induction ls with
  | nil => intro T h done hT; rw [List.append_nil]; exact hT
  | cons l ls ih =>
    intro T h done hT
    obtain ⟨hstart, hv, hrest⟩ := h
    have := ih _ ((TokenBatch.lastEnd_pushLocated ..).symm ▸ hrest) (done ++ [l])
      (batchOf_push hT l hstart hv)
    rw [show done ++ l :: ls = done ++ [l] ++ ls by simp]
    exact this

theorem batchOf_toTokenBatch (b : Array Lexeme) (h : Ordered 0 b.toList) :
    BatchOf (toTokenBatch b h) b.toList := by
  have := batchOf_pushLexemes b.toList (TokenBatch.empty b.size) h [] (batchOf_empty _)
  exact this

/-! ## Tokens of a batch -/

theorem ofUInt8_toUInt8 (c : TokenCategory) : TokenCategory.ofUInt8 c.toUInt8 = c := by
  cases c <;> rfl

theorem toByteArray_toByteSlice_range (a : ByteArray) {i j : Nat} (hij : i ≤ j) (hj : j ≤ a.size) :
    (a.toByteSlice i j).toByteArray = a.extract i j := by
  simp only [ByteArray.toByteSlice, hj, hij, dite_true, ByteSlice.toByteArray, ByteSlice.byteArray,
    ByteSlice.start, ByteSlice.size, ByteSlice.stop]
  congr 1
  omega

theorem size_toByteArray (s : ByteSlice) : s.toByteArray.size = s.size := by
  have h1 := s.stop_le_size_byteArray
  have h2 := s.start_le_stop
  simp only [ByteSlice.toByteArray, ByteArray.size_extract, ByteSlice.size]
  omega

theorem size_toByteSlice_full (a : ByteArray) : a.toByteSlice.size = a.size := by
  simp [ByteArray.toByteSlice, ByteSlice.size, ByteSlice.start, ByteSlice.stop]

theorem getElem_slice (s : ByteSlice) (i : Nat) (h : i < s.size) :
    s[i] = s.byteArray[s.start + i]'(by
      have := s.stop_le_size_byteArray; simp only [ByteSlice.size] at h; omega) := rfl

theorem size_toByteArray_toByteSlice (s : ByteSlice) :
    s.toByteArray.toByteSlice.size = s.size := by
  rw [size_toByteSlice_full, size_toByteArray]

theorem get!_toByteArray (s : ByteSlice) (i : Nat) :
    s.toByteArray.toByteSlice.get! i = s.get! i := by
  have hs := size_toByteArray_toByteSlice s
  simp only [ByteSlice.get!, ByteSlice.getD]
  by_cases h : i < s.size
  · have h' : i < s.toByteArray.toByteSlice.size := by omega
    simp only [h, h', dite_true]
    rw [getElem_slice, getElem_slice]
    have h1 := s.stop_le_size_byteArray
    simp only [ByteSlice.size] at h
    simp [ByteArray.toByteSlice, ByteSlice.byteArray, ByteSlice.start, ByteSlice.toByteArray,
      ByteSlice.size, ByteSlice.stop, ByteArray.getElem_extract]
  · have h' : ¬ i < s.toByteArray.toByteSlice.size := by omega
    simp only [h, h', dite_false]

theorem beq_toByteArray (w s : ByteSlice) : (w == s.toByteArray.toByteSlice) = (w == s) := by
  show ByteSlice.beq _ _ = ByteSlice.beq _ _
  unfold ByteSlice.beq
  rw [toByteArray_toByteSlice]

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

/-- A token of a batch of lexemes is reported as the naive lexer reports its lexeme alone. -/
theorem toHanded_batch (b : Array Lexeme) (hb0 : Ordered 0 b.toList) (c : BatchCursor)
    (h : c.HasNext) (hb : c.intoBatch = toTokenBatch b hb0) (hj : idx c < b.size) :
    toHanded c (c.next h).1 = lexemeHanded c.version b[idx c] := by
  have hB := batchOf_toTokenBatch b hb0
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hB.entry (idx c) (by simpa using hj)
  simp only [Array.getElem_toList] at e1 e4 e5 e6 e7 e8 e9 e10
  rw [lexemeHanded_eq]
  have hcontent : (c.content (c.next h).1).toByteArray = b[idx c].content := by
    rw [content_next, hb, toByteArray_toByteSlice_range _ e2 e3, e4]
  have hcat : c.category (c.next h).1 = b[idx c].category := by
    rw [category_next, hb, e1, ofUInt8_toUInt8]
  have hstart : (c.span (c.next h).1).start = b[idx c].start := by
    rw [span_next, hb, e5, e6, e7]; rfl
  have hend : (c.span (c.next h).1).end = b[idx c].end := by
    rw [span_next, hb, e8, e9, e10]; rfl
  unfold toHanded
  simp only [BatchCursor.syntax, SyntaxToken.fromToken, hcat, hstart, hend, toContent, hcontent,
    byteArray_toList]
  cases hc : b[idx c].category <;> simp [toTokenType, lexemeReserved, toReservedKind]
  · rw [← hcontent, fromBytes_toByteArray]
    cases Reserved.fromBytes? (c.content (c.next h).1) c.version <;> rfl

end BSmtLib.Proofs.Lexer.V1NaiveV2Batched

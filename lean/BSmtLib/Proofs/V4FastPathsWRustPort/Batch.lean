import BSmtLib.Proofs.V4FastPathsWRustPort.WP
import BSmtLib.Proofs.V4FastPathsWRustPort.Feed

/-!
# The Rust port's batches

The Rust port writes its tokens into a batch whose storage it keeps from one hand-over to the
next: the arrays may be longer than the tokens in use. `Holds T ls` says that the batch `T`
holds the lexemes `ls`: its first tokens are theirs, field by field. A cursor over such a batch
is reported to the adapter's consumer as the naive lexer reports each lexeme alone
(`toHanded_holds`), and the consumer records the lexemes of the cursor (`consume_holds`).
-/

namespace BSmtLib.Proofs.Lexer.V4FastPathsWRustPort

open BSmtLib.Lexer.Internal (intoBatch)
open BSmtLib.Proofs.Adapter V1Naive V1NaiveV2Batched

/-! ## Writing an entry -/

/-- How the batch writes a number at an index of an array, at most its size. -/
def wr (a : Array Nat) (i v : Nat) : Array Nat :=
  if i < a.size then a.set! i v else a.push v

/-- How the batch writes a byte at an index of an array, at most its size. -/
def wrB (a : ByteArray) (i : Nat) (v : UInt8) : ByteArray :=
  if i < a.size then a.set! i v else a.push v

theorem size_wr (a : Array Nat) (i v : Nat) (h : i ≤ a.size) :
    i < (wr a i v).size ∧ a.size ≤ (wr a i v).size := by
  unfold wr
  split
  · rw [Array.size_set!]; omega
  · rw [Array.size_push]; omega

theorem getElem!_wr (a : Array Nat) (i v j : Nat) (h : i ≤ a.size) :
    (wr a i v)[j]! = if j = i then v else a[j]! := by
  unfold wr
  by_cases hlt : i < a.size
  · simp only [hlt, ↓reduceIte, getElem!_def, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds]
    by_cases e : j = i
    · simp [e]
    · simp [e, Ne.symm e]
  · simp only [hlt, ↓reduceIte, getElem!_def, Array.getElem?_push]
    by_cases e : j = i
    · simp [e, show i = a.size by omega]
    · simp [e, show j ≠ a.size by omega]

theorem size_wrB (a : ByteArray) (i : Nat) (v : UInt8) (h : i ≤ a.size) :
    i < (wrB a i v).size ∧ a.size ≤ (wrB a i v).size := by
  unfold wrB
  split
  · show i < (a.data.set! i v).size ∧ a.data.size ≤ (a.data.set! i v).size
    rw [Array.size_set!]; exact ⟨‹_›, Nat.le_refl _⟩
  · show i < (a.data.push v).size ∧ a.data.size ≤ (a.data.push v).size
    rw [Array.size_push]; simp only [ByteArray.size] at h; omega

theorem get!_wrB (a : ByteArray) (i : Nat) (v : UInt8) (j : Nat) (h : i ≤ a.size) :
    (wrB a i v).get! j = if j = i then v else a.get! j := by
  unfold wrB
  have hs : a.size = a.data.size := rfl
  by_cases hlt : i < a.size
  · simp only [hlt, ↓reduceIte]
    show (a.data.set! i v)[j]! = if j = i then v else a.data[j]!
    simp only [getElem!_def, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    by_cases e : j = i
    · subst e
      simp only [↓reduceIte]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show j < a.data.size by omega))]
    · simp [e, Ne.symm e]
  · simp only [hlt, ↓reduceIte]
    show (a.data.push v)[j]! = if j = i then v else a.data[j]!
    simp only [getElem!_def, Array.getElem?_push]
    by_cases e : j = i
    · subst e
      have : j = a.size := by omega
      simp only [this, hs, ↓reduceIte]
    · have : ¬ (j = a.data.size) := by omega
      simp only [e, this, ↓reduceIte]

/-! ## What a batch holds -/

/-- The batch holds the lexemes: its first tokens are theirs, with their categories, contents
and spans, in order. -/
structure Holds (T : TokenBatch) (ls : List Lexeme) : Prop where
  len : T.len = ls.length
  types : T.len ≤ T.types.size
  contentStarts : T.len ≤ T.contentStarts.size
  contentStops : T.len ≤ T.contentStops.size
  startOffsets : T.len ≤ T.startOffsets.size
  startLines : T.len ≤ T.startLines.size
  startColumns : T.len ≤ T.startColumns.size
  endOffsets : T.len ≤ T.endOffsets.size
  endLines : T.len ≤ T.endLines.size
  endColumns : T.len ≤ T.endColumns.size
  entry : ∀ j (hj : j < ls.length),
    T.types.get! j = ls[j].category.toUInt8 ∧
    T.contentStarts[j]! ≤ T.contentStops[j]! ∧ T.contentStops[j]! ≤ T.bytes.size ∧
    T.bytes.extract (T.contentStarts[j]!) (T.contentStops[j]!) = ls[j].content ∧
    T.startOffsets[j]! = ls[j].start.offset ∧ T.startLines[j]! = ls[j].start.line ∧
    T.startColumns[j]! = ls[j].start.column ∧ T.endOffsets[j]! = ls[j].end.offset ∧
    T.endLines[j]! = ls[j].end.line ∧ T.endColumns[j]! = ls[j].end.column

/-- An emptied batch holds no lexemes. -/
theorem holds_clear (T : TokenBatch) (origin : Nat) : Holds (T.clear origin) [] := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | exact Nat.zero_le _ | (intro j hj; simp at hj)

theorem holds_empty (n : Nat) : Holds (TokenBatch.empty n) [] := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | exact Nat.zero_le _ | (intro j hj; simp at hj)

theorem holds_default : Holds (default : TokenBatch) [] := holds_empty 0

/-- A batch with its contents in another array holds the same lexemes if their contents are
there too. -/
theorem Holds.bytes_congr {T : TokenBatch} {ls : List Lexeme} (h : Holds T ls)
    (bytes : ByteArray) (hb : ∀ j (hj : j < ls.length),
      T.contentStops[j]! ≤ bytes.size ∧
      bytes.extract (T.contentStarts[j]!) (T.contentStops[j]!) = ls[j].content) :
    Holds { T with bytes } ls := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, he⟩ := h
  refine ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, fun j hj => ?_⟩
  obtain ⟨e1, e2, -, -, e5, e6, e7, e8, e9, e10⟩ := he j hj
  exact ⟨e1, e2, (hb j hj).1, (hb j hj).2, e5, e6, e7, e8, e9, e10⟩

/-- A token pushed onto a batch that holds the lexemes, with the fields of the lexeme `l`. -/
theorem holds_push {T : TokenBatch} {ls : List Lexeme} (h : Holds T ls) (l : Lexeme)
    (contentStart contentStop : Nat) (hcs : contentStart ≤ contentStop)
    (hce : contentStop ≤ T.bytes.size)
    (hcontent : T.bytes.extract contentStart contentStop = l.content)
    (after : T.lastEnd ≤ l.start.offset)
    (nonempty : l.start.offset < l.end.offset ∨
      l.category = .endOfFile ∧ l.start.offset = l.end.offset) :
    Holds (T.push l.category contentStart contentStop l.start.offset l.start.line l.start.column
      l.end.offset l.end.line l.end.column after nonempty) (ls ++ [l]) := by
  obtain ⟨hlen, ht, hcs', hce', hso, hsl, hsc, heo, hel, hec, hentry⟩ := h
  have et : (T.push l.category contentStart contentStop l.start.offset l.start.line
      l.start.column l.end.offset l.end.line l.end.column after nonempty).types =
      wrB T.types T.len l.category.toUInt8 := rfl
  have e1 : (T.push l.category contentStart contentStop l.start.offset l.start.line
      l.start.column l.end.offset l.end.line l.end.column after nonempty).contentStarts =
      wr T.contentStarts T.len contentStart := rfl
  have e2 : (T.push l.category contentStart contentStop l.start.offset l.start.line
      l.start.column l.end.offset l.end.line l.end.column after nonempty).contentStops =
      wr T.contentStops T.len contentStop := rfl
  have e3 : (T.push l.category contentStart contentStop l.start.offset l.start.line
      l.start.column l.end.offset l.end.line l.end.column after nonempty).startOffsets =
      wr T.startOffsets T.len l.start.offset := rfl
  have e4 : (T.push l.category contentStart contentStop l.start.offset l.start.line
      l.start.column l.end.offset l.end.line l.end.column after nonempty).startLines =
      wr T.startLines T.len l.start.line := rfl
  have e5 : (T.push l.category contentStart contentStop l.start.offset l.start.line
      l.start.column l.end.offset l.end.line l.end.column after nonempty).startColumns =
      wr T.startColumns T.len l.start.column := rfl
  have e6 : (T.push l.category contentStart contentStop l.start.offset l.start.line
      l.start.column l.end.offset l.end.line l.end.column after nonempty).endOffsets =
      wr T.endOffsets T.len l.end.offset := rfl
  have e7 : (T.push l.category contentStart contentStop l.start.offset l.start.line
      l.start.column l.end.offset l.end.line l.end.column after nonempty).endLines =
      wr T.endLines T.len l.end.line := rfl
  have e8 : (T.push l.category contentStart contentStop l.start.offset l.start.line
      l.start.column l.end.offset l.end.line l.end.column after nonempty).endColumns =
      wr T.endColumns T.len l.end.column := rfl
  have eb : (T.push l.category contentStart contentStop l.start.offset l.start.line
      l.start.column l.end.offset l.end.line l.end.column after nonempty).bytes = T.bytes := rfl
  have el : (T.push l.category contentStart contentStop l.start.offset l.start.line
      l.start.column l.end.offset l.end.line l.end.column after nonempty).len = T.len + 1 := rfl
  refine ⟨by rw [el, hlen]; simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [el, et]; exact (size_wrB _ _ _ ht).1
  · rw [el, e1]; exact (size_wr _ _ _ hcs').1
  · rw [el, e2]; exact (size_wr _ _ _ hce').1
  · rw [el, e3]; exact (size_wr _ _ _ hso).1
  · rw [el, e4]; exact (size_wr _ _ _ hsl).1
  · rw [el, e5]; exact (size_wr _ _ _ hsc).1
  · rw [el, e6]; exact (size_wr _ _ _ heo).1
  · rw [el, e7]; exact (size_wr _ _ _ hel).1
  · rw [el, e8]; exact (size_wr _ _ _ hec).1
  intro j hj
  rw [et, e1, e2, e3, e4, e5, e6, e7, e8, eb, get!_wrB _ _ _ _ ht, getElem!_wr _ _ _ _ hcs',
    getElem!_wr _ _ _ _ hce', getElem!_wr _ _ _ _ hso, getElem!_wr _ _ _ _ hsl,
    getElem!_wr _ _ _ _ hsc, getElem!_wr _ _ _ _ heo, getElem!_wr _ _ _ _ hel,
    getElem!_wr _ _ _ _ hec]
  simp only [List.length_append, List.length_singleton] at hj
  by_cases e : j = T.len
  · subst e
    simp only [↓reduceIte]
    rw [List.getElem_append_right (by omega)]
    simp only [hlen, Nat.sub_self, List.getElem_singleton]
    refine ⟨?_, hcs, hce, hcontent, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
  · simp only [e, ↓reduceIte]
    have hlt : j < ls.length := by omega
    rw [List.getElem_append_left hlt]
    exact hentry j hlt

/-! ## Cursors over a batch -/

/-- A token of a batch that holds the lexemes is reported as the naive lexer reports its lexeme
alone. -/
theorem toHanded_holds {g : BatchTag} {ls : List Lexeme} (c : BatchCursor g) (h : c.HasNext)
    (hb : Holds (intoBatch c) ls) (hj : idx c < ls.length) :
    toHanded c (c.next h).1 = lexemeHanded c.version ls[idx c] := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10⟩ := hb.entry (idx c) hj
  rw [lexemeHanded_eq]
  have hcontent : (c.content (c.next h).1).toByteArray = ls[idx c].content := by
    rw [content_next, toByteArray_toByteSlice_range _ e2 e3, e4]
  have hcat : c.category (c.next h).1 = ls[idx c].category := by
    rw [category_next, e1, ofUInt8_toUInt8]
  have hstart : (c.span (c.next h).1).start = ls[idx c].start := by
    rw [span_next, e5, e6, e7]; rfl
  have hend : (c.span (c.next h).1).end = ls[idx c].end := by
    rw [span_next, e8, e9, e10]; rfl
  unfold toHanded
  simp only [BatchCursor.syntax, SyntaxToken.fromToken, hcat, hstart, hend, toContent, hcontent,
    byteArray_toList]
  cases hc : ls[idx c].category <;> simp [toTokenType, lexemeReserved, toReservedKind]
  · rw [← hcontent, fromBytes_toByteArray]
    cases Reserved.fromBytes? (c.content (c.next h).1) c.version <;> rfl

theorem takeRest_holds {g : BatchTag} (ls : List Lexeme) :
    ∀ n (c : BatchCursor g), c.remaining = n →
    Holds (intoBatch c) ls → idx c + c.remaining = ls.length →
    (takeRest c).1 = (ls.drop (idx c)).mapM (lexemeHanded c.version) ∧
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
    rw [List.drop_eq_nil_of_le (by omega)]
    simp [hn]
  | succ n ih =>
    intro c hn hb hs
    have hh : c.HasNext := by rw [hasNext_iff]; omega
    have hr := remaining_next c hh
    have hi := idx_next c hh
    have hj : idx c < ls.length := by omega
    obtain ⟨i1, i2, i3, i4⟩ := ih (c.next hh).2.1 (by omega) (by rw [intoBatch_next]; exact hb)
      (by omega)
    rw [takeRest]
    simp only [hh, dite_true]
    rw [toHanded_holds c hh hb hj, List.drop_eq_getElem_cons hj, List.mapM_cons]
    cases hl : lexemeHanded c.version ls[idx c] with
    | none =>
      exact ⟨rfl, fun h => absurd rfl h, rfl, rfl⟩
    | some x =>
      rw [version_next, hi] at i1
      rw [version_next] at i3
      rw [relex_next] at i4
      refine ⟨?_, ?_, i3, i4⟩
      · rw [i1]
        cases (ls.drop (idx c + 1)).mapM (lexemeHanded c.version) <;> rfl
      · intro hne
        apply i2
        intro hn'
        rw [hn'] at hne
        exact hne rfl

/-- What the adapter's consumer does with a cursor over a batch that holds the lexemes. -/
theorem consume_holds {g : BatchTag} (ls : List Lexeme) (c : BatchCursor g) (h : c.HasNext)
    (hb : Holds (intoBatch c) ls) (hs : idx c + c.remaining = ls.length) (coll : Collector) :
    (∀ hs', (ls.drop (idx c)).mapM (lexemeHanded c.version) = some hs' →
      ((Consume.consume (H := Collector) c h).run coll).1.1 = .ok .continue ∧
      ((Consume.consume (H := Collector) c h).run coll).2.handed = coll.handed ++ hs' ∧
      ((Consume.consume (H := Collector) c h).run coll).1.2.1.remaining = 0 ∧
      ((Consume.consume (H := Collector) c h).run coll).1.2.1.version = c.version ∧
      ((Consume.consume (H := Collector) c h).run coll).1.2.1.relexRequested =
        c.relexRequested) ∧
    ((ls.drop (idx c)).mapM (lexemeHanded c.version) = none →
      ((Consume.consume (H := Collector) c h).run coll).1.1 = .error ()) := by
  have hr := remaining_next c h
  have hi := idx_next c h
  have hj : idx c < ls.length := by rw [hasNext_iff] at h; omega
  obtain ⟨i1, i2, i3, i4⟩ := takeRest_holds ls _ (c.next h).2.1 rfl
    (by rw [intoBatch_next]; exact hb) (by omega)
  rw [version_next, hi] at i1
  rw [version_next] at i3
  rw [relex_next] at i4
  simp only [Consume.consume]
  rw [toHanded_holds c h hb hj, List.drop_eq_getElem_cons hj, List.mapM_cons]
  cases hl : lexemeHanded c.version ls[idx c] with
  | none =>
    refine ⟨fun hs' h' => ?_, fun _ => rfl⟩
    simp at h'
  | some x =>
    generalize hrest : takeRest (c.next h).2.1 = rest at i1 i2 i3 i4
    obtain ⟨res, last, hf⟩ := rest
    simp only at i1 i2 i3 i4
    subst i1
    cases hm : (ls.drop (idx c + 1)).mapM (lexemeHanded c.version) with
    | none =>
      refine ⟨fun hs' h' => ?_, fun _ => rfl⟩
      simp at h'
    | some ys =>
      refine ⟨fun hs' h' => ?_, fun h' => ?_⟩
      · have h'' : x :: ys = hs' := by simpa using h'
        subst h''
        exact ⟨rfl, rfl, i2 (by simp [hm]), i3, i4⟩
      · simp at h'

end BSmtLib.Proofs.Lexer.V4FastPathsWRustPort

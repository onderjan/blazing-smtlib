import BSmtLib.Token.ConsumeFrom

/-!
# Batches that agree, and cursors over them

The Rust port makes a fresh batch for every slice, where the lexer with the batch in its state
reuses one, so the arrays of the two batches hold different entries from the length of the
batch on, left over from earlier tokens. A cursor reads only the entries below the length: two
batches agree (`Agree`) when they have the same length and the same entries below it, and the
same array of contents if they have a token. Each array of a batch has an entry for each of its
tokens (`Sized`), as every batch is made from an empty one by appending; that an append keeps
the batches in agreement rests on it.

Two cursors agree (`CursorAgree`) when they are the same but for their batches, which agree,
and they yield no token beyond the length of their batch. The fields of a cursor are private to
the module of tokens, so they are read here through its recursor; a cursor's operations are
shown to keep cursors in agreement, and its reads to give the same on both.

The two cursors are over different batches, so they have different tags, and a token of one is
related to a token of the other by its index (`tokenIndex`). What the consumer may do with a
cursor is not bounded by the types: the consumer, as a function, may take the cursor apart
through its recursor, as is done here, and read the storage beyond the length of its batch,
where the two lexers differ. `ConsumesAlike` states that the consumer does not depend on that
storage: on cursors that agree it gives the same result and consumer state and cursors that
agree.
-/

namespace BSmtLib.Facts.Proofs.Lexer.Simulation.Batch

open BSmtLib.Lexer.Internal (intoBatch tag_intoBatch)

/-! ## Batches -/

/-- Each array of the batch has an entry for each of its tokens. -/
structure Sized (b : Token.TokenBatch) : Prop where
  types : b.len ≤ b.types.size
  contentStarts : b.len ≤ b.contentStarts.size
  contentStops : b.len ≤ b.contentStops.size
  startOffsets : b.len ≤ b.startOffsets.size
  startLines : b.len ≤ b.startLines.size
  startColumns : b.len ≤ b.startColumns.size
  endOffsets : b.len ≤ b.endOffsets.size
  endLines : b.len ≤ b.endLines.size
  endColumns : b.len ≤ b.endColumns.size

/-- The entries at the index of the two batches are the same. -/
structure EntryEq (b c : Token.TokenBatch) (i : Nat) : Prop where
  types : b.types.get! i = c.types.get! i
  contentStarts : b.contentStarts[i]! = c.contentStarts[i]!
  contentStops : b.contentStops[i]! = c.contentStops[i]!
  startOffsets : b.startOffsets[i]! = c.startOffsets[i]!
  startLines : b.startLines[i]! = c.startLines[i]!
  startColumns : b.startColumns[i]! = c.startColumns[i]!
  endOffsets : b.endOffsets[i]! = c.endOffsets[i]!
  endLines : b.endLines[i]! = c.endLines[i]!
  endColumns : b.endColumns[i]! = c.endColumns[i]!

/-- The two batches hold the same tokens: the same length, the same entries below it, and the
same array of contents if they have a token. -/
structure Agree (b c : Token.TokenBatch) : Prop where
  len : b.len = c.len
  bytes : b.len = 0 ∨ b.bytes = c.bytes
  entries : ∀ i, i < b.len → EntryEq b c i
  sizedLeft : Sized b
  sizedRight : Sized c

/-- The array of the batch with the entry written at `index`, as `TokenBatch.push` writes it. -/
def write (array : Array Nat) (index value : Nat) : Array Nat :=
  if h : index < array.size then array.set index value else array.push value

/-- The array of bytes of the batch with the byte written at `index`, as `TokenBatch.push`
writes it. -/
def writeByte (array : ByteArray) (index : Nat) (value : UInt8) : ByteArray :=
  if h : index < array.size then array.set index value else array.push value

theorem size_write (array : Array Nat) (index value : Nat) (h : index ≤ array.size) :
    index < (write array index value).size := by
  unfold write
  split
  · rw [Array.size_set]; assumption
  · rw [Array.size_push]; omega

theorem size_write_ge (array : Array Nat) (index value : Nat) :
    array.size ≤ (write array index value).size := by
  unfold write
  split
  · rw [Array.size_set]; exact Nat.le_refl _
  · rw [Array.size_push]; omega

theorem getElem!_write (array : Array Nat) (index value i : Nat) (h : index ≤ array.size) :
    (write array index value)[i]! = if i = index then value else array[i]! := by
  unfold write
  by_cases hlt : index < array.size
  · simp only [hlt, ↓reduceDIte, getElem!_def, Array.getElem?_set]
    by_cases e : i = index
    · simp [e]
    · simp [e, Ne.symm e]
  · simp only [hlt, ↓reduceDIte, getElem!_def, Array.getElem?_push]
    by_cases e : i = index
    · simp [e, show index = array.size by omega]
    · simp [e, show i ≠ array.size by omega]

theorem size_writeByte (array : ByteArray) (index : Nat) (value : UInt8)
    (h : index ≤ array.size) : index < (writeByte array index value).size := by
  unfold writeByte
  split
  · show index < (array.data.set index value _).size
    rw [Array.size_set]; assumption
  · show index < (array.data.push value).size
    rw [Array.size_push]; simp only [ByteArray.size] at h; omega

theorem get!_writeByte (array : ByteArray) (index : Nat) (value : UInt8) (i : Nat)
    (h : index ≤ array.size) :
    (writeByte array index value).get! i = if i = index then value else array.get! i := by
  unfold writeByte
  have hs : array.size = array.data.size := rfl
  by_cases hlt : index < array.size
  · simp only [hlt, ↓reduceDIte]
    show (array.data.set index value hlt)[i]! = if i = index then value else array.data[i]!
    simp only [getElem!_def, Array.getElem?_set]
    by_cases e : i = index
    · simp [e]
    · simp [e, Ne.symm e]
  · simp only [hlt, ↓reduceDIte]
    show (array.data.push value)[i]! = if i = index then value else array.data[i]!
    simp only [getElem!_def, Array.getElem?_push]
    by_cases e : i = index
    · simp [e, show index = array.data.size by omega]
    · simp [e, show i ≠ array.size by omega]

section push

variable (b : Token.TokenBatch) (ty : Token.TokenCategory) (cs ce so sl sc eo el ec : Nat)
  (after : b.lastEnd ≤ so) (nonempty : so < eo ∨ ty = .endOfFile ∧ so = eo)

theorem len_push' : (b.push ty cs ce so sl sc eo el ec after nonempty).len = b.len + 1 := rfl
theorem bytes_push : (b.push ty cs ce so sl sc eo el ec after nonempty).bytes = b.bytes := rfl
theorem types_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).types = writeByte b.types b.len ty.toUInt8 :=
  rfl
theorem contentStarts_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).contentStarts =
      write b.contentStarts b.len cs := rfl
theorem contentStops_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).contentStops =
      write b.contentStops b.len ce := rfl
theorem startOffsets_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).startOffsets =
      write b.startOffsets b.len so := rfl
theorem startLines_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).startLines =
      write b.startLines b.len sl := rfl
theorem startColumns_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).startColumns =
      write b.startColumns b.len sc := rfl
theorem endOffsets_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).endOffsets =
      write b.endOffsets b.len eo := rfl
theorem endLines_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).endLines =
      write b.endLines b.len el := rfl
theorem endColumns_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).endColumns =
      write b.endColumns b.len ec := rfl

end push

theorem Sized.push {b : Token.TokenBatch} (h : Sized b) (ty : Token.TokenCategory)
    (cs ce so sl sc eo el ec : Nat) (after nonempty) :
    Sized (b.push ty cs ce so sl sc eo el ec after nonempty) := by
  exact ⟨size_writeByte _ _ _ h.1, size_write _ _ _ h.2, size_write _ _ _ h.3,
    size_write _ _ _ h.4, size_write _ _ _ h.5, size_write _ _ _ h.6, size_write _ _ _ h.7,
    size_write _ _ _ h.8, size_write _ _ _ h.9⟩

theorem sized_of_len_zero {b : Token.TokenBatch} (h : b.len = 0) : Sized b := by
  constructor <;> rw [h] <;> exact Nat.zero_le _

theorem sized_empty (capacity : Nat) : Sized (Token.TokenBatch.empty capacity) :=
  sized_of_len_zero rfl

theorem sized_default : Sized (default : Token.TokenBatch) :=
  sized_of_len_zero rfl

theorem sized_clear (b : Token.TokenBatch) (origin : Nat) : Sized (b.clear origin) :=
  sized_of_len_zero rfl

theorem Sized.withBytes {b : Token.TokenBatch} (h : Sized b) (bytes : ByteArray) :
    Sized { b with bytes } :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9⟩

theorem Sized.pushOnLine {b : Token.TokenBatch} (h : Sized b) (ty : Token.TokenCategory)
    (cs ce line lineStart start «end» : Nat) (after nonempty) :
    Sized (b.pushOnLine ty cs ce line lineStart start «end» after nonempty) :=
  h.push _ _ _ _ _ _ _ _ _ _ _

theorem Sized.pushLocated {b : Token.TokenBatch} (h : Sized b) (ty : Token.TokenCategory)
    (cs ce : Nat)
    (start «end» : Span.Location) (after nonempty) :
    Sized (b.pushLocated ty cs ce start «end» after nonempty) :=
  h.push _ _ _ _ _ _ _ _ _ _ _

/-- Batches without tokens agree. -/
theorem agree_of_len_zero {b c : Token.TokenBatch} (hb : b.len = 0) (hc : c.len = 0) : Agree b c :=
  ⟨hb.trans hc.symm, .inl hb, fun _ h => absurd h (by rw [hb]; exact Nat.not_lt_zero _),
    sized_of_len_zero hb, sized_of_len_zero hc⟩

theorem agree_clear (b c : Token.TokenBatch) (o o' : Nat) : Agree (b.clear o) (c.clear o') :=
  agree_of_len_zero rfl rfl

theorem Agree.symm {b c : Token.TokenBatch} (h : Agree b c) : Agree c b where
  len := h.len.symm
  bytes := h.bytes.imp (fun e => h.len ▸ e) Eq.symm
  entries i hi := by
    have e := h.entries i (h.len ▸ hi)
    exact ⟨e.1.symm, e.2.symm, e.3.symm, e.4.symm, e.5.symm, e.6.symm, e.7.symm, e.8.symm,
      e.9.symm⟩
  sizedLeft := h.sizedRight
  sizedRight := h.sizedLeft

theorem Agree.refl {b : Token.TokenBatch} (h : Sized b) : Agree b b :=
  ⟨rfl, .inr rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, h, h⟩

theorem Agree.withBytes {b c : Token.TokenBatch} (h : Agree b c) (bytes : ByteArray) :
    Agree { b with bytes } { c with bytes } :=
  ⟨h.len, .inr rfl, fun i hi =>
    have q := h.entries i hi; ⟨q.1, q.2, q.3, q.4, q.5, q.6, q.7, q.8, q.9⟩,
    h.sizedLeft.withBytes _, h.sizedRight.withBytes _⟩

/-- Appending the same token to batches that agree, with the same array of contents. -/
theorem Agree.push {b c : Token.TokenBatch} (h : Agree b c) (hbytes : b.bytes = c.bytes)
    (ty : Token.TokenCategory) (cs ce so sl sc eo el ec : Nat) (after nonempty after' nonempty') :
    Agree (b.push ty cs ce so sl sc eo el ec after nonempty)
      (c.push ty cs ce so sl sc eo el ec after' nonempty') := by
  have sb := h.sizedLeft
  have sc' := h.sizedRight
  refine ⟨by simp only [len_push', h.len], .inr hbytes, fun i hi => ?_, sb.push .., sc'.push ..⟩
  simp only [len_push'] at hi
  have hl := h.len
  by_cases e : i = b.len
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [types_push, contentStarts_push, contentStops_push, startOffsets_push,
        startLines_push, startColumns_push, endOffsets_push, endLines_push, endColumns_push]
    · rw [get!_writeByte _ _ _ _ sb.1, get!_writeByte _ _ _ _ sc'.1]; simp [e, hl]
    · rw [getElem!_write _ _ _ _ sb.2, getElem!_write _ _ _ _ sc'.2]; simp [e, hl]
    · rw [getElem!_write _ _ _ _ sb.3, getElem!_write _ _ _ _ sc'.3]; simp [e, hl]
    · rw [getElem!_write _ _ _ _ sb.4, getElem!_write _ _ _ _ sc'.4]; simp [e, hl]
    · rw [getElem!_write _ _ _ _ sb.5, getElem!_write _ _ _ _ sc'.5]; simp [e, hl]
    · rw [getElem!_write _ _ _ _ sb.6, getElem!_write _ _ _ _ sc'.6]; simp [e, hl]
    · rw [getElem!_write _ _ _ _ sb.7, getElem!_write _ _ _ _ sc'.7]; simp [e, hl]
    · rw [getElem!_write _ _ _ _ sb.8, getElem!_write _ _ _ _ sc'.8]; simp [e, hl]
    · rw [getElem!_write _ _ _ _ sb.9, getElem!_write _ _ _ _ sc'.9]; simp [e, hl]
  · have e' : i ≠ c.len := hl ▸ e
    have lt : i < b.len := by omega
    have q := h.entries i lt
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [types_push, contentStarts_push, contentStops_push, startOffsets_push,
        startLines_push, startColumns_push, endOffsets_push, endLines_push, endColumns_push]
    · rw [get!_writeByte _ _ _ _ sb.1, get!_writeByte _ _ _ _ sc'.1]; simp [e, e', q.1]
    · rw [getElem!_write _ _ _ _ sb.2, getElem!_write _ _ _ _ sc'.2]; simp [e, e', q.2]
    · rw [getElem!_write _ _ _ _ sb.3, getElem!_write _ _ _ _ sc'.3]; simp [e, e', q.3]
    · rw [getElem!_write _ _ _ _ sb.4, getElem!_write _ _ _ _ sc'.4]; simp [e, e', q.4]
    · rw [getElem!_write _ _ _ _ sb.5, getElem!_write _ _ _ _ sc'.5]; simp [e, e', q.5]
    · rw [getElem!_write _ _ _ _ sb.6, getElem!_write _ _ _ _ sc'.6]; simp [e, e', q.6]
    · rw [getElem!_write _ _ _ _ sb.7, getElem!_write _ _ _ _ sc'.7]; simp [e, e', q.7]
    · rw [getElem!_write _ _ _ _ sb.8, getElem!_write _ _ _ _ sc'.8]; simp [e, e', q.8]
    · rw [getElem!_write _ _ _ _ sb.9, getElem!_write _ _ _ _ sc'.9]; simp [e, e', q.9]

theorem Agree.pushOnLine {b c : Token.TokenBatch} (h : Agree b c) (hbytes : b.bytes = c.bytes)
    (ty : Token.TokenCategory) (cs ce line lineStart start «end» : Nat) (after nonempty after'
      nonempty') :
    Agree (b.pushOnLine ty cs ce line lineStart start «end» after nonempty)
      (c.pushOnLine ty cs ce line lineStart start «end» after' nonempty') :=
  h.push hbytes _ _ _ _ _ _ _ _ _ _ _ _ _

theorem Agree.pushLocated {b c : Token.TokenBatch} (h : Agree b c) (hbytes : b.bytes = c.bytes)
    (ty : Token.TokenCategory) (cs ce : Nat) (start «end» : Span.Location) (after nonempty after'
      nonempty') :
    Agree (b.pushLocated ty cs ce start «end» after nonempty)
      (c.pushLocated ty cs ce start «end» after' nonempty') :=
  h.push hbytes _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ## Cursors -/

variable {g g' g₀ g₀' : Token.BatchTag}

/-- The index of the token in its batch. -/
noncomputable def tokenIndex (t : Token g) : Nat := Token.rec (fun i _ => i) t

/-- The index of the first token of the cursor's hand-over. -/
noncomputable def cFirst (c : Token.BatchCursor g) : Nat :=
  Token.BatchCursor.rec (fun _ _ _ f _ _ _ _ _ => f) c

/-- The index after the last token the cursor yields. -/
noncomputable def cStop (c : Token.BatchCursor g) : Nat :=
  Token.BatchCursor.rec (fun _ _ _ _ s _ _ _ _ => s) c

/-- The index of the cursor's next token. -/
noncomputable def cNext (c : Token.BatchCursor g) : Nat :=
  Token.BatchCursor.rec (fun _ _ _ _ _ n _ _ _ => n) c

/-- The two cursors are the same but for their batches, which agree, and yield no token beyond
the length of their batch. -/
structure CursorAgree (c : Token.BatchCursor g) (d : Token.BatchCursor g') : Prop where
  version : c.version = d.version
  batch : Agree (intoBatch c) (intoBatch d)
  first : cFirst c = cFirst d
  stop : cStop c = cStop d
  next : cNext c = cNext d
  relex : c.relexRequested = d.relexRequested
  discard : c.discardRequested = d.discardRequested
  bounded : cStop c ≤ (intoBatch c).len

theorem cNext_le_cStop (c : Token.BatchCursor g) : cNext c ≤ cStop c := by
  cases c with
  | _ v b tg f s n r dc bd => exact bd.2.1

theorem hasNext_iff (c : Token.BatchCursor g) : c.HasNext ↔ cNext c < cStop c := by
  cases c
  exact Iff.rfl

theorem CursorAgree.hasNext_iff {c : Token.BatchCursor g} {d : Token.BatchCursor g'}
    (h : CursorAgree c d) :
    c.HasNext ↔ d.HasNext := by
  rw [Batch.hasNext_iff, Batch.hasNext_iff, h.next, h.stop]

theorem cursorAgree_new (v : Token.Version) {b c : Token.TokenBatch} (h : Agree b c) :
    CursorAgree (Token.BatchCursor.new v b) (Token.BatchCursor.new v c) :=
  ⟨rfl, h, rfl, h.len, rfl, rfl, rfl, Nat.le_refl _⟩

theorem CursorAgree.takeNext {c : Token.BatchCursor g} {d : Token.BatchCursor g'}
    (h : CursorAgree c d)
    (hc : c.HasNext) (hd : d.HasNext) :
    tokenIndex (c.next hc).1 = tokenIndex (d.next hd).1 ∧
      CursorAgree (c.next hc).2.1 (d.next hd).2.1 := by
  cases c
  cases d
  obtain ⟨hv, hb, hf, hs, hn, hr, hdc, hbd⟩ := h
  simp only [cFirst, cStop, cNext] at hf hs hn hbd
  subst hf hs hn
  exact ⟨rfl, hv, hb, rfl, rfl, rfl, hr, hdc, hbd⟩

theorem CursorAgree.resetConsumed {c : Token.BatchCursor g} {d : Token.BatchCursor g'}
    (h : CursorAgree c d) : CursorAgree c.resetConsumed d.resetConsumed := by
  cases c
  cases d
  obtain ⟨hv, hb, hf, hs, hn, hr, hdc, hbd⟩ := h
  simp only [cFirst, cStop, cNext] at hf hs hn hbd
  subst hf hs hn
  exact ⟨hv, hb, rfl, rfl, rfl, hr, hdc, hbd⟩

/-- Cursors with the same tag are over the same batch. -/
theorem intoBatch_eq (c d : Token.BatchCursor g) : intoBatch c = intoBatch d :=
  Token.TokenBatch.tag_injective ((tag_intoBatch c).trans (tag_intoBatch d).symm)

theorem version_resetConsumed (c : Token.BatchCursor g) : c.resetConsumed.version = c.version := rfl

theorem cStop_le_of_follows {c d : Token.BatchCursor g} (h : c.Follows d) : cStop c ≤ cStop d := by
  cases c
  cases d
  exact h.2.1

theorem cNext_lt_of_consumed {c d : Token.BatchCursor g}
    (h : c.Consumed d) : cNext d < cNext c := by
  cases c
  cases d
  exact h.2

/-- A cursor that follows one over a batch, at most to its length, yields no token beyond the
length of the batch. -/
theorem bounded_of_follows {c d : Token.BatchCursor g} (h : c.Follows d)
    (hd : cStop d ≤ (intoBatch d).len) : cStop c ≤ (intoBatch c).len := by
  rw [intoBatch_eq c d]
  exact Nat.le_trans (cStop_le_of_follows h) hd

/-- The category of the entry at the index of the batch. -/
def categoryAt (b : Token.TokenBatch) (i : Nat) : Token.TokenCategory :=
  Token.TokenCategory.ofUInt8 (b.types.get! i)

/-- The content of the entry at the index of the batch. -/
def contentAt (b : Token.TokenBatch) (i : Nat) : ByteSlice :=
  b.bytes.toByteSlice (b.contentStarts[i]!) (b.contentStops[i]!)

/-- The span of the entry at the index of the batch. -/
def spanAt (b : Token.TokenBatch) (i : Nat) : Span :=
  Span.ofNumbers b.startOffsets[i]! b.startLines[i]! b.startColumns[i]! b.endOffsets[i]!
    b.endLines[i]! b.endColumns[i]!

theorem category_eq (c : Token.BatchCursor g) (t : Token g) :
    c.category t = categoryAt (intoBatch c) (tokenIndex t) := by
  cases t; exact Token.TokenBatch.categoryOf_eq ..

theorem content_eq (c : Token.BatchCursor g) (t : Token g) :
    c.content t = contentAt (intoBatch c) (tokenIndex t) := by
  cases t; exact Token.TokenBatch.contentOf_eq ..

theorem span_eq (c : Token.BatchCursor g) (t : Token g) :
    c.span t = spanAt (intoBatch c) (tokenIndex t) := by
  cases t; exact Token.TokenBatch.spanOf_eq ..

theorem Agree.categoryAt {b c : Token.TokenBatch} (h : Agree b c) {i : Nat} (hi : i < b.len) :
    categoryAt b i = categoryAt c i := by
  simp only [Batch.categoryAt, (h.entries i hi).types]

theorem Agree.contentAt {b c : Token.TokenBatch} (h : Agree b c) {i : Nat} (hi : i < b.len) :
    contentAt b i = contentAt c i := by
  have e := h.entries i hi
  have hb : b.bytes = c.bytes := h.bytes.resolve_left (by omega)
  unfold Batch.contentAt
  rw [hb, e.contentStarts, e.contentStops]

theorem Agree.spanAt {b c : Token.TokenBatch} (h : Agree b c) {i : Nat} (hi : i < b.len) :
    spanAt b i = spanAt c i := by
  have e := h.entries i hi
  simp only [Batch.spanAt, e.startOffsets, e.startLines, e.startColumns,
    e.endOffsets, e.endLines, e.endColumns]

/-- The category of a token below the length of the batches agrees. -/
theorem CursorAgree.category {c : Token.BatchCursor g} {d : Token.BatchCursor g'}
    (h : CursorAgree c d)
    {t : Token g} {t' : Token g'} (et : tokenIndex t = tokenIndex t')
    (ht : tokenIndex t < (intoBatch c).len) : c.category t = d.category t' := by
  rw [category_eq, category_eq, ← et, h.batch.categoryAt ht]

theorem CursorAgree.content {c : Token.BatchCursor g} {d : Token.BatchCursor g'}
    (h : CursorAgree c d)
    {t : Token g} {t' : Token g'} (et : tokenIndex t = tokenIndex t')
    (ht : tokenIndex t < (intoBatch c).len) : c.content t = d.content t' := by
  rw [content_eq, content_eq, ← et, h.batch.contentAt ht]

theorem CursorAgree.span {c : Token.BatchCursor g} {d : Token.BatchCursor g'} (h : CursorAgree c d)
    {t : Token g} {t' : Token g'} (et : tokenIndex t = tokenIndex t')
    (ht : tokenIndex t < (intoBatch c).len) : c.span t = d.span t' := by
  rw [span_eq, span_eq, ← et, h.batch.spanAt ht]

/-- The token the cursor yields next is at the index of its next token. -/
theorem tokenIndex_next (c : Token.BatchCursor g) (hc : c.HasNext) :
    tokenIndex (c.next hc).1 = cNext c := by
  cases c; rfl

/-- The token the cursor yields next is below the length of its batch. -/
theorem tokenIndex_next_lt {c : Token.BatchCursor g} (hc : c.HasNext)
    (hb : cStop c ≤ (intoBatch c).len) : tokenIndex (c.next hc).1 < (intoBatch c).len := by
  have := (Batch.hasNext_iff c).mp hc
  rw [tokenIndex_next]
  omega

/-- The token the cursor has next is at the index of its next token. -/
theorem tokenIndex_peek (c : Token.BatchCursor g) (hc : c.HasNext) :
    tokenIndex (c.peek hc) = cNext c := by
  cases c; rfl

/-- The span of the token the cursors have next agrees. -/
theorem CursorAgree.span_peek {c : Token.BatchCursor g} {d : Token.BatchCursor g'}
    (h : CursorAgree c d)
    (hc : c.HasNext) (hd : d.HasNext) : c.span (c.peek hc) = d.span (d.peek hd) := by
  have := (Batch.hasNext_iff c).mp hc
  have := h.bounded
  refine h.span (by rw [tokenIndex_peek, tokenIndex_peek, h.next]) ?_
  rw [tokenIndex_peek]
  omega

theorem consumedEndOf_eq {c c₀ : Token.BatchCursor g} (hc : c.Consumed c₀) :
    c.consumedEndOf hc = (spanAt (intoBatch c) (cNext c - 1)).end := by
  cases c; exact congrArg Span.«end» (Token.TokenBatch.spanOf_eq ..)

/-- The end of the last token consumed agrees. -/
theorem CursorAgree.consumedEndOf {c c₀ : Token.BatchCursor g} {d d₀ : Token.BatchCursor g'}
    (h : CursorAgree c d) (hc : c.Consumed c₀) (hd : d.Consumed d₀) :
    c.consumedEndOf hc = d.consumedEndOf hd := by
  have hlt := cNext_lt_of_consumed hc
  have hle := cNext_le_cStop c
  have hbd := h.bounded
  have hi : cNext c - 1 < (intoBatch c).len := by omega
  rw [consumedEndOf_eq, consumedEndOf_eq, ← h.next, h.batch.spanAt hi]

theorem consumedSpanOf_eq {c c₀ : Token.BatchCursor g} (hc : c.Consumed c₀) :
    c.consumedSpanOf hc = spanAt (intoBatch c) (cNext c - 1) := by
  cases c; exact Token.TokenBatch.spanOf_eq ..

/-- The span of the last token consumed agrees. -/
theorem CursorAgree.consumedSpanOf {c c₀ : Token.BatchCursor g} {d d₀ : Token.BatchCursor g'}
    (h : CursorAgree c d) (hc : c.Consumed c₀) (hd : d.Consumed d₀) :
    c.consumedSpanOf hc = d.consumedSpanOf hd := by
  have hlt := cNext_lt_of_consumed hc
  have hle := cNext_le_cStop c
  have hbd := h.bounded
  have hi : cNext c - 1 < (intoBatch c).len := by omega
  rw [consumedSpanOf_eq, consumedSpanOf_eq, ← h.next, h.batch.spanAt hi]

theorem foldl_congr {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (init : β), (∀ b a, a ∈ l → f b a = g b a) → l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | a :: l, init, h => by
    simp only [List.foldl_cons]
    rw [h init a (List.mem_cons_self ..)]
    exact foldl_congr l _ fun b x hx => h b x (List.mem_cons_of_mem _ hx)

theorem foldConsumedCategories_eq {β : Type} (c : Token.BatchCursor g) (init : β)
    (f : β → Token.TokenCategory → β) : c.foldConsumedCategories init f =
      (List.range (cNext c)).foldl (fun acc index => f acc (categoryAt (intoBatch c) index))
        init := by
  cases c; exact Token.BatchCursor.foldConsumedCategories_eq ..

theorem CursorAgree.foldConsumedCategories {β : Type} {c : Token.BatchCursor g}
    {d : Token.BatchCursor g'}
    (h : CursorAgree c d) (init : β) (f : β → Token.TokenCategory → β) :
    c.foldConsumedCategories init f = d.foldConsumedCategories init f := by
  have hle := cNext_le_cStop c
  have hbd := h.bounded
  rw [foldConsumedCategories_eq, foldConsumedCategories_eq, ← h.next]
  apply foldl_congr
  intro acc i hi
  have := List.mem_range.mp hi
  rw [h.batch.categoryAt (by omega)]

theorem remaining_eq (c : Token.BatchCursor g) : c.remaining = cStop c - cNext c := by
  cases c; rfl

theorem CursorAgree.remaining {c : Token.BatchCursor g} {d : Token.BatchCursor g'}
    (h : CursorAgree c d) :
    c.remaining = d.remaining := by
  rw [remaining_eq, remaining_eq, h.stop, h.next]

/-! ## The consumer -/

/--
The consumer reads the cursors it is handed only below the length of their batches: on cursors
that agree, from the same consumer state, it gives the same result and consumer state, and
cursors that agree. Both runs are the projections of one computation of such pairs.
-/
def ConsumesAlike (H : Type) (m : Type → Type) (R E : Type) [Monad m] [Token.Consume H R E]
    [∀ batch, Token.ConsumeFrom H (Token.BatchCursor batch) m] : Prop :=
  ∀ {g g' : Token.BatchTag} (c : Token.BatchCursor g) (d : Token.BatchCursor g') (hc : c.HasNext)
    (hd : d.HasNext), CursorAgree c d → ∀ s : H,
    ∃ y : m {z : (Except E (ControlFlow R) × {c' // c'.Consumed c}) ×
        (Except E (ControlFlow R) × {d' // d'.Consumed d}) × H //
        z.1.1 = z.2.1.1 ∧ CursorAgree z.1.2.val z.2.1.2.val},
      (Token.ConsumeFrom.consume c hc).run s = (fun z => (z.val.1, z.val.2.2)) <$> y ∧
        (Token.ConsumeFrom.consume d hd).run s = (fun z => (z.val.2.1, z.val.2.2)) <$> y

end BSmtLib.Facts.Proofs.Lexer.Simulation.Batch

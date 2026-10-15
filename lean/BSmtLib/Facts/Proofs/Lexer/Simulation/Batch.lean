module

public import BSmtLib.Token.ConsumeFrom
public import BSmtLib.Lexer
import all BSmtLib.Token
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.Helpers

@[expose] public section

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

open BSmtLib.Token.BatchCursor.Internal
    (consumedEndOf consumedSpanOf discardRequested foldConsumedCategories Follows relexRequested remaining resetConsumed)

/-! ## Batches -/

/-- Each array of the batch has an entry for each of its tokens. -/
structure Sized (b : Token.Internal.TokenBatch) : Prop where
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
structure EntryEq (b c : Token.Internal.TokenBatch) (i : Nat) : Prop where
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
structure Agree (b c : Token.Internal.TokenBatch) : Prop where
  len : b.len = c.len
  contents : ∀ i, i < b.len →
    (b.bytes.toByteSlice (b.contentStarts[i]!) (b.contentStops[i]!)).toByteArray =
      (c.bytes.toByteSlice (c.contentStarts[i]!) (c.contentStops[i]!)).toByteArray
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

variable (b : Token.Internal.TokenBatch) (ty : Token.TokenCategory) (cs ce so sl sc eo el ec : Nat)
  (after : b.lastEnd ≤ so) (nonempty : so < eo ∨ ty = .endOfFile ∧ so = eo)

theorem len_push' : (b.push ty cs ce so sl sc eo el ec after nonempty).len = b.len + 1 := (rfl)
theorem bytes_push : (b.push ty cs ce so sl sc eo el ec after nonempty).bytes = b.bytes := (rfl)
theorem types_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).types = writeByte b.types b.len
        (Token.TokenCategory.Internal.toUInt8 ty) :=
  (rfl)
theorem contentStarts_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).contentStarts =
      write b.contentStarts b.len cs := (rfl)
theorem contentStops_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).contentStops =
      write b.contentStops b.len ce := (rfl)
theorem startOffsets_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).startOffsets =
      write b.startOffsets b.len so := (rfl)
theorem startLines_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).startLines =
      write b.startLines b.len sl := (rfl)
theorem startColumns_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).startColumns =
      write b.startColumns b.len sc := (rfl)
theorem endOffsets_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).endOffsets =
      write b.endOffsets b.len eo := (rfl)
theorem endLines_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).endLines =
      write b.endLines b.len el := (rfl)
theorem endColumns_push :
    (b.push ty cs ce so sl sc eo el ec after nonempty).endColumns =
      write b.endColumns b.len ec := (rfl)

end push

theorem Sized.push {b : Token.Internal.TokenBatch} (h : Sized b) (ty : Token.TokenCategory)
    (cs ce so sl sc eo el ec : Nat) (after nonempty) :
    Sized (b.push ty cs ce so sl sc eo el ec after nonempty) := by
  exact ⟨size_writeByte _ _ _ h.1, size_write _ _ _ h.2, size_write _ _ _ h.3,
    size_write _ _ _ h.4, size_write _ _ _ h.5, size_write _ _ _ h.6, size_write _ _ _ h.7,
    size_write _ _ _ h.8, size_write _ _ _ h.9⟩

theorem sized_of_len_zero {b : Token.Internal.TokenBatch} (h : b.len = 0) : Sized b := by
  constructor <;> rw [h] <;> exact Nat.zero_le _

theorem sized_empty (capacity : Nat) : Sized (Token.Internal.TokenBatch.empty capacity) :=
  sized_of_len_zero rfl

theorem sized_default : Sized (default : Token.Internal.TokenBatch) :=
  sized_of_len_zero rfl

theorem sized_clear (b : Token.Internal.TokenBatch) (origin : Nat) : Sized (b.clear origin) :=
  sized_of_len_zero rfl

theorem Sized.withBytes {b : Token.Internal.TokenBatch} (h : Sized b) (bytes : ByteArray) :
    Sized { b with bytes } :=
  ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9⟩

theorem Sized.pushOnLine {b : Token.Internal.TokenBatch} (h : Sized b) (ty : Token.TokenCategory)
    (cs ce line lineStart start «end» : Nat) (after nonempty) :
    Sized (b.pushOnLine ty cs ce line lineStart start «end» after nonempty) :=
  h.push _ _ _ _ _ _ _ _ _ _ _

theorem Sized.pushLocated {b : Token.Internal.TokenBatch} (h : Sized b) (ty : Token.TokenCategory)
    (cs ce : Nat)
    (start «end» : Span.Location) (after nonempty) :
    Sized (b.pushLocated ty cs ce start «end» after nonempty) :=
  h.push _ _ _ _ _ _ _ _ _ _ _

/-- Batches without tokens agree. -/
theorem agree_of_len_zero {b c : Token.Internal.TokenBatch} (hb : b.len = 0) (hc : c.len =
    0) : Agree b c :=
  ⟨hb.trans hc.symm, fun _ h => absurd h (by rw [hb]; exact Nat.not_lt_zero _),
    fun _ h => absurd h (by rw [hb]; exact Nat.not_lt_zero _),
    sized_of_len_zero hb, sized_of_len_zero hc⟩

theorem agree_clear (b c : Token.Internal.TokenBatch) (o o' : Nat) :
    Agree (b.clear o) (c.clear o') :=
  agree_of_len_zero rfl rfl

theorem Agree.symm {b c : Token.Internal.TokenBatch} (h : Agree b c) : Agree c b where
  len := h.len.symm
  contents i hi := (h.contents i (h.len ▸ hi)).symm
  entries i hi := by
    have e := h.entries i (h.len ▸ hi)
    exact ⟨e.1.symm, e.2.symm, e.3.symm, e.4.symm, e.5.symm, e.6.symm, e.7.symm, e.8.symm,
      e.9.symm⟩
  sizedLeft := h.sizedRight
  sizedRight := h.sizedLeft

theorem Agree.refl {b : Token.Internal.TokenBatch} (h : Sized b) : Agree b b :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, h, h⟩

theorem Agree.withBytes {b c : Token.Internal.TokenBatch} (h : Agree b c) (bytes : ByteArray) :
    Agree { b with bytes } { c with bytes } :=
  ⟨h.len, fun i hi => (by
      have q := h.entries i hi
      show (bytes.toByteSlice (b.contentStarts[i]!) (b.contentStops[i]!)).toByteArray = _
      rw [q.contentStarts, q.contentStops]), fun i hi =>
    have q := h.entries i hi; ⟨q.1, q.2, q.3, q.4, q.5, q.6, q.7, q.8, q.9⟩,
    h.sizedLeft.withBytes _, h.sizedRight.withBytes _⟩

/-- Batches with the same length, the same entries below it and the same array of contents
agree. -/
theorem Agree.ofBytes {b c : Token.Internal.TokenBatch} (hlen : b.len = c.len) (hbytes : b.bytes =
    c.bytes)
    (hentries : ∀ i, i < b.len → EntryEq b c i) (hb : Sized b) (hc : Sized c) : Agree b c :=
  ⟨hlen, fun i hi => by rw [hbytes, (hentries i hi).contentStarts, (hentries i hi).contentStops],
    hentries, hb, hc⟩

/-- The entries of batches that agree, with the same token appended. -/
theorem Agree.entries_push {b c : Token.Internal.TokenBatch} (h : Agree b c)
    (ty : Token.TokenCategory) (cs ce so sl sc eo el ec : Nat) (after nonempty after' nonempty') :
    ∀ i, i < (b.push ty cs ce so sl sc eo el ec after nonempty).len →
      EntryEq (b.push ty cs ce so sl sc eo el ec after nonempty)
        (c.push ty cs ce so sl sc eo el ec after' nonempty') i := by
  have sb := h.sizedLeft
  have sc' := h.sizedRight
  intro i hi
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

/-- Appending the same token to batches that agree, with the same content of the token. -/
theorem Agree.push' {b c : Token.Internal.TokenBatch} (h : Agree b c) (ty : Token.TokenCategory)
    (cs ce so sl sc eo el ec : Nat)
    (hnew : (b.bytes.toByteSlice cs ce).toByteArray = (c.bytes.toByteSlice cs ce).toByteArray)
    (after nonempty after' nonempty') :
    Agree (b.push ty cs ce so sl sc eo el ec after nonempty)
      (c.push ty cs ce so sl sc eo el ec after' nonempty') := by
  have sb := h.sizedLeft
  have sc' := h.sizedRight
  have hl := h.len
  refine ⟨by simp only [len_push', h.len], fun i hi => ?_,
    h.entries_push ty cs ce so sl sc eo el ec after nonempty after' nonempty', sb.push ..,
    sc'.push ..⟩
  simp only [len_push'] at hi
  simp only [contentStarts_push, contentStops_push]
  rw [getElem!_write _ _ _ _ sb.2, getElem!_write _ _ _ _ sc'.2, getElem!_write _ _ _ _ sb.3,
    getElem!_write _ _ _ _ sc'.3]
  by_cases e : i = b.len
  · simp only [e, hl, ite_true]
    exact hnew
  · have e' : i ≠ c.len := hl ▸ e
    simp only [e, e', ite_false]
    exact h.contents i (by omega)

/-- Appending the same token to batches that agree, with the same array of contents. -/
theorem Agree.push {b c : Token.Internal.TokenBatch} (h : Agree b c) (hbytes : b.bytes = c.bytes)
    (ty : Token.TokenCategory) (cs ce so sl sc eo el ec : Nat) (after nonempty after' nonempty') :
    Agree (b.push ty cs ce so sl sc eo el ec after nonempty)
      (c.push ty cs ce so sl sc eo el ec after' nonempty') :=
  h.push' ty cs ce so sl sc eo el ec (by rw [hbytes]) after nonempty after' nonempty'

theorem Agree.pushOnLine {b c : Token.Internal.TokenBatch} (h : Agree b c) (hbytes : b.bytes =
    c.bytes)
    (ty : Token.TokenCategory) (cs ce line lineStart start «end» : Nat) (after nonempty after'
      nonempty') :
    Agree (b.pushOnLine ty cs ce line lineStart start «end» after nonempty)
      (c.pushOnLine ty cs ce line lineStart start «end» after' nonempty') :=
  h.push hbytes _ _ _ _ _ _ _ _ _ _ _ _ _

theorem Agree.pushLocated {b c : Token.Internal.TokenBatch} (h : Agree b c) (hbytes : b.bytes =
    c.bytes)
    (ty : Token.TokenCategory) (cs ce : Nat) (start «end» : Span.Location) (after nonempty after'
      nonempty') :
    Agree (b.pushLocated ty cs ce start «end» after nonempty)
      (c.pushLocated ty cs ce start «end» after' nonempty') :=
  h.push hbytes _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Appending the same located token to batches that agree, with the same content of the
token. -/
theorem Agree.pushLocated' {b c : Token.Internal.TokenBatch} (h : Agree b c)
    (ty : Token.TokenCategory)
    (cs ce : Nat)
    (hnew : (b.bytes.toByteSlice cs ce).toByteArray = (c.bytes.toByteSlice cs ce).toByteArray)
    (start «end» : Span.Location) (after nonempty after' nonempty') :
    Agree (b.pushLocated ty cs ce start «end» after nonempty)
      (c.pushLocated ty cs ce start «end» after' nonempty') :=
  h.push' _ _ _ _ _ _ _ _ _ hnew _ _ _ _

/-! ## Content buffers

A content buffer, like a batch, is cleared and reused, and keeps the bytes of earlier tokens
beyond its length; only the bytes below its length are its content. Two buffers agree
(`ContentAgree`) when they have the same content.
-/

/-- The content of the buffer: its bytes below its length. -/
def bufferContent (a : Lexer.Internal.Helpers.ContentBuffer) : List UInt8 :=
  a.bytes.data.toList.take a.len

/-- The two buffers have the same content. -/
def ContentAgree (a b : Lexer.Internal.Helpers.ContentBuffer) : Prop :=
  bufferContent a = bufferContent b

theorem length_bufferContent (a : Lexer.Internal.Helpers.ContentBuffer) :
    (bufferContent a).length = a.len := by
  obtain ⟨⟨d⟩, len, fits⟩ := a
  simp only [ByteArray.size] at fits
  simp only [bufferContent, List.length_take, Array.length_toList]
  omega

theorem ContentAgree.refl (a : Lexer.Internal.Helpers.ContentBuffer) : ContentAgree a a := rfl

theorem ContentAgree.symm {a b : Lexer.Internal.Helpers.ContentBuffer} (h : ContentAgree a b) :
    ContentAgree b a := Eq.symm h

theorem ContentAgree.len {a b : Lexer.Internal.Helpers.ContentBuffer} (h : ContentAgree a b) :
    a.len = b.len := by
  rw [← length_bufferContent a, ← length_bufferContent b]
  exact congrArg List.length h

theorem ContentAgree.clear (a b : Lexer.Internal.Helpers.ContentBuffer) :
    ContentAgree a.clear b.clear := by
  simp [ContentAgree, bufferContent, Lexer.Internal.Helpers.ContentBuffer.clear]

theorem ContentAgree.empty_clear (b : Lexer.Internal.Helpers.ContentBuffer) :
    ContentAgree Lexer.Internal.Helpers.ContentBuffer.empty b.clear := by
  simp [ContentAgree, bufferContent, Lexer.Internal.Helpers.ContentBuffer.empty,
    Lexer.Internal.Helpers.ContentBuffer.clear]

theorem bufferContent_push (a : Lexer.Internal.Helpers.ContentBuffer) (c : UInt8) :
    bufferContent (a.push c) = bufferContent a ++ [c] := by
  obtain ⟨⟨d⟩, len, fits⟩ := a
  simp only [ByteArray.size] at fits
  unfold bufferContent Lexer.Internal.Helpers.ContentBuffer.push
  dsimp only
  split
  · rename_i h
    simp only [ByteArray.size] at h
    show ((d.set len c h).toList.take (len + 1)) = _
    rw [Array.toList_set, List.take_set, List.take_add_one,
      List.getElem?_eq_getElem (by simpa using h)]
    simp [List.length_take, show min len d.size = len by omega]
  · rename_i h
    simp only [ByteArray.size] at h
    show ((d.push c).toList.take (len + 1)) = _
    have : len = d.size := by omega
    subst this
    simp [List.take_of_length_le]

theorem bufferContent_extendFrom (a : Lexer.Internal.Helpers.ContentBuffer) (src : ByteArray)
    (s e : Nat) :
    bufferContent (a.extendFrom src s e) = bufferContent a ++ (src.extract s e).data.toList := by
  obtain ⟨⟨d⟩, len, fits⟩ := a
  simp only [ByteArray.size] at fits
  unfold bufferContent Lexer.Internal.Helpers.ContentBuffer.extendFrom
    Lexer.Internal.Helpers.ContentBuffer.copiedCount
  dsimp only
  rw [ByteArray.copySlice_eq_append]
  simp only [ByteArray.data_append, ByteArray.data_extract, Array.toList_append,
    Array.toList_extract, List.append_assoc, List.extract_eq_take_drop, List.drop_zero,
    Nat.sub_zero]
  have hA : (d.toList.take len).length = len := by simp; omega
  have hB : (List.take (s + (e - s) - s) (src.data.toList.drop s)).length =
      min (e - s) (src.size - s) := by
    show _ = min (e - s) (src.data.size - s)
    simp only [List.length_take, List.length_drop, Array.length_toList]
    omega
  rw [List.take_append, hA, List.take_of_length_le (l := d.toList.take len) (by rw [hA]; omega),
    Nat.add_sub_cancel_left, List.take_left' hB, show s + (e - s) - s = e - s by omega]

theorem ContentAgree.push {a b : Lexer.Internal.Helpers.ContentBuffer} (h : ContentAgree a b)
    (c : UInt8) :
    ContentAgree (a.push c) (b.push c) := by
  unfold ContentAgree
  rw [bufferContent_push, bufferContent_push, h]

theorem ContentAgree.extendFrom {a b : Lexer.Internal.Helpers.ContentBuffer} (h : ContentAgree a b)
    (src : ByteArray) (s e : Nat) :
    ContentAgree (a.extendFrom src s e) (b.extendFrom src s e) := by
  unfold ContentAgree
  rw [bufferContent_extendFrom, bufferContent_extendFrom, h]

/-- A byte below the length of the buffer is a byte of its content. -/
theorem getElem_bufferContent (a : Lexer.Internal.Helpers.ContentBuffer) (i : Nat) (hi : i <
    a.len) :
    a.bytes[i]'(Nat.lt_of_lt_of_le hi a.fits) =
      (bufferContent a)[i]'(by rw [length_bufferContent]; exact hi) := by
  obtain ⟨⟨d⟩, len, fits⟩ := a
  simp [bufferContent]
  rfl

theorem ContentAgree.getElem {a b : Lexer.Internal.Helpers.ContentBuffer} (h : ContentAgree a b)
    (i : Nat)
    (hi : i < a.len) (hj : i < b.len) :
    a.bytes[i]'(Nat.lt_of_lt_of_le hi a.fits) = b.bytes[i]'(Nat.lt_of_lt_of_le hj b.fits) := by
  rw [getElem_bufferContent a i hi, getElem_bufferContent b i hj]
  simp only [ContentAgree] at h
  simp only [h]

theorem ContentAgree.size {a b : Lexer.Internal.Helpers.ContentBuffer} (h : ContentAgree a b) :
    Lexer.Internal.Helpers.Content.stored.size a
        = Lexer.Internal.Helpers.Content.stored.size b := h.len

theorem last?_bufferContent (a : Lexer.Internal.Helpers.ContentBuffer) :
    Lexer.Internal.Helpers.Content.stored.last? a = (bufferContent a).getLast? := by
  have hl := length_bufferContent a
  unfold Lexer.Internal.Helpers.Content.last?
  by_cases h0 : a.len = 0
  · simp only [h0, dite_true]
    rw [h0] at hl
    rw [List.eq_nil_of_length_eq_zero hl]
    rfl
  · simp only [h0, dite_false]
    rw [List.getLast?_eq_getElem?, hl, List.getElem?_eq_getElem (by omega),
      ← getElem_bufferContent a _ (by omega)]

theorem ContentAgree.last? {a b : Lexer.Internal.Helpers.ContentBuffer} (h : ContentAgree a b) :
    Lexer.Internal.Helpers.Content.stored.last? a
        = Lexer.Internal.Helpers.Content.stored.last? b := by
  rw [last?_bufferContent, last?_bufferContent, show bufferContent a = bufferContent b from h]

theorem ContentAgree.contentSize {a b : Lexer.Internal.Helpers.ContentBuffer} (h : ContentAgree a b)
    (k : Lexer.Internal.Helpers.Content) : k.size a = k.size b := by
  cases k
  · exact h.size
  · rfl

theorem ContentAgree.contentLast? {a b : Lexer.Internal.Helpers.ContentBuffer}
    (h : ContentAgree a b)
    (k : Lexer.Internal.Helpers.Content) : k.last? a = k.last? b := by
  cases k
  · exact h.last?
  · rfl

theorem ContentAgree.single {a b : Lexer.Internal.Helpers.ContentBuffer} (h : ContentAgree a b)
    (v : UInt8) :
    (if _ : a.len = 1 then a.bytes[0]'(by have := a.fits; omega) == v else false) =
      (if _ : b.len = 1 then b.bytes[0]'(by have := b.fits; omega) == v else false) := by
  have hl := h.len
  by_cases h1 : a.len = 1
  · have h1' : b.len = 1 := hl ▸ h1
    simp only [h1, h1', dite_true]
    rw [h.getElem 0 (by omega) (by omega)]
  · have h1' : ¬ b.len = 1 := hl ▸ h1
    simp only [h1, h1', dite_false]

/-- The content of the buffer as a slice. -/
theorem toByteArray_view (a : Lexer.Internal.Helpers.ContentBuffer) :
    a.view.toByteArray.data.toList = bufferContent a := by
  obtain ⟨⟨d⟩, len, fits⟩ := a
  simp only [ByteArray.size] at fits
  simp only [Lexer.Internal.Helpers.ContentBuffer.view, ByteArray.toByteSlice]
  rw [dite_eq_left_of_eq_true (eq_true (show len ≤ ({ data := d } : ByteArray).size from fits))]
  simp [bufferContent, ByteSlice.toByteArray, ByteSlice.byteArray, ByteSlice.start, ByteSlice.size,
    ByteSlice.stop]

/-- The contents of two buffers that agree, as slices. -/
theorem ContentAgree.view {a b : Lexer.Internal.Helpers.ContentBuffer} (h : ContentAgree a b) :
    (a.bytes.toByteSlice 0 a.len).toByteArray = (b.bytes.toByteSlice 0 b.len).toByteArray := by
  apply ByteArray.ext
  apply Array.ext'
  exact (toByteArray_view a).trans (h.trans (toByteArray_view b).symm)

/-- Batches that agree, emptied, with the content of the buffers that agree as their array of
contents, and the same token with that content appended. -/
theorem agree_stored {a a' : Lexer.Internal.Helpers.ContentBuffer} (h : ContentAgree a a')
    (b c : Token.Internal.TokenBatch) (o o' : Nat) (ty : Token.TokenCategory)
    (start «end» : Span.Location)
    (n n' : Nat) (hn : a.len = n) (hn' : a'.len = n') (after nonempty after' nonempty') :
    Agree ({ b.clear o with bytes := a.bytes } |>.pushLocated ty 0 n start «end» after nonempty)
      ({ c.clear o' with bytes := a'.bytes } |>.pushLocated ty 0 n' start «end» after'
        nonempty') := by
  have e : n' = n := by rw [← hn, ← hn', h.len]
  subst e
  have hv := h.view
  rw [← h.len, hn] at hv
  refine Agree.pushLocated' (b := { b.clear o with bytes := a.bytes })
    (c := { c.clear o' with bytes := a'.bytes }) (agree_of_len_zero rfl rfl) ty 0 n' ?_ start
    «end» _ _ _ _
  exact hv

/-- The empty slices of two arrays have the same content. -/
theorem toByteArray_toByteSlice_zero (x y : ByteArray) :
    (x.toByteSlice 0 0).toByteArray = (y.toByteSlice 0 0).toByteArray := by
  apply ByteArray.ext
  simp [ByteArray.toByteSlice, ByteSlice.toByteArray, ByteSlice.byteArray, ByteSlice.start,
    ByteSlice.size,
    ByteSlice.stop]

/-- A condition that reads a content buffer only below its length, made the same on two buffers
that agree. -/
macro "content_agree " h:term : tactic =>
  `(tactic| first | rw [($h).contentLast? _] | rw [($h).contentSize _] | rw [($h).single])

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
  batch : Agree (BSmtLib.Lexer.Internal.intoBatch c) (BSmtLib.Lexer.Internal.intoBatch d)
  first : cFirst c = cFirst d
  stop : cStop c = cStop d
  next : cNext c = cNext d
  relex : relexRequested c = relexRequested d
  discard : discardRequested c = discardRequested d
  bounded : cStop c ≤ (BSmtLib.Lexer.Internal.intoBatch c).len

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

theorem cursorAgree_new (v : Token.Version) {b c : Token.Internal.TokenBatch} (h : Agree b c) :
    CursorAgree (Token.BatchCursor.Internal.new v b) (Token.BatchCursor.Internal.new v c) :=
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
    (h : CursorAgree c d) : CursorAgree (resetConsumed c) (resetConsumed d) := by
  cases c
  cases d
  obtain ⟨hv, hb, hf, hs, hn, hr, hdc, hbd⟩ := h
  simp only [cFirst, cStop, cNext] at hf hs hn hbd
  subst hf hs hn
  exact ⟨hv, hb, rfl, rfl, rfl, hr, hdc, hbd⟩

/-- Cursors with the same tag are over the same batch. -/
theorem intoBatch_eq (c d : Token.BatchCursor g) : BSmtLib.Lexer.Internal.intoBatch c =
    BSmtLib.Lexer.Internal.intoBatch d :=
  Token.Internal.TokenBatch.tag_injective ((BSmtLib.Lexer.Internal.tag_intoBatch c).trans
      (BSmtLib.Lexer.Internal.tag_intoBatch d).symm)

theorem version_resetConsumed (c : Token.BatchCursor g) : (resetConsumed c).version = c.version :=
    (rfl)

theorem cStop_le_of_follows {c d : Token.BatchCursor g} (h : Follows c d) : cStop c ≤ cStop d := by
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
theorem bounded_of_follows {c d : Token.BatchCursor g} (h : Follows c d)
    (hd : cStop d ≤ (BSmtLib.Lexer.Internal.intoBatch d).len) : cStop c ≤
    (BSmtLib.Lexer.Internal.intoBatch c).len := by
  rw [intoBatch_eq c d]
  exact Nat.le_trans (cStop_le_of_follows h) hd

/-- The category of the entry at the index of the batch. -/
def categoryAt (b : Token.Internal.TokenBatch) (i : Nat) : Token.TokenCategory :=
  Token.TokenCategory.Internal.ofUInt8 (b.types.get! i)

/-- The content of the entry at the index of the batch. -/
def contentAt (b : Token.Internal.TokenBatch) (i : Nat) : ByteSlice :=
  b.bytes.toByteSlice (b.contentStarts[i]!) (b.contentStops[i]!)

/-- The span of the entry at the index of the batch. -/
def spanAt (b : Token.Internal.TokenBatch) (i : Nat) : Span :=
  Span.Internal.ofNumbers b.startOffsets[i]! b.startLines[i]! b.startColumns[i]! b.endOffsets[i]!
    b.endLines[i]! b.endColumns[i]!

theorem category_eq (c : Token.BatchCursor g) (t : Token g) :
    c.category t = categoryAt (BSmtLib.Lexer.Internal.intoBatch c) (tokenIndex t) := by
  cases t; exact Token.Internal.TokenBatch.categoryOf_eq ..

theorem content_eq (c : Token.BatchCursor g) (t : Token g) :
    c.content t = contentAt (BSmtLib.Lexer.Internal.intoBatch c) (tokenIndex t) := by
  cases t; exact Token.Internal.TokenBatch.contentOf_eq ..

theorem span_eq (c : Token.BatchCursor g) (t : Token g) :
    c.span t = spanAt (BSmtLib.Lexer.Internal.intoBatch c) (tokenIndex t) := by
  cases t; exact Token.Internal.TokenBatch.spanOf_eq ..

theorem Agree.categoryAt {b c : Token.Internal.TokenBatch} (h : Agree b c) {i : Nat} (hi : i <
    b.len) :
    categoryAt b i = categoryAt c i := by
  simp only [Batch.categoryAt, (h.entries i hi).types]

theorem Agree.contentAt {b c : Token.Internal.TokenBatch} (h : Agree b c) {i : Nat} (hi : i <
    b.len) :
    (contentAt b i).toByteArray = (contentAt c i).toByteArray :=
  h.contents i hi

theorem Agree.spanAt {b c : Token.Internal.TokenBatch} (h : Agree b c) {i : Nat} (hi : i < b.len) :
    spanAt b i = spanAt c i := by
  have e := h.entries i hi
  simp only [Batch.spanAt, e.startOffsets, e.startLines, e.startColumns,
    e.endOffsets, e.endLines, e.endColumns]

/-- The category of a token below the length of the batches agrees. -/
theorem CursorAgree.category {c : Token.BatchCursor g} {d : Token.BatchCursor g'}
    (h : CursorAgree c d)
    {t : Token g} {t' : Token g'} (et : tokenIndex t = tokenIndex t')
    (ht : tokenIndex t < (BSmtLib.Lexer.Internal.intoBatch c).len) : c.category t = d.category t'
    := by
  rw [category_eq, category_eq, ← et, h.batch.categoryAt ht]

theorem CursorAgree.content {c : Token.BatchCursor g} {d : Token.BatchCursor g'}
    (h : CursorAgree c d)
    {t : Token g} {t' : Token g'} (et : tokenIndex t = tokenIndex t')
    (ht : tokenIndex t < (BSmtLib.Lexer.Internal.intoBatch c).len) :
    (c.content t).toByteArray = (d.content t').toByteArray :=
    by
  rw [content_eq, content_eq, ← et, h.batch.contentAt ht]

theorem CursorAgree.span {c : Token.BatchCursor g} {d : Token.BatchCursor g'} (h : CursorAgree c d)
    {t : Token g} {t' : Token g'} (et : tokenIndex t = tokenIndex t')
    (ht : tokenIndex t < (BSmtLib.Lexer.Internal.intoBatch c).len) : c.span t = d.span t' := by
  rw [span_eq, span_eq, ← et, h.batch.spanAt ht]

/-- The token the cursor yields next is at the index of its next token. -/
theorem tokenIndex_next (c : Token.BatchCursor g) (hc : c.HasNext) :
    tokenIndex (c.next hc).1 = cNext c := by
  cases c; rfl

/-- The token the cursor yields next is below the length of its batch. -/
theorem tokenIndex_next_lt {c : Token.BatchCursor g} (hc : c.HasNext)
    (hb : cStop c ≤ (BSmtLib.Lexer.Internal.intoBatch c).len) : tokenIndex (c.next hc).1 <
    (BSmtLib.Lexer.Internal.intoBatch c).len := by
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
    (consumedEndOf c) hc = (spanAt (BSmtLib.Lexer.Internal.intoBatch c) (cNext c - 1)).end := by
  cases c; exact congrArg Span.«end» (Token.Internal.TokenBatch.spanOf_eq ..)

/-- The end of the last token consumed agrees. -/
theorem CursorAgree.consumedEndOf {c c₀ : Token.BatchCursor g} {d d₀ : Token.BatchCursor g'}
    (h : CursorAgree c d) (hc : c.Consumed c₀) (hd : d.Consumed d₀) :
    (consumedEndOf c) hc = consumedEndOf d hd := by
  have hlt := cNext_lt_of_consumed hc
  have hle := cNext_le_cStop c
  have hbd := h.bounded
  have hi : cNext c - 1 < (BSmtLib.Lexer.Internal.intoBatch c).len := by omega
  rw [consumedEndOf_eq, consumedEndOf_eq, ← h.next, h.batch.spanAt hi]

theorem consumedSpanOf_eq {c c₀ : Token.BatchCursor g} (hc : c.Consumed c₀) :
    (consumedSpanOf c) hc = spanAt (BSmtLib.Lexer.Internal.intoBatch c) (cNext c - 1) := by
  cases c; exact Token.Internal.TokenBatch.spanOf_eq ..

/-- The span of the last token consumed agrees. -/
theorem CursorAgree.consumedSpanOf {c c₀ : Token.BatchCursor g} {d d₀ : Token.BatchCursor g'}
    (h : CursorAgree c d) (hc : c.Consumed c₀) (hd : d.Consumed d₀) :
    (consumedSpanOf c) hc = consumedSpanOf d hd := by
  have hlt := cNext_lt_of_consumed hc
  have hle := cNext_le_cStop c
  have hbd := h.bounded
  have hi : cNext c - 1 < (BSmtLib.Lexer.Internal.intoBatch c).len := by omega
  rw [consumedSpanOf_eq, consumedSpanOf_eq, ← h.next, h.batch.spanAt hi]

theorem foldl_congr {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (init : β), (∀ b a, a ∈ l → f b a = g b a) → l.foldl f init = l.foldl g init
  | [], _, _ => rfl
  | a :: l, init, h => by
    simp only [List.foldl_cons]
    rw [h init a (List.mem_cons_self ..)]
    exact foldl_congr l _ fun b x hx => h b x (List.mem_cons_of_mem _ hx)

theorem foldConsumedCategories_eq {β : Type} (c : Token.BatchCursor g) (init : β)
    (f : β → Token.TokenCategory → β) : foldConsumedCategories c init f =
      (List.range (cNext c)).foldl (fun acc index => f acc
          (categoryAt (BSmtLib.Lexer.Internal.intoBatch c) index))
        init := by
  cases c; exact Token.BatchCursor.foldConsumedCategories_eq ..

theorem CursorAgree.foldConsumedCategories {β : Type} {c : Token.BatchCursor g}
    {d : Token.BatchCursor g'}
    (h : CursorAgree c d) (init : β) (f : β → Token.TokenCategory → β) :
    (foldConsumedCategories c) init f = foldConsumedCategories d init f := by
  have hle := cNext_le_cStop c
  have hbd := h.bounded
  rw [foldConsumedCategories_eq, foldConsumedCategories_eq, ← h.next]
  apply foldl_congr
  intro acc i hi
  have := List.mem_range.mp hi
  rw [h.batch.categoryAt (by omega)]

theorem remaining_eq (c : Token.BatchCursor g) : remaining c = cStop c - cNext c := by
  cases c; rfl

theorem CursorAgree.remaining {c : Token.BatchCursor g} {d : Token.BatchCursor g'}
    (h : CursorAgree c d) :
    (remaining c) = remaining d := by
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

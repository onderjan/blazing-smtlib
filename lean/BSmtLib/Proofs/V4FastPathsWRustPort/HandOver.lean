import BSmtLib.Proofs.V4FastPathsWRustPort.Batch

/-!
# The Rust port's hand-overs to the adapter's consumer

The adapter's consumer `Collector` takes every token of a cursor at once and records them; it
fails at a lexeme that it does not record (whitespace or a comment), and never switches the
version or finishes. So the Rust port's hand-over of a batch that holds lexemes leaves the lexer
state as it was, under the version, and the consumer with the lexemes recorded, or fails.
-/

namespace BSmtLib.Proofs.Lexer.V4FastPathsWRustPort

open BSmtLib.Lexer.Internal (intoBatch)
open BSmtLib.Proofs.Adapter V1Naive V1NaiveV2Batched
open Lexer.WRustPort (flushCursor callConsumer)

section

variable {floor : Option Nat} {low : Nat}

theorem idx_new' (v : Version) (b : TokenBatch) : idx (BatchCursor.new v b) = 0 := rfl

/-- The call of the consumer. -/
theorem wp_callConsumer {g : BatchTag} {cursor : BatchCursor g} {h : cursor.HasNext}
    {s : BS floor low} {coll : Collector}
    {Q : (Except Unit (ControlFlow Empty) × {c : BatchCursor g // c.Consumed cursor}) →
      BS floor low → Collector → Prop} {QE : Intr floor → BS floor low → Collector → Prop}
    (hq : Q ((Consume.consume (H := Collector) cursor h).run coll).1 s
      ((Consume.consume (H := Collector) cursor h).run coll).2) :
    WP (callConsumer (H := Collector) (m := Id) (R := Empty) (E := Unit) (floor := floor)
      (low := low) cursor h) s coll Q QE := hq

theorem intoBatch_new (v : Version) (b : TokenBatch) : intoBatch (BatchCursor.new v b) = b := rfl

/-- A postcondition holds of a state with the same value. -/
theorem q_of_val_eq {α : Type} {Q : α → BS floor low → Collector → Prop} {a : α}
    {s s' : BS floor low} {coll : Collector} (h : s'.val = s.val) (hq : Q a s coll) :
    Q a s' coll := by
  have : s' = s := Subtype.ext h
  subst this
  exact hq

/-- The hand-over of a cursor over a batch that holds the lexemes, by a lexer that does not
recover. -/
theorem flushCursor_wp (v : Version) (T : TokenBatch) (ls : List Lexeme) (hT : Holds T ls)
    (hfloor : ∀ p, floor = some p → (BatchCursor.new v T).EndsAfter p) (s : BS floor low)
    (coll : Collector) (hrec : s.val.recovers = false) (hv : s.val.version = v)
    {Q : Unit → BS floor low → Collector → Prop} {QE : Intr floor → BS floor low → Collector → Prop}
    (hok : ∀ hs, handedAll v ls = some hs → Q () s { handed := coll.handed ++ hs })
    (herr : handedAll v ls = none → ∀ e s' coll', QE e s' coll') :
    WP (flushCursor (H := Collector) (m := Id) (R := Empty) (E := Unit) (BatchCursor.new v T)
      hfloor) s coll Q QE := by
  rw [flushCursor]
  apply wp_dite
  · intro h
    have hc := consume_holds ls (BatchCursor.new v T) h (by rw [intoBatch_new]; exact hT)
      (by rw [idx_new', remaining_new, hT.len]; omega) coll
    rw [idx_new', List.drop_zero] at hc
    obtain ⟨hcok, hcerr⟩ := hc
    apply wp_bind
    apply wp_callConsumer
    generalize hX : (Consume.consume (H := Collector) (BatchCursor.new v T) h).run coll = X
      at hcok hcerr
    obtain ⟨⟨answer, next, hnext⟩, coll'⟩ := X
    cases hh : handedAll v ls with
    | none =>
      have h1 := hcerr hh
      simp only at h1
      subst h1
      dsimp only
      apply wp_bind
      apply wp_modifyCore
      apply wp_bind
      apply wp_getCore
      simp only [hrec]
      apply wp_throw
      · exact ⟨_, rfl⟩
      · exact herr hh _ _ _
    | some hs =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hcok hs hh
      simp only at h1 h2 h3 h4 h5
      subst h1
      dsimp only
      apply wp_bind
      apply wp_modifyCore
      apply wp_ite
      · intro h'
        rw [h5] at h'
        cases h'
      intro _
      rw [flushCursor]
      apply wp_dite
      · intro h'
        exfalso
        rw [hasNext_iff, BatchCursor.remaining_resetConsumed] at h'
        omega
      · intro _
        apply wp_bind
        apply wp_getCore
        simp only [hrec]
        apply wp_pure
        have e1 : coll' = { handed := coll.handed ++ hs } := by
          cases coll'; simp only at h2; rw [h2]
        have e2 : next.version = v := h4
        rw [e1]
        refine q_of_val_eq ?_ (hok hs hh)
        obtain ⟨⟨⟩, _⟩ := s
        simp only at hrec hv ⊢
        rw [e2, hrec, hv]
  · intro h
    have h0 : ls = [] := by
      rw [hasNext_iff, remaining_new, hT.len] at h
      exact List.eq_nil_of_length_eq_zero (by omega)
    apply wp_bind
    apply wp_getCore
    simp only [hrec]
    apply wp_pure
    have := hok [] (by rw [h0]; rfl)
    rwa [List.append_nil] at this

/-- The fields of the lexer state that its correspondence with the naive lexer's reads, all but
the batch and the depths. -/
def key (c : WCore) :=
  (c.version, c.state, c.discard, c.recovers, c.recoveryState, c.tokenStart, c.tokenContent,
    c.offset, c.base, c.line, c.lineStart)

/-- What the consumer records of the lexemes after what it has recorded, if it records them. -/
theorem pending_some {v : Version} {coll : Collector} {ls : List Lexeme}
    {hs : List Spec.Lexer.Handed} (h : handedAll v ls = some hs) :
    pending v coll ls = some (coll.handed ++ hs) := by
  simp [pending, h]

theorem pending_nil (v : Version) (coll : Collector) : pending v coll [] = some coll.handed := by
  simp [pending, handedAll]

theorem pending_none {v : Version} {coll : Collector} {ls : List Lexeme}
    (h : handedAll v ls = none) : pending v coll ls = none := by
  simp [pending, h]

/-- The hand-over of a cursor over a batch that holds the lexemes, with any consumer after. -/
theorem flushCursor_wp' (v : Version) (T : TokenBatch) (ls : List Lexeme) (hT : Holds T ls)
    (hfloor : ∀ p, floor = some p → (BatchCursor.new v T).EndsAfter p) (s : BS floor low)
    (coll : Collector) (hrec : s.val.recovers = false) (hv : s.val.version = v)
    {Q : Unit → BS floor low → Collector → Prop} {QE : Intr floor → BS floor low → Collector → Prop}
    (hok : ∀ coll', pending v coll' [] = pending v coll ls → Q () s coll')
    (herr : pending v coll ls = none → ∀ e s' coll', QE e s' coll') :
    WP (flushCursor (H := Collector) (m := Id) (R := Empty) (E := Unit) (BatchCursor.new v T)
      hfloor) s coll Q QE :=
  flushCursor_wp v T ls hT hfloor s coll hrec hv
    (fun hs hh => hok _ (by rw [pending_nil, pending_some hh]))
    (fun hh => herr (pending_none hh))

/-- The hand-over of the batch of the lexer state. -/
theorem flushBatch_wp (v : Version) (ls : List Lexeme) (s : BS floor low)
    (hT : Holds s.val.batch ls) (coll : Collector) (hrec : s.val.recovers = false)
    (hv : s.val.version = v)
    {Q : Unit → BS floor low → Collector → Prop} {QE : Intr floor → BS floor low → Collector → Prop}
    (hok : ∀ s' coll', key s'.val = key s.val → s'.val.batch = s.val.batch.clear s.val.offset →
      pending v coll' [] = pending v coll ls → Q () s' coll')
    (herr : pending v coll ls = none → ∀ e s' coll', QE e s' coll') :
    WP (Lexer.WRustPort.flushBatch (H := Collector) (m := Id) (R := Empty) (E := Unit)) s coll
      Q QE := by
  subst hv
  unfold Lexer.WRustPort.flushBatch
  apply wp_bind
  apply wp_modifyGetThe
  dsimp only
  apply wp_ite
  · intro h0
    apply wp_pure
    have hl : ls = [] := by
      have := hT.len
      simp only [beq_iff_eq] at h0
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hl
    exact hok _ _ rfl rfl rfl
  · intro _
    apply wp_bind
    apply wp_getCore
    refine flushCursor_wp' _ _ ls hT _ _ coll ?_ ?_ ?_ herr
    · exact hrec
    · rfl
    · intro coll' hc
      exact hok _ _ rfl rfl hc

/-- The lexeme of a token with the content and the span on a line, from the offset `start` to
the offset `end`. -/
def onLine (ty : TokenCategory) (content : ByteSlice) (line lineStart start «end» : Nat) : Lexeme :=
  { category := ty, content := content.toByteArray,
    start := { offset := start, line, column := start - lineStart },
    «end» := { offset := «end», line, column := «end» - lineStart } }

theorem extract_slice (content : ByteSlice) :
    content.byteArray.extract content.start content.stop = content.toByteArray := by
  have := content.start_le_stop
  simp only [ByteSlice.toByteArray, ByteSlice.size]
  congr 1
  omega

/-- The hand-over of the full batch that the loop of `lexNormal` holds. -/
theorem flushHeld_wp (v : Version) (batch : TokenBatch) (origin : Nat)
    (hbatch : ∀ p, floor = some p → batch.StartsFrom p) (ls : List Lexeme) (hT : Holds batch ls)
    (s : BS floor low) (coll : Collector) (hrec : s.val.recovers = false) (hv : s.val.version = v)
    {Q : {batch : TokenBatch // batch.lastEnd = origin ∧ ∀ p, floor = some p → batch.StartsFrom p} →
      BS floor low → Collector → Prop}
    {QE : Intr floor → BS floor low → Collector → Prop}
    (hok : ∀ r s' coll', r.val = batch.clear origin → key s'.val = key s.val →
      pending v coll' [] = pending v coll ls → Q r s' coll')
    (herr : pending v coll ls = none → ∀ e s' coll', QE e s' coll') :
    WP (Lexer.WRustPort.flushHeld (H := Collector) (m := Id) (R := Empty) (E := Unit) batch origin
      hbatch) s coll Q QE := by
  subst hv
  unfold Lexer.WRustPort.flushHeld
  apply wp_bind
  apply wp_modifyBound
  apply wp_bind
  apply wp_getCore
  apply wp_bind
  refine flushCursor_wp' _ _ ls hT _ _ coll ?_ ?_ ?_ herr
  · exact hrec
  · rfl
  · intro coll' hc
    apply wp_pure
    exact hok _ _ _ rfl rfl hc

/-- The hand-over of a token on the fast path into the batch that the loop of `lexNormal`
holds. -/
theorem pushFast_wp (v : Version) (batch : TokenBatch) (locals : Lexer.WRustPort.FastState)
    (offset base : Nat) (ty : TokenCategory) (content : ByteSlice) (start «end» : Nat)
    (emit : Bool) (hty : ty ≠ .endOfFile) (hstart : base ≤ start) (hend : start < «end»)
    (hframe : Lexer.WRustPort.Frame floor low offset)
    (hbatch : Lexer.WRustPort.Held floor offset base start batch)
    (ls : List Lexeme) (hT : Holds batch ls) (hb : content.byteArray = batch.bytes)
    (s : BS floor low) (coll : Collector) (hrec : s.val.recovers = false) (hv : s.val.version = v)
    {Q : {batch : TokenBatch // Lexer.WRustPort.Held floor offset base «end» batch} →
      BS floor low → Collector → Prop}
    {QE : Intr floor → BS floor low → Collector → Prop}
    (hok : ∀ r s' coll' ls', Holds r.val ls' → r.val.bytes = batch.bytes → key s'.val = key s.val →
      pending v coll' ls' = pending v coll (ls ++ if emit then
        [onLine ty content locals.line locals.lineStart (offset + (start - base))
          (offset + («end» - base))] else []) → Q r s' coll')
    (herr : pending v coll (ls ++ if emit then
        [onLine ty content locals.line locals.lineStart (offset + (start - base))
          (offset + («end» - base))] else []) = none → ∀ e s' coll', QE e s' coll') :
    WP (Lexer.WRustPort.pushFast (H := Collector) (m := Id) (R := Empty) (E := Unit) batch locals
      offset base ty content start «end» emit hty hstart hend hframe hbatch) s coll Q QE := by
  unfold Lexer.WRustPort.pushFast
  cases emit
  · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at hok herr ⊢
    split
    rename_i b' hl' hf' heq
    have hb' : b' = batch := (congrArg Subtype.val heq).symm
    subst hb'
    apply wp_ite
    · intro _
      apply wp_bind
      refine flushHeld_wp v _ _ _ ls hT s coll hrec hv ?_ herr
      intro r s' coll' hr hk hc
      obtain ⟨rb, rl, rf⟩ := r
      simp only at hr
      subst hr
      apply wp_pure
      exact hok _ s' coll' [] (holds_clear _ _) rfl hk hc
    · intro _
      apply wp_pure
      exact hok _ s coll ls hT rfl rfl rfl
  · simp only [↓reduceIte] at hok herr ⊢
    have hT' := holds_push hT
      (onLine ty content locals.line locals.lineStart (offset + (start - base))
        (offset + («end» - base))) content.start content.stop content.start_le_stop
      (by rw [← hb]; exact content.stop_le_size_byteArray)
      (by rw [← hb, extract_slice]; rfl) hbatch.1
      (.inl (show offset + (start - base) < offset + («end» - base) by omega))
    split
    rename_i b' hl' hf' heq
    have hb' := (congrArg Subtype.val heq).symm
    simp only at hb'
    subst hb'
    apply wp_ite
    · intro _
      apply wp_bind
      refine flushHeld_wp v _ _ _ _ hT' s coll hrec hv ?_ herr
      intro r s' coll' hr hk hc
      obtain ⟨rb, rl, rf⟩ := r
      simp only at hr
      subst hr
      apply wp_pure
      exact hok _ s' coll' [] (holds_clear _ _) rfl hk hc
    · intro _
      apply wp_pure
      exact hok _ s coll _ hT' rfl rfl rfl

/-- The lexeme of a token with the content on a line, from `start` to the offset `end`. -/
def borrowedLexeme (ty : TokenCategory) (content : ByteSlice) (start : Location) (line lineStart
    «end» : Nat) : Lexeme :=
  { category := ty, content := content.toByteArray, start,
    «end» := { offset := «end», line, column := «end» - lineStart } }

/-- The hand-over of a token on the slow path into the batch that the loop of `lexNormal`
holds. -/
theorem pushBorrowed_wp (v : Version) (batch : TokenBatch) (offset base : Nat)
    (ty : TokenCategory) (content : ByteSlice) (start : Location) (tokenEnd : Nat)
    (hty : ty ≠ .endOfFile) (hafter : batch.lastEnd ≤ start.offset)
    (hend : start.offset < offset + (tokenEnd - base))
    (hfloor : ∀ p, floor = some p → p ≤ start.offset ∧ batch.StartsFrom p)
    (ls : List Lexeme) (hT : Holds batch ls) (hb : content.byteArray = batch.bytes)
    (s : BS floor low) (coll : Collector) (hrec : s.val.recovers = false) (hv : s.val.version = v)
    {Q : {batch : TokenBatch // Lexer.WRustPort.Held floor offset base tokenEnd batch} →
      BS floor low → Collector → Prop}
    {QE : Intr floor → BS floor low → Collector → Prop}
    (hok : ∀ r s' coll' ls', Holds r.val ls' → r.val.bytes = batch.bytes → key s'.val = key s.val →
      pending v coll' ls' = pending v coll (ls ++
        [borrowedLexeme ty content start s.val.line s.val.lineStart (offset + (tokenEnd - base))]) →
      Q r s' coll')
    (herr : pending v coll (ls ++
        [borrowedLexeme ty content start s.val.line s.val.lineStart (offset + (tokenEnd - base))]) =
      none → ∀ e s' coll', QE e s' coll') :
    WP (Lexer.WRustPort.pushBorrowed (H := Collector) (m := Id) (R := Empty) (E := Unit) batch
      offset base ty content start tokenEnd hty hafter hend hfloor) s coll Q QE := by
  unfold Lexer.WRustPort.pushBorrowed
  apply wp_bind
  apply wp_getCore
  have hT' := holds_push hT
    (borrowedLexeme ty content start s.val.line s.val.lineStart (offset + (tokenEnd - base)))
    content.start content.stop content.start_le_stop
    (by rw [← hb]; exact content.stop_le_size_byteArray)
    (by rw [← hb, extract_slice]; rfl) hafter (.inl hend)
  dsimp only
  apply wp_ite
  · intro _
    apply wp_bind
    refine flushHeld_wp v _ _ _ _ hT' s coll hrec hv ?_ herr
    intro r s' coll' hr hk hc
    obtain ⟨rb, rl, rf⟩ := r
    simp only at hr
    subst hr
    apply wp_pure
    exact hok _ s' coll' [] (holds_clear _ _) rfl hk hc
  · intro _
    apply wp_pure
    exact hok _ s coll _ hT' rfl rfl rfl

theorem holds_of_len_zero {T : TokenBatch} (h : T.len = 0) : Holds T [] := by
  refine ⟨h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first | (rw [h]; exact Nat.zero_le _) | (intro j hj; simp at hj)

/-- The hand-over of a token whose content is in the lexer's token content, alone, after the
batch of the lexer state. -/
theorem sinkStoredAt_wp (v : Version) (ty : TokenCategory) (hty : ty ≠ .endOfFile)
    (start «end» : Location) (hend : start.offset < «end».offset)
    (hfloor : ∀ p, floor = some p → p < «end».offset) (ls : List Lexeme)
    (s : BS floor low) (hT : Holds s.val.batch ls) (coll : Collector)
    (hrec : s.val.recovers = false) (hv : s.val.version = v)
    {Q : Unit → BS floor low → Collector → Prop} {QE : Intr floor → BS floor low → Collector → Prop}
    (hok : ∀ s' coll', key s'.val = key s.val → s'.val.batch = s.val.batch.clear s.val.offset →
      pending v coll' [] = pending v coll
        (ls ++ [{ category := ty, content := s.val.tokenContent, start, «end» }]) →
      Q () s' coll')
    (herr : pending v coll
        (ls ++ [{ category := ty, content := s.val.tokenContent, start, «end» }]) = none →
      ∀ e s' coll', QE e s' coll') :
    WP (Lexer.WRustPort.sinkStoredAt (H := Collector) (m := Id) (R := Empty) (E := Unit) ty hty
      start «end» hend hfloor) s coll Q QE := by
  unfold Lexer.WRustPort.sinkStoredAt
  apply wp_bind
  refine flushBatch_wp v ls s hT coll hrec hv ?_ ?_
  · intro s1 coll1 hk1 hb1 hc1
    have hk1' := hk1
    simp only [key, Prod.mk.injEq] at hk1'
    obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hk1'
    apply wp_bind
    apply wp_getCore
    let l : Lexeme := { category := ty, content := s.val.tokenContent, start, «end» }
    have hS : Holds (({ (TokenBatch.empty 1).clear start.offset with
        bytes := s1.val.tokenContent } : TokenBatch).pushLocated ty 0 s1.val.tokenContent.size
        start «end» (Nat.le_of_eq (TokenBatch.lastEnd_clear _ _)) (.inl hend)) [l] := by
      have := holds_push (holds_of_len_zero (T := ({ (TokenBatch.empty 1).clear start.offset with
        bytes := s1.val.tokenContent } : TokenBatch)) rfl) l 0 s1.val.tokenContent.size
        (Nat.zero_le _) (Nat.le_refl _) (by rw [e7]; exact ByteArray.extract_zero_size)
        (Nat.le_of_eq (TokenBatch.lastEnd_clear _ _)) (.inl hend)
      exact this
    have hv1 : s1.val.version = v := e1.trans hv
    refine flushCursor_wp' s1.val.version _ [l] hS _ s1 coll1 (e4.trans hrec) rfl ?_ ?_
    · intro coll2 hc2
      rw [hv1] at hc2
      refine hok s1 coll2 hk1 hb1 ?_
      rw [hc2]
      have := pending_congr_append hc1 [l]
      rw [List.nil_append] at this
      exact this
    · intro hn
      rw [hv1] at hn
      apply herr
      have := pending_congr_append hc1 [l]
      rw [List.nil_append] at this
      rw [← this]
      exact hn
  · exact fun hn => herr (pending_none_append hn _)

/-- The location of the index `position` of the slice in a step whose offset `low` is that of
the index `base`, on the lexer's line. -/
def stepLocation (c : WCore) (low base position : Nat) : Location :=
  { offset := low + (position - base), line := c.line,
    column := low + (position - base) - c.lineStart }

/-- The hand-over of the token in progress, ended at `tokenEnd`, alone after the batch of the
lexer state. -/
theorem sinkStored_wp (v : Version) (ty : TokenCategory) (hty : ty ≠ .endOfFile)
    (tokenEnd : Lexer.Slice.TokenEnd) (start : Location) (base : Nat)
    (h : Lexer.WRustPort.Started floor low start) (ls : List Lexeme)
    (s : BS floor low) (hT : Holds s.val.batch ls) (coll : Collector)
    (hrec : s.val.recovers = false) (hv : s.val.version = v)
    {Q : Unit → BS floor low → Collector → Prop} {QE : Intr floor → BS floor low → Collector → Prop}
    (hok : ∀ s' coll', key s'.val = key s.val → s'.val.batch = s.val.batch.clear s.val.offset →
      pending v coll' [] = pending v coll
        (ls ++ [⟨ty, s.val.tokenContent, start, stepLocation s.val low base tokenEnd.position⟩]) →
      Q () s' coll')
    (herr : pending v coll
        (ls ++ [⟨ty, s.val.tokenContent, start, stepLocation s.val low base tokenEnd.position⟩]) =
      none → ∀ e s' coll', QE e s' coll') :
    WP (Lexer.WRustPort.sinkStored (H := Collector) (m := Id) (R := Empty) (E := Unit) ty hty
      tokenEnd start base h) s coll Q QE := by
  unfold Lexer.WRustPort.sinkStored Lexer.WRustPort.locationFrom
  apply wp_bind
  apply wp_bind
  apply wp_getCore
  apply wp_pure
  exact sinkStoredAt_wp v ty hty start _ _ _ ls s hT coll hrec hv hok herr

/-- The hand-over of the end-of-file token at the location. -/
theorem sinkEof_wp (v : Version) (location : Location) (s : BS none low) (coll : Collector)
    (hrec : s.val.recovers = false) (hv : s.val.version = v)
    {Q : Unit → BS none low → Collector → Prop} {QE : Intr none → BS none low → Collector → Prop}
    (hok : ∀ coll', pending v coll' [] = pending v coll [eofLexeme location] → Q () s coll')
    (herr : pending v coll [eofLexeme location] = none → ∀ e s' coll', QE e s' coll') :
    WP (Lexer.WRustPort.sinkEof (H := Collector) (m := Id) (R := Empty) (E := Unit) location) s
      coll Q QE := by
  unfold Lexer.WRustPort.sinkEof
  apply wp_bind
  apply wp_getCore
  have hS := holds_push (holds_clear (TokenBatch.empty 1) location.offset) (eofLexeme location) 0 0
    (Nat.le_refl _) (Nat.zero_le _) rfl (Nat.le_of_eq (TokenBatch.lastEnd_clear _ _))
    (.inr ⟨rfl, rfl⟩)
  subst hv
  exact flushCursor_wp' _ _ _ hS _ s coll hrec rfl hok herr

end

end BSmtLib.Proofs.Lexer.V4FastPathsWRustPort

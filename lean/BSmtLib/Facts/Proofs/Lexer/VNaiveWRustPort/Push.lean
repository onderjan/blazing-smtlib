module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Token

@[expose] public section

/-!
# The Rust port's hand-overs of batches and tokens, with every consumer

The hand-over of the batch of the lexer state (`flushBatch_wp`), of the batch the loop of the
normal state holds when it is full (`flushHeld_wp`, `pushFast_wp`, `pushBorrowed_wp`), of a token
whose content is in the lexer's token content (`sinkStoredAt_wp`, `sinkStored_wp`), and of the
end-of-file token (`sinkEof_wp`): if the consumer goes on, the lexer state keeps its `key` and
the consumer is where `pending` says; if it stops, the interruption is where it stops
(`Stops`), and the lexer state is left as `StopState` says.
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Push

open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Simulation.Bytes
open BSmtLib.Token.BatchCursor.Internal (EndsAfter)
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Lexer.Internal.WRustPort.Rust (flushCursor)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Batch
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Cursor
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step BSmtLib.Lexer.Internal.VNaive

/-- The lexer state `c` after a hand-over from the lexer state `s` stopped with the consumer
having done `p`: the version the consumer is in, the batch handed over, and the rest that the
correspondence reads kept, with the array of contents `bytes` of its batch. -/
structure StopState (s : WP.WCore) (p : Prog) (d : Option Span.Location) (c : WP.WCore)
    (bytes : ByteArray) :
    Prop where
  version : c.version = p.ver
  batch : Holds c.batch []
  recovers : c.recovers = s.recovers
  holding : c.holding = s.holding
  discardedFrom : c.discardedFrom = discardsAfter s.discardedFrom d
  recoveryState : c.recoveryState = s.recoveryState
  initial : c.initialVersion = s.initialVersion
  offset : c.offset = s.offset
  line : c.line = s.line
  lineStart : c.lineStart = s.lineStart
  bytes : c.batch.bytes = bytes

section

variable {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} {low : Nat}

theorem withVersion_key {s : WP.BS floor low} {p : Prog}
    (h : (p.ver == .v2_0) = (s.val.version == .v2_0)) :
    key (withVersion s p.ver).val = key s.val := by
  simp only [key, withVersion, h]

/-- The hand-over of a new cursor over a batch that holds lexemes. -/
theorem flushNew_wp (T : Token.Internal.TokenBatch) (ls : List Lexeme) (hT : Holds T ls)
    (hfloor : ∀ p, floor = some p → EndsAfter
      (Token.BatchCursor.Internal.new (s : WP.BS floor low).val.version T) p)
    (coll : List Handed) {Q : Unit → WP.BS floor low → List Handed → Prop}
    {QE : WP.Intr C floor → WP.BS floor low → List Handed → Prop} (hrec : s.val.recovers = false)
    (hok : ∀ p', pending C s.val.holding s.val.version coll ls = .cont p' →
      Q () (withVersion s p'.ver) p'.taken)
    (herr : ∀ e p d, Stops C s.val.holding s.val.version coll ls e p d →
      QE e (withDiscards s p.ver d) p.taken) :
    WP (flushCursor (H := Answering C) (m := AnswerM) (R := C.Result) (E := Option C.Error)
      (Token.BatchCursor.Internal.new s.val.version T) hfloor) s coll Q QE := by
  have hy : yields (Token.BatchCursor.Internal.new s.val.version T) ls = ls := yields_new _ T ls hT
  refine flushCursor_wp' (Token.BatchCursor.Internal.new s.val.version T) ls hT
    (by rw [cStop_new, hT.len]; exact Nat.le_refl _) rfl rfl hfloor s coll hrec rfl ?_ ?_
  · rw [hy]; exact hok
  · rw [hy]; exact herr

/-- The hand-over of the batch of the lexer state. -/
theorem flushBatch_wp (ls : List Lexeme) (s : WP.BS floor low) (hT : Holds s.val.batch ls)
    (coll : List Handed) (hrec : s.val.recovers = false)
    {Q : Unit → WP.BS floor low → List Handed → Prop}
    {QE : WP.Intr C floor → WP.BS floor low → List Handed → Prop}
    (hok : ∀ s' coll', key s'.val = key s.val → s'.val.batch = s.val.batch.clear s.val.offset →
      pending C s.val.holding s'.val.version coll' [] =
        pending C s.val.holding s.val.version coll ls →
      Q () s' coll')
    (herr : ∀ e s' p d, Stops C s.val.holding s.val.version coll ls e p d →
      StopState s.val p d s'.val s.val.batch.bytes → QE e s' p.taken) :
    WP (Lexer.Internal.WRustPort.Rust.flushBatch (H := Answering C) (m := AnswerM) (R := C.Result)
      (E := Option C.Error)) s coll Q QE := by
  unfold Lexer.Internal.WRustPort.Rust.flushBatch
  apply WP.wp_bind
  apply WP.wp_modifyGetThe
  dsimp only
  apply WP.wp_ite
  · intro h0
    apply WP.wp_pure
    have hl : ls = [] := by
      have := hT.len
      simp only [beq_iff_eq] at h0
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst hl
    exact hok _ _ rfl rfl rfl
  · intro _
    apply WP.wp_bind
    apply WP.wp_getCore
    refine flushNew_wp _ ls hT _ coll hrec ?_ ?_
    · intro p' hp
      refine hok _ _ (withVersion_key (pending_cont hp)) rfl ?_
      rw [hp]
      rfl
    · intro e p d hs
      exact herr e _ p d hs ⟨rfl, holds_clear _ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The hand-over of the full batch that the loop of `lexNormal` holds. -/
theorem flushHeld_wp (batch : Token.Internal.TokenBatch) (origin : Nat)
    (hbatch : ∀ p, floor = some p → batch.StartsFrom p) (ls : List Lexeme) (hT : Holds batch ls)
    (s : WP.BS floor low) (coll : List Handed) (hrec : s.val.recovers = false)
    {Q : {batch : Token.Internal.TokenBatch //
        batch.lastEnd = origin ∧ ∀ p, floor = some p → batch.StartsFrom p} →
      WP.BS floor low → List Handed → Prop}
    {QE : WP.Intr C floor → WP.BS floor low → List Handed → Prop}
    (hok : ∀ r s' coll', r.val = batch.clear origin → key s'.val = key s.val →
      pending C s.val.holding s'.val.version coll' [] =
        pending C s.val.holding s.val.version coll ls →
      Q r s' coll')
    (herr : ∀ e s' p d, Stops C s.val.holding s.val.version coll ls e p d →
      StopState s.val p d s'.val batch.bytes → QE e s' p.taken) :
    WP (Lexer.Internal.WRustPort.Rust.flushHeld (H := Answering C) (m := AnswerM) (R := C.Result)
      (E := Option C.Error) batch origin hbatch) s coll Q QE := by
  unfold Lexer.Internal.WRustPort.Rust.flushHeld
  apply WP.wp_bind
  apply WP.wp_modifyBound
  apply WP.wp_bind
  apply WP.wp_getCore
  apply WP.wp_bind
  refine flushNew_wp _ ls hT _ coll hrec ?_ ?_
  · intro p' hp
    apply WP.wp_pure
    refine hok _ _ _ rfl (withVersion_key (pending_cont hp)) ?_
    rw [hp]
    rfl
  · intro e p d hs
    exact herr e _ p d hs ⟨rfl, holds_clear _ _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The hand-over of a token on the fast path into the batch that the loop of `lexNormal`
holds. -/
theorem pushFast_wp (input : ByteSlice) (batch : Token.Internal.TokenBatch)
    (locals : Lexer.Internal.WRustPort.FastState) (offset base : Nat) (ty : Token.TokenCategory)
    (contentStart contentStop start «end» : Nat)
    (emit : Bool) (hty : ty ≠ .endOfFile) (hstart : base ≤ start) (hend : start < «end»)
    (hframe : Lexer.Internal.WRustPort.Frame floor low offset)
    (hbatch : Lexer.Internal.WRustPort.Held floor offset base start batch)
    (ls : List Lexeme) (hT : Holds batch ls) (hb : input.byteArray = batch.bytes)
    (hcs : contentStart ≤ contentStop) (hce : contentStop ≤ input.size)
    (s : WP.BS floor low) (coll : List Handed) (hrec : s.val.recovers = false)
    {Q : {batch : Token.Internal.TokenBatch // Lexer.Internal.WRustPort.Held floor offset base «end» batch} →
      WP.BS floor low → List Handed → Prop}
    {QE : WP.Intr C floor → WP.BS floor low → List Handed → Prop}
    (hok : ∀ r s' coll' ls', Holds r.val ls' → r.val.bytes = batch.bytes → key s'.val = key s.val →
      pending C s.val.holding s'.val.version coll' ls' =
        pending C s.val.holding s.val.version coll (ls ++ if emit then
          [onLine ty (input.slice contentStart contentStop) locals.line locals.lineStart
            (offset + (start - base)) (offset + («end» - base))] else []) → Q r s' coll')
    (herr : ∀ e s' p d, Stops C s.val.holding s.val.version coll (ls ++ if emit then
        [onLine ty (input.slice contentStart contentStop) locals.line locals.lineStart
          (offset + (start - base)) (offset + («end» - base))] else []) e p d →
      StopState s.val p d s'.val input.byteArray → QE e s' p.taken) :
    WP (Lexer.Internal.WRustPort.Rust.pushFast (H := Answering C) (m := AnswerM) (R := C.Result)
      (E := Option C.Error) input batch locals offset base ty contentStart contentStop start «end»
      emit hty hstart hend hframe hbatch) s coll Q QE := by
  unfold Lexer.Internal.WRustPort.Rust.pushFast
  cases emit
  · simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at hok herr ⊢
    split
    rename_i b' hl' hf' heq
    have hb' : b' = batch := (congrArg Subtype.val heq).symm
    subst hb'
    apply WP.wp_ite
    · intro _
      apply WP.wp_bind
      refine flushHeld_wp _ _ _ ls hT s coll hrec ?_
        (fun e s' p d hs hss => herr e s' p d hs { hss with bytes := hss.bytes.trans hb.symm })
      intro r s' coll' hr hk hc
      obtain ⟨rb, rl, rf⟩ := r
      simp only at hr
      subst hr
      apply WP.wp_pure
      exact hok _ s' coll' [] (holds_clear _ _) rfl hk hc
    · intro _
      apply WP.wp_pure
      exact hok _ s coll ls hT rfl rfl rfl
  · simp only [↓reduceIte] at hok herr ⊢
    have hT' := holds_push hT
      (onLine ty (input.slice contentStart contentStop) locals.line locals.lineStart
        (offset + (start - base)) (offset + («end» - base)))
      (input.start + contentStart) (input.start + contentStop) (extract_input input hcs hce).1
      (by rw [← hb]; exact (extract_input input hcs hce).2.1)
      (by rw [← hb, (extract_input input hcs hce).2.2]; rfl) hbatch.1
      (.inl (show offset + (start - base) < offset + («end» - base) by omega))
    split
    rename_i b' hl' hf' heq
    have hb' := (congrArg Subtype.val heq).symm
    simp only at hb'
    subst hb'
    apply WP.wp_ite
    · intro _
      apply WP.wp_bind
      refine flushHeld_wp _ _ _ _ hT' s coll hrec ?_
        (fun e s' p d hs hss => herr e s' p d hs { hss with bytes := hss.bytes.trans hb.symm })
      intro r s' coll' hr hk hc
      obtain ⟨rb, rl, rf⟩ := r
      simp only at hr
      subst hr
      apply WP.wp_pure
      exact hok _ s' coll' [] (holds_clear _ _) rfl hk hc
    · intro _
      apply WP.wp_pure
      exact hok _ s coll _ hT' rfl rfl rfl

/-- The hand-over of a token on the slow path into the batch that the loop of `lexNormal`
holds. -/
theorem pushBorrowed_wp (input : ByteSlice) (batch : Token.Internal.TokenBatch)
    (offset base : Nat) (ty : Token.TokenCategory) (contentStart contentStop : Nat)
    (start : Span.Location)
    (tokenEnd : Nat)
    (hty : ty ≠ .endOfFile) (hafter : batch.lastEnd ≤ start.offset)
    (hend : start.offset < offset + (tokenEnd - base))
    (hfloor : ∀ p, floor = some p → p ≤ start.offset ∧ batch.StartsFrom p)
    (ls : List Lexeme) (hT : Holds batch ls) (hb : input.byteArray = batch.bytes)
    (hcs : contentStart ≤ contentStop) (hce : contentStop ≤ input.size)
    (s : WP.BS floor low) (coll : List Handed) (hrec : s.val.recovers = false)
    {Q : {batch : Token.Internal.TokenBatch //
        Lexer.Internal.WRustPort.Held floor offset base tokenEnd batch} →
      WP.BS floor low → List Handed → Prop}
    {QE : WP.Intr C floor → WP.BS floor low → List Handed → Prop}
    (hok : ∀ r s' coll' ls', Holds r.val ls' → r.val.bytes = batch.bytes → key s'.val = key s.val →
      pending C s.val.holding s'.val.version coll' ls' =
        pending C s.val.holding s.val.version coll (ls ++
        [borrowedLexeme ty (input.slice contentStart contentStop) start s.val.line s.val.lineStart
          (offset + (tokenEnd - base))]) →
      Q r s' coll')
    (herr : ∀ e s' p d, Stops C s.val.holding s.val.version coll (ls ++
        [borrowedLexeme ty (input.slice contentStart contentStop) start s.val.line s.val.lineStart
          (offset + (tokenEnd - base))]) e p d →
      StopState s.val p d s'.val input.byteArray → QE e s' p.taken) :
    WP (Lexer.Internal.WRustPort.pushBorrowed (H := Answering C) (m := AnswerM) (R := C.Result)
      (E := Option C.Error) input batch offset base ty contentStart contentStop start tokenEnd hty
      hafter hend hfloor) s coll Q QE := by
  unfold Lexer.Internal.WRustPort.pushBorrowed
  apply WP.wp_bind
  apply WP.wp_getCore
  have hT' := holds_push hT
    (borrowedLexeme ty (input.slice contentStart contentStop) start s.val.line s.val.lineStart
      (offset + (tokenEnd - base)))
    (input.start + contentStart) (input.start + contentStop) (extract_input input hcs hce).1
    (by rw [← hb]; exact (extract_input input hcs hce).2.1)
    (by rw [← hb, (extract_input input hcs hce).2.2]; rfl) hafter (.inl hend)
  dsimp only
  apply WP.wp_ite
  · intro _
    apply WP.wp_bind
    refine flushHeld_wp _ _ _ _ hT' s coll hrec ?_
        (fun e s' p d hs hss => herr e s' p d hs { hss with bytes := hss.bytes.trans hb.symm })
    intro r s' coll' hr hk hc
    obtain ⟨rb, rl, rf⟩ := r
    simp only at hr
    subst hr
    apply WP.wp_pure
    exact hok _ s' coll' [] (holds_clear _ _) rfl hk hc
  · intro _
    apply WP.wp_pure
    exact hok _ s coll _ hT' rfl rfl rfl

/-- What the consumer does after lexemes, from where the consumer is after earlier ones. -/
theorem stops_congr {hd : Bool} {ver ver' : Token.Version} {c₁ c₂ : List Handed}
    {xs ys : List Lexeme} (h : pending C hd ver c₁ xs = pending C hd ver' c₂ ys)
    {e : WP.Intr C floor}
    {p : Prog} {d : Option Span.Location} (hs : Stops C hd ver c₁ xs e p d) :
    Stops C hd ver' c₂ ys e p d := by
  unfold Stops at hs ⊢
  rw [← h]
  exact hs

/-- The hand-over of a token whose content is in the lexer's token content, alone, after the
batch of the lexer state. -/
theorem sinkStoredAt_wp (ty : Token.TokenCategory)
    (start «end» : Span.Location) (hend : start.offset < «end».offset)
    (hfloor : ∀ p, floor = some p → p < «end».offset) (ls : List Lexeme)
    (s : WP.BS floor low) (hT : Holds s.val.batch ls) (coll : List Handed)
    (hrec : s.val.recovers = false) (hfits : Fits s.val.tokenContent)
    {Q : Unit → WP.BS floor low → List Handed → Prop}
    {QE : WP.Intr C floor → WP.BS floor low → List Handed → Prop}
    (hok : ∀ s' coll', key s'.val = key s.val → s'.val.batch = s.val.batch.clear s.val.offset →
      pending C s.val.holding s'.val.version coll' [] = pending C s.val.holding s.val.version coll
        (ls ++ [{ category := ty, content := contentBytes s.val.tokenContent, start, «end» }]) →
      Q () s' coll')
    (herr : ∀ e s' p d, Stops C s.val.holding s.val.version coll
        (ls ++ [{ category := ty, content := contentBytes s.val.tokenContent, start, «end» }])
          e p d →
      StopState s.val p d s'.val s.val.batch.bytes → QE e s' p.taken) :
    WP (Lexer.Internal.WRustPort.Rust.sinkStoredAt (H := Answering C) (m := AnswerM) (R := C.Result)
      (E := Option C.Error) ty start «end» hend hfloor) s coll Q QE := by
  unfold Lexer.Internal.WRustPort.Rust.sinkStoredAt
  apply WP.wp_bind
  refine flushBatch_wp ls s hT coll hrec ?_ ?_
  · intro s1 coll1 hk1 hb1 hc1
    obtain ⟨⟨e1, e1'⟩, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := key_fields hk1
    simp only [Prod.mk.injEq] at e3
    apply WP.wp_bind
    apply WP.wp_getCore
    let l : Lexeme := { category := ty, content := contentBytes s.val.tokenContent, start, «end» }
    have hS :
        Holds
        (({ (Token.Internal.TokenBatch.empty 1).clear start.offset with bytes :=
        s1.val.tokenContent.bytes } : Token.Internal.TokenBatch).pushLocated ty 0
            s1.val.tokenContent.len
        start «end» (Nat.le_of_eq (Token.Internal.TokenBatch.lastEnd_clear _ _)) (.inl hend))
            [l] := by
      have := holds_push (holds_of_len_zero (T := ({ (Token.Internal.TokenBatch.empty
          1).clear start.offset with
        bytes :=
            s1.val.tokenContent.bytes } : Token.Internal.TokenBatch)) rfl) l 0 s1.val.tokenContent.len
        (Nat.zero_le _) (by rw [e7]; exact hfits) (by rw [e7]; rfl)
        (Nat.le_of_eq (Token.Internal.TokenBatch.lastEnd_clear _ _)) (.inl hend)
      exact this
    have hcong := pending_congr_append C s.val.holding hc1 [l]
    rw [List.nil_append] at hcong
    refine flushNew_wp _ [l] hS _ coll1 (e4.trans hrec) ?_ ?_
    · intro p' hp
      refine hok _ _ ((withVersion_key (pending_cont hp)).trans hk1) hb1 ?_
      rw [e3.2] at hp
      show HandOut.cont ⟨p'.taken, p'.ver⟩ = _
      rw [← hcong, hp]
    · intro e p d hs
      rw [e3.2] at hs
      refine herr e _ p d (stops_congr hcong hs) ⟨rfl, ?_, e4, e3.2,
        by show discardsAfter _ d = _; rw [e3.1], e5, e1', e8, e10, e11,
        by show s1.val.batch.bytes = _; rw [hb1]; rfl⟩
      show Holds s1.val.batch []
      rw [hb1]
      exact holds_clear _ _
  · intro e s' p d hs hss
    exact herr e s' p d (hs.append _) hss

/-- The hand-over of the token in progress, ended at `tokenEnd`, alone after the batch of the
lexer state. -/
theorem sinkStored_wp (ty : Token.TokenCategory)
    (tokenEnd : Lexer.Internal.WRustPort.Slice.TokenEnd) (start : Span.Location) (base : Nat)
    (h : Lexer.Internal.WRustPort.Started floor low start) (ls : List Lexeme)
    (s : WP.BS floor low) (hT : Holds s.val.batch ls) (coll : List Handed)
    (hrec : s.val.recovers = false) (hfits : Fits s.val.tokenContent)
    {Q : Unit → WP.BS floor low → List Handed → Prop}
    {QE : WP.Intr C floor → WP.BS floor low → List Handed → Prop}
    (hok : ∀ s' coll', key s'.val = key s.val → s'.val.batch = s.val.batch.clear s.val.offset →
      pending C s.val.holding s'.val.version coll' [] = pending C s.val.holding s.val.version coll
        (ls ++ [⟨ty, contentBytes s.val.tokenContent, start,
          stepLocation s.val low base tokenEnd.position⟩]) →
      Q () s' coll')
    (herr : ∀ e s' p d, Stops C s.val.holding s.val.version coll
        (ls ++ [⟨ty, contentBytes s.val.tokenContent, start,
          stepLocation s.val low base tokenEnd.position⟩]) e p d →
      StopState s.val p d s'.val s.val.batch.bytes → QE e s' p.taken) :
    WP (Lexer.Internal.WRustPort.sinkStored (H := Answering C) (m := AnswerM) (R := C.Result)
      (E := Option C.Error) ty tokenEnd start base h) s coll Q QE := by
  unfold Lexer.Internal.WRustPort.sinkStored Lexer.Internal.WRustPort.locationFrom
  apply WP.wp_bind
  apply WP.wp_bind
  apply WP.wp_getCore
  apply WP.wp_pure
  exact sinkStoredAt_wp ty start _ _ _ ls s hT coll hrec hfits hok herr

/-- The hand-over of the end-of-file token at the location, unless a result is held. -/
theorem sinkEof_wp (location : Span.Location) (s : WP.BS none low) (coll : List Handed)
    (hrec : s.val.recovers = false)
    {Q : Unit → WP.BS none low → List Handed → Prop} {QE : WP.Intr C none → WP.BS none low →
        List Handed → Prop}
    (hheld : s.val.holding = true → Q () s coll)
    (hok : s.val.holding = false → ∀ p', pending C false s.val.version coll [eofLexeme location] =
      .cont p' → Q () (withVersion s p'.ver) p'.taken)
    (herr : s.val.holding = false → ∀ e p d,
      Stops C false s.val.version coll [eofLexeme location] e p d →
      QE e (withDiscards s p.ver d) p.taken) :
    WP (Lexer.Internal.WRustPort.Rust.sinkEof (H := Answering C) (m := AnswerM) (R := C.Result)
      (E := Option C.Error) location) s coll Q QE := by
  unfold Lexer.Internal.WRustPort.Rust.sinkEof
  apply WP.wp_bind
  apply WP.wp_getCore
  cases hh : s.val.holding with
  | true =>
    simp only [↓reduceIte]
    exact WP.wp_pure _ (hheld hh)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply WP.wp_bind
    apply WP.wp_getCore
    have hS := holds_push (holds_of_len_zero (T := ({ (Token.Internal.TokenBatch.empty 1).clear
        location.offset with
        bytes := s.val.tokenContent.bytes } : Token.Internal.TokenBatch)) rfl)
            (eofLexeme location) 0 0
      (Nat.le_refl _) (Nat.zero_le _) (by rw [ByteArray.extract_same]; rfl)
      (Nat.le_of_eq (Token.Internal.TokenBatch.lastEnd_clear _ _))
      (.inr ⟨rfl, rfl⟩)
    refine flushNew_wp _ _ hS _ coll hrec ?_ ?_
    · rw [hh]; exact hok hh
    · rw [hh]; exact herr hh

/-- A step interrupted where the consumer stopped on lexemes handed over from the lexer state
`s`, which is fixed. -/
theorem stepFails_of_stops' {v : Token.Version} {hd : Bool} {iv : Token.Version}
    {input : ByteSlice} {st : St}
    {location : Span.Location} {start : Nat} {ver : Token.Version} {coll : List Handed}
    {held : List Lexeme} {s c : WP.WCore} {p : Prog} {d : Option Span.Location} {bytes : ByteArray}
    (hss : StopState s p d c bytes)
    (hfix : Fixed v hd iv s) {ver1 : Token.Version} {coll1 : List Handed} {held1 : List Lexeme}
    (h : ∃ rest, outcome C hd (pending C hd ver coll held)
        (feedFrom v C.concrete input st location start) =
      outcome C hd (pending C hd ver1 coll1 held1) rest)
    {e : WP.Intr C floor} (hs : Stops C s.holding ver1 coll1 held1 e p d)
    (hbytes : bytes = input.byteArray := by first | rfl | assumption) :
    StepFails C v hd iv input st location start ver coll held e c p.taken := by
  rw [hfix.holding] at hs
  exact stepFails_of_stops h.choose_spec hs hss.version hss.batch
    (hss.recovers.trans hfix.recovers)
    (hss.holding.trans hfix.holding)
    (hss.discardedFrom.trans (by rw [hfix.discardedFrom]; cases d <;> rfl))
    (hss.recoveryState.trans hfix.recoveryState) (hss.initial.trans hfix.initial)
    (hss.bytes.trans hbytes)

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Push

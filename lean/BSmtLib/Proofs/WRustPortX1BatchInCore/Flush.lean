import BSmtLib.Proofs.WRustPortX1BatchInCore.HandOver

/-!
# The hand-overs of a batch, of a token alone and of the end of the input

Where the Rust port empties the batch in its state and hands it over, the lexer with the batch
in its state takes the batch out of its state, hands it over and puts it back emptied; where the
Rust port hands a token over alone in a batch of its own, the other puts it into its batch. The
batches handed over agree, and the batches in the states have no tokens after the hand-over;
their arrays of contents stay the same as before in both.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation (M runM)
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} {strict : Bool} {Er : WS floor low → XS floor low → Prop}

/-- The two states correspond with the Rust port's line and line start `l` and `ls`, and their
batches have no tokens. -/
abbrev SRE (l ls : Nat) (s : WS floor low) (t : XS floor low) : Prop :=
  SRL l ls s t ∧ s.val.batch.len = 0

/-- `SRE`, and the same arrays of contents of the batches where the simulation is strict. -/
abbrev SREb (strict : Bool) (l ls : Nat) (s : WS floor low) (t : XS floor low) : Prop :=
  SRE l ls s t ∧ BytesEq strict s.val.batch t.val.batch

/-- A hand-over of batches that agree, in the version of the lexers, from states whose batches
have no tokens; where the simulation is strict, the Rust port's batch has the array of contents
the other gives its batch back with. -/
theorem handOver_sim' (hcons : ConsumesAlike H m R E) (l ls : Nat) (v : Version)
    (b b' : TokenBatch) (hb : Agree b b') (bytesAfter : ByteArray) (hf hf') :
    SimR (ErZ strict) (fun s t => SRE l ls s t ∧ s.val.version = v ∧
        (strict = true → s.val.batch.bytes = bytesAfter))
      (fun _ spent s t => SRE l ls s t ∧ t.val.batch.len = 0 ∧
        spent = { b' with bytes := bytesAfter } ∧
        (strict = true → s.val.batch.bytes = bytesAfter))
      (Lexer.WRustPort.flushCursor (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) (BatchCursor.new v b) hf)
      (Lexer.X1BatchInCore.handOver b' bytesAfter hf') := by
  rw [handOver_eq]
  refine getCore_bind_right fun s₀ t₀ h₀ => ?_
  obtain ⟨⟨⟨hst, hl, hls⟩, hlen⟩, hv, hby⟩ := h₀
  have hcd : CursorAgree (BatchCursor.new v b) (BatchCursor.new t₀.val.version b') := by
    rw [← hst.version, hv]
    exact cursorAgree_new _ hb
  refine SimR.mono (fun s t h => ?_) (fun _ spent s t h => ?_) (fun _ _ h => h)
    (flushCursor_sim hcons l ls s₀.val.batch t₀.val.batch hlen bytesAfter hby _ _ _ rfl hcd _ _)
  · obtain ⟨hs, ht⟩ := h
    subst hs ht
    exact ⟨hst.toSameBut, hv, rfl, rfl, hl, hls⟩
  · obtain ⟨⟨hsame, hv, hbw, hbx, hl', hls'⟩, hspent⟩ := h
    refine ⟨⟨⟨{ toSameBut := hsame, version := hv, batch := ?_, capacity := ?_ }, hl', hls'⟩,
      by rw [hbw]; exact hlen⟩, ?_, hspent, by rw [hbw]; exact hby⟩
    · rw [hbw, hbx]; exact agree_of_len_zero hlen (hst.batch.len ▸ hlen)
    · rw [hbw, hlen]; decide
    · rw [hbx, ← hst.batch.len]; exact hlen

/-- `handOver_sim'` with the interruptions thrown from states with `ErS`. -/
theorem handOver_simS (hcons : ConsumesAlike H m R E) (l ls : Nat) (v : Version)
    (b b' : TokenBatch) (hb : Agree b b') (bytesAfter : ByteArray) (hf hf') :
    LSim strict (fun s t => SRE l ls s t ∧ s.val.version = v ∧
        (strict = true → s.val.batch.bytes = bytesAfter))
      (fun _ spent s t => SRE l ls s t ∧ t.val.batch.len = 0 ∧
        spent = { b' with bytes := bytesAfter } ∧
        (strict = true → s.val.batch.bytes = bytesAfter))
      (Lexer.WRustPort.flushCursor (H := H) (m := m) (R := R) (E := E) (floor := floor)
        (low := low) (BatchCursor.new v b) hf)
      (Lexer.X1BatchInCore.handOver b' bytesAfter hf') :=
  SimR.mono (fun _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ h => h.1)
    (handOver_sim' hcons l ls v b b' hb bytesAfter hf hf')

omit [Consume H m R E] in
/-- The lexer with the batch in its state puts the batch back, from states with `SRE`. -/
theorem storeSpent_right {α : Type} (l ls : Nat) (a : α) (spent : TokenBatch) :
    SimR (m := m) (H := H) (ε := Interrupted R E floor) Er
      (fun s t => SRE (floor := floor) (low := low) l ls s t ∧
        (strict = true → s.val.batch.bytes = spent.bytes))
      (fun x _ s t => x = a ∧ SREb strict l ls s t)
      (pure a) (Lexer.X1BatchInCore.storeSpent spent) := by
  unfold Lexer.X1BatchInCore.storeSpent Lexer.X1BatchInCore.modifyBound
  refine SimR.modifyGet_right fun s t h => ⟨rfl, ⟨⟨⟨?_, h.1.1.2⟩, h.1.2⟩, h.2⟩⟩
  obtain ⟨⟨⟨hst, -, -⟩, hlen⟩, -⟩ := h
  exact { hst with batch := agree_of_len_zero hlen rfl }

theorem flushBatch_simZ (hcons : ConsumesAlike H m R E) (l ls : Nat) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low)
      (ErZ strict)
      (SRLb strict l ls) (fun _ _ => SREb strict l ls) Lexer.WRustPort.flushBatch
      Lexer.X1BatchInCore.flushBatch := by
  unfold Lexer.WRustPort.flushBatch Lexer.X1BatchInCore.flushBatch
  refine SimR.modifyGet_bind_left fun s t h => ?_
  refine getCore_bind_right fun s' t' h' => ?_
  obtain ⟨hs', ht'⟩ := h'
  subst s' t'
  obtain ⟨⟨hst, hl, hls⟩, hby⟩ := h
  have hlen := hst.batch.len
  refine SimR.ite (by simp only [beq_iff_eq, hlen]) (fun hz => ?_) fun hz => ?_
  · refine SimR.pure fun s' t' h' => ?_
    obtain ⟨hs', ht'⟩ := h'
    subst s' t'
    have hz : s.val.batch.len = 0 := by simpa using hz
    have ha := agree_of_len_zero (b := s.val.batch.clear s.val.offset) rfl (hlen ▸ hz)
    exact ⟨⟨⟨{ hst with batch := ha, capacity := zero_lt_capacity }, hl, hls⟩, rfl⟩, hby⟩
  · refine SimR.modifyGet_bind_right fun s' t' h' => ?_
    obtain ⟨hs', ht'⟩ := h'
    subst s' t'
    dsimp only
    refine SimR.of_bind_pure_left (SimR.bind (getCore_bind_left fun s₀ t₀ h₀ => SimR.pre ?_
      (handOver_sim' hcons l ls s₀.val.version s.val.batch t.val.batch hst.batch
        t.val.batch.bytes _ _)) fun _ spent => ?_)
    · intro s'' t'' h''
      obtain ⟨hs'', ht''⟩ := h''
      subst s'' t''
      obtain ⟨hs₀, ht₀⟩ := h₀
      subst hs₀ ht₀
      exact ⟨⟨⟨{ hst with batch := agree_of_len_zero rfl rfl, capacity := zero_lt_capacity }, hl,
        hls⟩, rfl⟩, rfl, hby⟩
    · refine SimR.post (fun _ _ _ _ h => h.2) (SimR.pre (fun _ _ h => ⟨h.1, ?_⟩)
        (storeSpent_right l ls _ _))
      rw [h.2.2.1]
      exact h.2.2.2

theorem flushBatch_sim (hcons : ConsumesAlike H m R E) (l ls : Nat) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low)
      (SRLb strict l ls) (fun _ _ => SREb strict l ls) Lexer.WRustPort.flushBatch
      Lexer.X1BatchInCore.flushBatch :=
  SimR.mono (fun _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ h => h.1) (flushBatch_simZ hcons l ls)

theorem handOverStored_simZ (hcons : ConsumesAlike H m R E) (l ls : Nat) (ty : TokenCategory)
    (hty : ty ≠ .endOfFile) (start «end» : Location) (hend : start.offset < «end».offset)
    (hfloor hfloor') :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low)
      (ErZ strict)
      (SRLb strict l ls) (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.sinkStoredAt ty hty start «end» hend hfloor)
      (Lexer.X1BatchInCore.handOverStored ty hty start «end» hend hfloor') := by
  unfold Lexer.WRustPort.sinkStoredAt Lexer.X1BatchInCore.handOverStored
  refine SimR.seq (flushBatch_simZ hcons l ls) ?_
  refine SimR.modifyGet_bind_right fun s t h => ?_
  dsimp only
  refine getCore_bind fun w x => ?_
  refine SimR.intro fun s₀ t₀ h₀ => ?_
  obtain ⟨⟨hs, ht⟩, hw, hx⟩ := h₀
  subst w x s₀ t₀
  obtain ⟨⟨⟨hst, hl, hls⟩, hlen⟩, hby⟩ := h
  have hc : s.val.tokenContent = t.val.tokenContent := hst.tokenContent
  refine SimR.of_bind_pure_left (SimR.bind (SimR.pre ?_ (handOver_sim' hcons l ls s.val.version
    _ _ ?_ t.val.batch.bytes _ _)) fun _ spent => ?_)
  · intro s' t' h'
    obtain ⟨-, hs', ht'⟩ := h'
    subst hs' ht'
    exact ⟨⟨⟨{ hst with batch := agree_of_len_zero hlen rfl, capacity := by rw [hlen]; decide },
      hl, hls⟩, hlen⟩, rfl, hby⟩
  · rw [hc]
    exact ((agree_clear (TokenBatch.empty 1) t.val.batch start.offset start.offset).withBytes
      t.val.tokenContent).pushLocated rfl ty 0 t.val.tokenContent.size start «end» _ _ _ _
  · refine SimR.post (fun _ _ _ _ h => h.2) (SimR.pre (fun _ _ h => ⟨h.1, ?_⟩)
      (storeSpent_right l ls _ _))
    rw [h.2.2.1]
    exact h.2.2.2

theorem handOverStored_sim (hcons : ConsumesAlike H m R E) (l ls : Nat) (ty : TokenCategory)
    (hty : ty ≠ .endOfFile) (start «end» : Location) (hend : start.offset < «end».offset)
    (hfloor hfloor') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low)
      (SRLb strict l ls) (fun _ _ => SREb strict l ls)
      (Lexer.WRustPort.sinkStoredAt ty hty start «end» hend hfloor)
      (Lexer.X1BatchInCore.handOverStored ty hty start «end» hend hfloor') :=
  SimR.mono (fun _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ h => h.1)
    (handOverStored_simZ hcons l ls ty hty start «end» hend hfloor hfloor')

/-- The lexer with the batch in its state hands nothing over from a state whose batch has no
tokens. -/
theorem flushBatch_bind_right_empty {α β : Type} {P : WS floor low → XS floor low → Prop}
    {Q : α → β → WS floor low → XS floor low → Prop}
    {f : Lexer.WRustPort.LexM H m R E floor low α}
    {k : PUnit → Lexer.X1BatchInCore.LexM H m R E floor low β}
    (hP : ∀ s t, P s t → t.val.batch.len = 0) (hk : SimR Er P Q f (k ⟨⟩)) :
    SimR Er P Q f (Lexer.X1BatchInCore.flushBatch >>= k) := by
  unfold Lexer.X1BatchInCore.flushBatch
  rw [bind_assoc]
  refine getCore_bind_right fun s t h => ?_
  have h0 : (t.val.batch.len == 0) = true := by simp [hP s t h]
  rw [ite_eq_left h0, pure_bind]
  exact SimR.pre (fun s' t' h' => by obtain ⟨rfl, rfl⟩ := h'; exact h) hk

/-- The end of the input, which is not strict: the Rust port's batch is a fresh one. -/
theorem handOverEof_simZ (hcons : ConsumesAlike H m R E) (l ls : Nat) (location : Location) :
    ESim (H := H) (m := m) (R := R) (E := E) (floor := none) (low := low)
      (ErZ false)
      (fun s t => SRE l ls s t ∧ s.val.tokenContent = ByteArray.empty)
      (fun _ _ => SRE l ls) (Lexer.WRustPort.sinkEof location)
      (Lexer.X1BatchInCore.handOverEof location) := by
  unfold Lexer.WRustPort.sinkEof Lexer.X1BatchInCore.handOverEof
  refine getCore_bind_left fun s t h => ?_
  obtain ⟨⟨⟨hst, hl, hls⟩, hlen⟩, hempty⟩ := h
  refine flushBatch_bind_right_empty (fun s' t' h' => ?_) ?_
  · obtain ⟨-, rfl⟩ := h'
    rw [← hst.batch.len]
    exact hlen
  refine SimR.modifyGet_bind_right fun s' t' h' => ?_
  obtain ⟨hs', ht'⟩ := h'
  subst s' t'
  dsimp only
  refine getCore_bind_right fun s' t' h' => ?_
  obtain ⟨hs', ht'⟩ := h'
  subst s' t'
  have hc : t.val.tokenContent = ByteArray.empty := hst.tokenContent ▸ hempty
  refine SimR.of_bind_pure_left (SimR.bind (SimR.pre ?_ (handOver_sim' hcons l ls s.val.version
    _ _ ?_ _ _ _)) fun _ spent => ?_)
  · intro s' t' h'
    obtain ⟨hs', ht'⟩ := h'
    subst hs' ht'
    exact ⟨⟨⟨{ hst with batch := agree_of_len_zero hlen rfl, capacity := by rw [hlen]; decide },
      hl, hls⟩, hlen⟩, rfl, nofun⟩
  · simp only [hc, ByteArray.size_empty]
    refine Agree.pushLocated ?_ ?_ _ 0 0 location location _ _ _ _
    · exact agree_of_len_zero rfl rfl
    · rfl
  · exact SimR.post (fun _ _ _ _ h => h.2.1)
      (SimR.pre (fun _ _ h => ⟨h.1, nofun⟩) (storeSpent_right (strict := false) l ls _ _))

theorem handOverEof_sim (hcons : ConsumesAlike H m R E) (l ls : Nat) (location : Location) :
    LSim false (H := H) (m := m) (R := R) (E := E) (floor := none) (low := low)
      (fun s t => SRE l ls s t ∧ s.val.tokenContent = ByteArray.empty)
      (fun _ _ => SRE l ls) (Lexer.WRustPort.sinkEof location)
      (Lexer.X1BatchInCore.handOverEof location) :=
  SimR.mono (fun _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ h => h.1)
    (handOverEof_simZ hcons l ls location)

/-- The hand-over of the full batch that the loop of the normal state holds; both give it back
emptied. -/
theorem flushHeld_sim (hcons : ConsumesAlike H m R E) (l ls : Nat) (batch batch' : TokenBatch)
    (hb : Agree batch batch') (hbytes : batch.bytes = batch'.bytes) (origin : Nat)
    (hbatch hbatch') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRE l ls)
      (fun a b s t => Agree a.val b.val ∧ a.val.bytes = b.val.bytes ∧ a.val.len = 0 ∧
        SRE l ls s t)
      (Lexer.WRustPort.flushHeld batch origin hbatch)
      (Lexer.X1BatchInCore.flushHeld batch' origin hbatch') := by
  unfold Lexer.WRustPort.flushHeld Lexer.X1BatchInCore.flushHeld
  unfold Lexer.WRustPort.modifyBound
  refine SimR.modify_bind_left fun s t h => ?_
  obtain ⟨⟨hst, hl, hls⟩, hlen⟩ := h
  refine getCore_bind_left fun s₀ t₀ h₀ => ?_
  refine SimR.bind (SimR.pre ?_
    (handOver_simS hcons l ls s₀.val.version batch batch' hb _ _ _)) fun _ spent => ?_
  · intro s' t' h'
    obtain ⟨hs', ht'⟩ := h'
    obtain ⟨hs₀, ht₀⟩ := h₀
    subst s' t' s₀ t₀
    have ha := agree_of_len_zero (b := batch.clear s.val.offset) rfl (hst.batch.len ▸ hlen)
    exact ⟨⟨⟨{ hst with batch := ha, capacity := zero_lt_capacity }, hl, hls⟩, rfl⟩, rfl,
      fun _ => hbytes⟩
  · refine SimR.pure fun s' t' h' => ?_
    obtain ⟨hsre, -, rfl, -⟩ := h'
    exact ⟨agree_of_len_zero rfl rfl, hbytes, rfl, hsre⟩

end

end BSmtLib.Proofs.WRustPortX1BatchInCore

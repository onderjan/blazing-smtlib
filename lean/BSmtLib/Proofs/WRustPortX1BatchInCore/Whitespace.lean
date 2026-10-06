import BSmtLib.Proofs.WRustPortX1BatchInCore.Held

/-!
# The runs the loop of the normal state leaves for the steps, and the whitespace run

A symbol run that the slice ends inside goes to the stored path (`storeUnfinishedSymbolRun`),
and a whitespace run that the consumer takes is lexed by its own loop (`startWhitespaceFrom`),
which marks the line feeds it passes; both lexers do the same, with the batches the loops hold.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation (M runM)
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted)
open BSmtLib.Proofs.Lexer.Slice (get? runEnd)

/-- The two states correspond and their batches have no tokens. -/
abbrev SR0 {floor : Option Nat} {low : Nat} (s : WS floor low) (t : XS floor low) : Prop :=
  SR s t ∧ s.val.batch.len = 0

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} {strict : Bool}

omit [Consume H m R E] in
/-- From states with batches without tokens, with any line and line start of the Rust port. -/
theorem LSim.of_sre {α β : Type} {Q : α → β → WS floor low → XS floor low → Prop}
    {f : Lexer.WRustPort.LexM H m R E floor low α}
    {g : Lexer.X1BatchInCore.LexM H m R E floor low β}
    (h : ∀ l ls, LSim strict (SRE l ls) Q f g) : LSim strict SR0 Q f g :=
  SimR.intro fun s t hst => SimR.pre (fun _ _ h' => by
    obtain ⟨⟨h', hz⟩, rfl, rfl⟩ := h'
    exact ⟨sr_srl h', hz⟩) (h s.val.line s.val.lineStart)

omit [Consume H m R E] in
theorem markLineFeedAt_sim0 (position : Nat) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) SR0
      (fun _ _ => SR0) (Lexer.WRustPort.markLineFeedAt position)
      (Lexer.X1BatchInCore.markLineFeedAt position) := by
  unfold Lexer.WRustPort.markLineFeedAt Lexer.X1BatchInCore.markLineFeedAt
  exact modifyCore_sim _ _ fun _ _ h => ⟨{ h.1 with
    line := by simp [h.1.line]
    lineStart := by
      simp only [Lexer.WRustPort.LexerCore.offsetAt, Lexer.X1BatchInCore.LexerCore.offsetAt,
        h.1.offset, h.1.base] }, h.2⟩

omit [Consume H m R E] in
theorem modifyContent_sre (l ls : Nat) (f : ByteArray → ByteArray) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRE l ls)
      (fun _ _ => SRE l ls) (Lexer.WRustPort.modifyContent f)
      (Lexer.X1BatchInCore.modifyContent f) :=
  modifyCore_sim _ _ fun _ _ h =>
    ⟨⟨{ h.1.1 with tokenContent := congrArg f h.1.1.tokenContent }, h.1.2⟩, h.2⟩

omit [Consume H m R E] in
theorem extendContent_sre (l ls : Nat) (input : ByteSlice) (start stop : Nat) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRE l ls)
      (fun _ _ => SRE l ls) (Lexer.WRustPort.extendContent input start stop)
      (Lexer.X1BatchInCore.extendContent input start stop) := by
  unfold Lexer.WRustPort.extendContent Lexer.X1BatchInCore.extendContent
    Lexer.WRustPort.extendContentFrom Lexer.X1BatchInCore.extendContentFrom
  exact modifyContent_sre l ls _

omit [Consume H m R E] in
theorem extendContentFrom_sre (l ls : Nat) (bytes : ByteSlice) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRE l ls)
      (fun _ _ => SRE l ls) (Lexer.WRustPort.extendContentFrom bytes)
      (Lexer.X1BatchInCore.extendContentFrom bytes) := by
  unfold Lexer.WRustPort.extendContentFrom Lexer.X1BatchInCore.extendContentFrom
  exact modifyContent_sre l ls _

omit [Consume H m R E] in
theorem startToken_sre (l ls : Nat) (offset : Nat) (base position : Nat)
    (hframe : Lexer.WRustPort.Frame floor low offset)
    (hframe' : Lexer.X1BatchInCore.Frame floor low offset) :
    LSim strict (H := H) (m := m) (R := R) (E := E) (SRE l ls)
      (fun a b s t => a.val = b.val ∧ SRE l ls s t)
      (Lexer.WRustPort.startToken offset base position hframe)
      (Lexer.X1BatchInCore.startToken offset base position hframe') := by
  unfold Lexer.WRustPort.startToken Lexer.X1BatchInCore.startToken
  refine getCore_bind_P fun s₀ t₀ h₀ => ?_
  obtain ⟨⟨hst, hl, hls⟩, hz⟩ := h₀
  refine SimR.seq (P' := SRE l ls) (modifyCore_sim _ _ fun s t h => ?_) ?_
  · obtain ⟨⟨h, hl', hls'⟩, hz'⟩ := h
    exact ⟨⟨{ h with tokenStart := by simp only [hst.line, hst.lineStart], state := rfl }, hl',
      hls'⟩, hz'⟩
  refine SimR.seq (P' := SRE l ls) (modifyContent_sre l ls _) ?_
  exact SimR.pure fun s t h => ⟨by simp only [hst.line, hst.lineStart], h⟩

omit [Consume H m R E] in
theorem storeUnfinishedSymbolRun_sim (l ls : Nat) (input : ByteSlice) (entry : UInt8)
    (offset base index after runEndAt : Nat) (b b' : TokenBatch) (hb : HR b b')
    (hframe hframe' hindex hrun hbatch hbatch') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) (SRE l ls)
      (fun _ _ => SRLb strict l ls)
      (Lexer.WRustPort.storeUnfinishedSymbolRun input entry offset base index after runEndAt b
        hframe hindex hrun hbatch)
      (Lexer.X1BatchInCore.storeUnfinishedSymbolRun input entry offset base index after runEndAt
        b' hframe' hindex hrun hbatch') := by
  unfold Lexer.WRustPort.storeUnfinishedSymbolRun Lexer.X1BatchInCore.storeUnfinishedSymbolRun
  refine SimR.bind (startToken_sre l ls offset base index hframe hframe') fun a a' => ?_
  obtain ⟨a, ha⟩ := a
  obtain ⟨a', ha'⟩ := a'
  refine SimR.of_fact' (Er := ErS strict) fun (e : a = a') => ?_
  subst e
  dsimp only
  refine SimR.ite Iff.rfl (fun _ => ?_) fun _ => ?_ <;>
  exact SimR.seq (extendContent_sre l ls _ _ _)
    (SimR.pre (fun s t h => h.1) (leavePending_sim l ls _ _ _ _ _ _ _ hb _ _ _ _ _ _ _ _))

/-- What the whitespace run gives back: the index after it and the batches held by the loops,
with the states' batches without tokens; or nothing, where the run reaches the end of the slice
and the batches are put back into the states. -/
def WsQ (strict : Bool) {α β : Type} (val : α → Nat × TokenBatch) (val' : β → Nat × TokenBatch)
    (a : Option α) (b : Option β) (s : WS floor low) (t : XS floor low) : Prop :=
  match a, b with
  | none, none => SRb strict s t
  | some x, some y => (val x).1 = (val' y).1 ∧ HR (val x).2 (val' y).2 ∧ SR0 s t
  | _, _ => False

theorem startWhitespaceFrom_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice)
    (offset base index : Nat) (start : Location) :
    ∀ k (b b' : TokenBatch) («end» : Nat), input.size - «end» = k → HR b b' →
      ∀ hframe hframe' hstart hstart' hend hend' hrun hrun' hbatch hbatch',
      LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) SR0
        (WsQ strict (·.val) (·.val))
        (Lexer.WRustPort.startWhitespaceFrom input offset base index «end» start b hframe hstart
          hend hrun hbatch)
        (Lexer.X1BatchInCore.startWhitespaceFrom input offset base index «end» start b' hframe'
          hstart' hend' hrun' hbatch') := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro b b' e hk hb hframe hframe' hstart hstart' hend hend' hrun hrun' hbatch hbatch'
  rw [Lexer.WRustPort.startWhitespaceFrom, Lexer.X1BatchInCore.startWhitespaceFrom]
  dsimp only
  split_both
  · rename_i c h1 c' h2
    obtain rfl : c' = c := Option.some.inj (h2.symm.trans h1)
    have := Lexer.Slice.lt_size_of_get? h1
    have hle := Lexer.Slice.le_runEnd input e Lexer.RUN_NON_LF_WHITESPACE
    refine SimR.dite Iff.rfl (fun hnl _ => ?_) fun hnl _ => ?_
    · exact SimR.seq (markLineFeedAt_sim0 _) (ih _ (by omega) b b' _ rfl hb _ _ _ _ _ _ _ _ _ _)
    · refine LSim.of_sre fun l ls => SimR.bind (pushBorrowed_sim hcons l ls b b' hb _ _ _ _ _ _
        _ _ _ _ _ _ _) fun x y => SimR.pure fun s t h => ⟨rfl, h.1, h.2.1.1, h.2.2⟩
  · rename_i c h1 h2
    exact absurd (h1.symm.trans h2) (by simp)
  · rename_i h1 c h2
    exact absurd (h1.symm.trans h2) (by simp)
  · refine LSim.of_sre fun l ls => ?_
    exact SimR.seq (extendContent_sre l ls _ _ _) (SimR.seq (SimR.pre (fun s t h => h.1)
      (leavePending_sim l ls _ _ _ _ _ _ _ hb _ _ _ _ _ _ _ _))
      (SimR.pure fun s t h => ⟨h.1.1, h.2⟩))

theorem startWhitespace_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice)
    (offset base index : Nat) (b b' : TokenBatch) (hb : HR b b')
    (hrun hrun' hframe hframe' hindex hbatch hbatch') :
    LSim strict (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low) SR0
      (WsQ strict (·.val) (·.val))
      (Lexer.WRustPort.startWhitespace input offset base index b hrun hframe hindex hbatch)
      (Lexer.X1BatchInCore.startWhitespace input offset base index b' hrun' hframe' hindex
        hbatch') := by
  unfold Lexer.WRustPort.startWhitespace Lexer.X1BatchInCore.startWhitespace
  refine LSim.of_sre fun l ls => SimR.bind (startToken_sre l ls offset base index _ _)
    fun a a' => ?_
  obtain ⟨a, ha⟩ := a
  obtain ⟨a', ha'⟩ := a'
  refine SimR.of_fact' (Er := ErS strict) fun (e : a = a') => ?_
  subst e
  exact SimR.pre (fun s t h => ⟨h.1.1, h.2⟩)
    (startWhitespaceFrom_sim hcons input offset base index a _ b b' index rfl hb _ _ _ _ _ _ _ _
      _ _)

end

end BSmtLib.Proofs.WRustPortX1BatchInCore

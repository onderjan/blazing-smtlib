import BSmtLib.Proofs.WRustPortX1BatchInCore.Eof

/-!
# The calls on the lexer states

The calls (`lexSliceStep`, `lexEofStep`) run on the lexer state and the consumer, and are the
same code over the loops shown alike before (`lexSliceInner_sim`, `lexEofInner_sim`). Between
calls the two lexer states correspond and their batches have no tokens (`TopRel`); two actions on
the lexer states and the consumer are related by `ISim`. A call that fails leaves them so too.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted Failure Stop RecoveryState)
open BSmtLib.Proofs.Lexer.WRustPort (Ops)

/-- The two lexer states correspond and their batches have no tokens: the states between the
calls. -/
def TopRel (w x : Core) : Prop :=
  CoreRel w x ∧ w.batch.len = 0

theorem currentLocation_eq {w x : Core} (h : CoreRel w x) :
    w.currentLocation = x.currentLocation := by
  simp only [Lexer.WRustPort.LexerCore.currentLocation, Lexer.WRustPort.LexerCore.locationAt,
    Lexer.WRustPort.LexerCore.offsetAt, h.offset, h.base, h.line, h.lineStart]

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The lexer states are reset alike. -/
theorem reset_sim :
    ISim (H := H) (m := m) (fun w x => CoreRel w x) (fun _ _ => TopRel) Lexer.WRustPort.reset
      Lexer.WRustPort.reset := by
  unfold Lexer.WRustPort.reset
  refine ISim.modify _ _ fun w x h => ⟨?_, rfl⟩
  exact { h with
    version := h.initialVersion, state := rfl, discardedFrom := rfl, holding := rfl
    consumedDepth := rfl
    lexedDepth := rfl, recoveryState := rfl, tokenStart := rfl, offset := rfl, line := rfl
    tokenContent := by simp only [h.tokenContent], base := rfl, lineStart := rfl
    batch := agree_clear _ _ _ _, capacity := zero_lt_capacity }

theorem reset_sim' :
    ISim (H := H) (m := m) TopRel (fun _ _ => TopRel) Lexer.WRustPort.reset
      Lexer.WRustPort.reset :=
  ISim.mono (fun _ _ h => h.1) (fun _ _ _ _ h => h) reset_sim

/-- The bytes are skipped alike while recovering. -/
theorem skipSlice_sim (slice : ByteSlice) (skip : RecoveryState) :
    ISim (H := H) (m := m) TopRel (fun a b w x => a = b ∧ TopRel w x)
      (Lexer.WRustPort.skipSlice slice skip) (Lexer.WRustPort.skipSlice slice skip) := by
  unfold Lexer.WRustPort.skipSlice
  refine ISim.get_bind fun w x h => ?_
  obtain ⟨hc, hz⟩ := h
  refine ISim.ite (by rw [hc.consumedDepth]) (fun _ => ISim.pure fun _ _ h => ⟨rfl, h⟩)
    fun _ => ?_
  dsimp only
  generalize (if (skip == RecoveryState.boundary) = true then RecoveryState.plain else skip) = sk
  have e : Lexer.WRustPort.skipBytes slice (x.version == .v2_0) x.offset 0
      { skip := sk, depth := x.consumedDepth, line := x.line, lineStart := x.lineStart } =
      Lexer.WRustPort.skipBytes slice (w.version == .v2_0) w.offset 0
        { skip := sk, depth := w.consumedDepth, line := w.line, lineStart := w.lineStart } := by
    rw [hc.version, hc.offset, hc.consumedDepth, hc.line, hc.lineStart]
  rw [e]
  split
  · refine ISim.seq (ISim.set _ _ fun _ _ _ => ?_) (ISim.pure fun _ _ h => ⟨rfl, h⟩)
    exact ⟨{ hc with
      offset := (by simp only [hc.offset]), consumedDepth := rfl, line := rfl
      lineStart := rfl }, hz⟩
  · refine ISim.seq (ISim.set _ _ fun _ _ _ => ?_) (ISim.pure fun _ _ h => ⟨rfl, h⟩)
    exact ⟨{ hc with
      offset := (by simp only [hc.offset]), consumedDepth := rfl, line := rfl
      lineStart := rfl, recoveryState := rfl }, hz⟩

end

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H R E]
  [∀ batch, ConsumeFrom H (BatchCursor batch) m]
  {o₁ o₂ : Ops H m R E}
  {LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop}

/-- Equal results, from lexer states related by `TopRel` to lexer states related by it. -/
abbrev TopQ {α : Type} (a b : α) (w x : Core) : Prop :=
  a = b ∧ TopRel w x

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem executeStep_sim {step step' : Lexer.WRustPort.InnerM H m (Except (Failure E)
      (ControlFlow R))}
    (hs : ISim TopRel TopQ step step') :
    ISim TopRel TopQ (Lexer.WRustPort.executeStep step) (Lexer.WRustPort.executeStep step') := by
  unfold Lexer.WRustPort.executeStep
  refine ISim.bind hs fun a b => ISim.intro fun w x h => ?_
  obtain ⟨rfl, ht⟩ := h
  have hpre : ∀ w' x', w' = w ∧ x' = x → TopRel w' x' := fun _ _ h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ht
  rcases a with f | _ | r
  · exact ISim.pure fun w' x' h => ⟨rfl, hpre w' x' h⟩
  · exact ISim.pure fun w' x' h => ⟨rfl, hpre w' x' h⟩
  · refine ISim.get_bind fun w' x' h => ISim.pure fun _ _ h' => ?_
    obtain ⟨rfl, rfl⟩ := h'
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by rw [currentLocation_eq ht.1], ht⟩

omit [Consume H R E] [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem fail_sim (abandon : Location → StateT H m Unit) (failure : Failure E) (atEnd : Bool) :
    ISim TopRel TopQ (Lexer.WRustPort.fail abandon failure atEnd)
      (Lexer.WRustPort.fail abandon failure atEnd) := by
  unfold Lexer.WRustPort.fail
  refine ISim.get_bind fun w x h => ?_
  refine ISim.ite (by rw [h.1.recovers]) (fun _ => ISim.pure fun _ _ h => ⟨rfl, h⟩) fun _ => ?_
  dsimp only
  refine ISim.seq (P' := TopRel)
    (ISim.modify _ _ fun w x h => ⟨{ h.1 with holding := rfl }, h.2⟩) ?_
  refine ISim.seq (P' := TopRel) (ISim.modify _ _ fun w x h => ⟨coreRel_resumeAt h.1 _ _, rfl⟩) ?_
  refine ISim.bind (ISim.lift _) fun _ _ => ?_
  refine ISim.seq (P' := TopRel) (ISim.modify _ _ fun w x h => ?_) (ISim.pure fun _ _ h => ⟨rfl, h⟩)
  exact ⟨{ h.2.1 with recoveryState := rfl }, h.2.2⟩

omit [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexSliceInner_isim (ho : OpsSim o₁ o₂ LRel) (slice : ByteSlice) :
    ISim TopRel TopQ (Lexer.WRustPort.lexSliceInner (ops := o₁) (H := H) (m := m) (R := R) (E := E)
      slice) (Lexer.WRustPort.lexSliceInner (ops := o₂) slice) := fun w x h =>
  Couple.mono (fun _ _ hab => ⟨hab.1, hab.2.1, hab.2.2⟩) (lexSliceInner_sim ho slice w x h.1)

omit [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexEofInner_isim (ho : OpsSim o₁ o₂ LRel) :
    ISim TopRel TopQ (Lexer.WRustPort.lexEofInner (ops := o₁) (H := H) (m := m) (R := R) (E := E))
      (Lexer.WRustPort.lexEofInner (ops := o₂)) := fun w x h =>
  Couple.mono (fun _ _ hab => ⟨hab.1, hab.2.1, hab.2.2⟩) (lexEofInner_sim ho w x h.1 h.2)

set_option hygiene false in
/-- The lexing of the slice after the skipping, in a call. The names are those of
`lexSliceStep_sim`. -/
local macro "slice_tail" : tactic => `(tactic| (
  refine ISim.bind (lexSliceInner_isim ho _) fun a b => ISim.intro fun w₂ x₂ h₂ => ?_
  obtain ⟨rfl, ht⟩ := h₂
  have hpre : ∀ w' x', w' = w₂ ∧ x' = x₂ → TopRel w' x' := fun _ _ h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ht
  rcases a with f | held
  · exact ISim.bind (ISim.mono hpre (fun _ _ _ _ h => h) (fail_sim abandon f false))
      fun _ _ => ISim.pure fun _ _ hh => ⟨by rw [hh.1], hh.2⟩
  · exact ISim.mono hpre (fun _ _ _ _ h => h) (ISim.pure fun w' x' h => ⟨rfl, h⟩)))

omit [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexSliceStep_sim (ho : OpsSim o₁ o₂ LRel) (abandon recover : Location → StateT H m Unit)
    (slice : ByteSlice) :
    ISim TopRel TopQ (Lexer.WRustPort.lexSliceStep (ops := o₁) (R := R) (E := E) abandon recover
      slice) (Lexer.WRustPort.lexSliceStep (ops := o₂) abandon recover slice) := by
  unfold Lexer.WRustPort.lexSliceStep
  refine ISim.get_bind fun w x h => ?_
  refine ISim.ite (by rw [h.1.discardedFrom]) (fun _ => ISim.pure fun _ _ h => ⟨rfl, h⟩)
    fun _ => ?_
  dsimp only
  refine ISim.get_bind fun w x h => ?_
  rw [h.1.recoveryState]
  rcases x.recoveryState with _ | skip
  · slice_tail
  · refine ISim.ite Iff.rfl (fun _ => ISim.pure fun _ _ h => ⟨rfl, h⟩) fun _ => ?_
    refine ISim.bind (skipSlice_sim slice _) fun a b => ISim.intro fun w x h => ?_
    obtain ⟨rfl, ht⟩ := h
    rcases a with _ | skipped
    · exact ISim.pure fun _ _ h => ⟨rfl, by obtain ⟨rfl, rfl⟩ := h; exact ht⟩
    · refine ISim.mono (P := TopRel) (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact ht)
        (fun _ _ _ _ h => h) ?_
      refine ISim.seq (P' := TopRel) (ISim.modify _ _ fun w x h => ?_) ?_
      · exact ⟨{ h.1 with recoveryState := rfl, lexedDepth := h.1.consumedDepth }, h.2⟩
      refine ISim.get_bind fun w x h => ?_
      rw [currentLocation_eq h.1]
      refine ISim.bind (ISim.lift _) fun _ _ => ISim.intro fun w' x' h' => ?_
      refine ISim.mono (P := TopRel) (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact h'.2)
        (fun _ _ _ _ h => h) ?_
      slice_tail

set_option hygiene false in
/-- The lexing of the end of the input after the recovery, in a call. The names are those of
`lexEofStep_sim`. -/
local macro "eof_tail" : tactic => `(tactic| (
  refine ISim.bind (executeStep_sim (lexEofInner_isim ho)) fun a b =>
    ISim.intro fun w₂ x₂ h₂ => ?_
  obtain ⟨rfl, ht⟩ := h₂
  have hpre : ∀ w' x', w' = w₂ ∧ x' = x₂ → TopRel w' x' := fun _ _ h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ht
  refine ISim.mono hpre (fun _ _ _ _ h => h) ?_
  rcases a with f | flow
  · refine ISim.ite Iff.rfl (fun _ => ?_) fun _ => ?_
    · exact ISim.seq reset_sim' (ISim.pure fun _ _ hh => ⟨rfl, hh⟩)
    · exact ISim.bind (fail_sim abandon f true)
        fun _ _ => ISim.pure fun _ _ hh => ⟨by rw [hh.1], hh.2⟩
  · exact ISim.seq reset_sim' (ISim.pure fun _ _ hh => ⟨rfl, hh⟩)))

omit [∀ batch, ConsumeFrom H (BatchCursor batch) m] in
theorem lexEofStep_sim (ho : OpsSim o₁ o₂ LRel) (abandon recover : Location → StateT H m Unit) :
    ISim TopRel TopQ (Lexer.WRustPort.lexEofStep (ops := o₁) (R := R) (E := E) abandon recover)
      (Lexer.WRustPort.lexEofStep (ops := o₂) abandon recover) := by
  unfold Lexer.WRustPort.lexEofStep
  refine ISim.get_bind fun w x h => ?_
  rw [h.1.recoveryState]
  generalize x.recoveryState.isSome = recovered
  refine ISim.ite Iff.rfl (fun _ => ?_) fun _ => by eof_tail
  refine ISim.seq (P' := TopRel) (ISim.modify _ _ fun w x h => ?_) ?_
  · exact ⟨{ h.1 with recoveryState := rfl }, h.2⟩
  refine ISim.get_bind fun w x h => ?_
  rw [currentLocation_eq h.1]
  refine ISim.bind (ISim.lift _) fun _ _ => ISim.intro fun w' x' h' => ?_
  refine ISim.mono (P := TopRel) (fun _ _ h => by obtain ⟨rfl, rfl⟩ := h; exact h'.2)
    (fun _ _ _ _ h => h) ?_
  eof_tail

end

end BSmtLib.Proofs.WRustPortX1BatchInCore

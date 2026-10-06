import BSmtLib.Proofs.WRustPortX1BatchInCore.Eof

/-!
# The calls of the lexers

The calls of the two lexers (`lexSliceStep`, `lexEofStep`) run on the lexer state and the
consumer, and are the same code over the loops shown alike before (`lexSliceInner_sim`,
`lexEofInner_sim`). Between calls the two lexer states correspond and their batches have no
tokens (`TopRel`); two actions on the lexer states and the consumer are related by `ISim`.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation (M runM)
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted Failure Stop RecoveryState)

/-- The two lexer states correspond and their batches have no tokens: the states between the
calls of the lexers. -/
def TopRel (w : WCore) (x : XCore) : Prop :=
  CoreRel w x ∧ w.batch.len = 0

section

variable {H : Type} {m : Type → Type} [Monad m] [LawfulMonad m] {α β γ δ : Type}

/-- The action `f` of the Rust port on its lexer state and the consumer and the action `g` of
the other lexer, run from lexer states related by `P` and the same consumer state, are the
projections of one computation of results and lexer states related by `Q`. -/
def ISim (P : WCore → XCore → Prop) (Q : α → β → WCore → XCore → Prop)
    (f : StateT WCore (StateT H m) α) (g : StateT XCore (StateT H m) β) : Prop :=
  ∀ w x, P w x → Couple (fun a b => Q a.1 b.1 a.2 b.2) (f.run w) (g.run x)

/-- Mapped actions. -/
theorem Couple.map {Rel : α → β → Prop} {Rel' : γ → δ → Prop} {a : StateT H m α}
    {b : StateT H m β} (f : α → γ) (g : β → δ) (h : Couple Rel a b)
    (hfg : ∀ x y, Rel x y → Rel' (f x) (g y)) : Couple Rel' (f <$> a) (g <$> b) := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact Couple.bind h fun x y hxy => Couple.pure (hfg x y hxy)

variable {P : WCore → XCore → Prop}

theorem ISim.pure {Q : α → β → WCore → XCore → Prop} {a : α} {b : β}
    (hq : ∀ w x, P w x → Q a b w x) :
    ISim (H := H) (m := m) P Q (Pure.pure a) (Pure.pure b) := fun w x h => by
  simp only [StateT.run_pure]
  exact Couple.pure (hq w x h)

theorem ISim.bind {Q : α → β → WCore → XCore → Prop} {Q₂ : γ → δ → WCore → XCore → Prop}
    {f : StateT WCore (StateT H m) α} {g : StateT XCore (StateT H m) β}
    {k : α → StateT WCore (StateT H m) γ} {k' : β → StateT XCore (StateT H m) δ}
    (hf : ISim P Q f g) (hk : ∀ a b, ISim (Q a b) Q₂ (k a) (k' b)) :
    ISim P Q₂ (f >>= k) (g >>= k') := fun w x h => by
  simp only [StateT.run_bind]
  exact Couple.bind (hf w x h) fun a b hab => hk a.1 b.1 a.2 b.2 hab

theorem ISim.seq {P' : WCore → XCore → Prop} {Q₂ : γ → δ → WCore → XCore → Prop}
    {f : StateT WCore (StateT H m) PUnit} {g : StateT XCore (StateT H m) PUnit}
    {k : StateT WCore (StateT H m) γ} {k' : StateT XCore (StateT H m) δ}
    (hf : ISim P (fun _ _ => P') f g) (hk : ISim P' Q₂ k k') :
    ISim P Q₂ (f >>= fun _ => k) (g >>= fun _ => k') :=
  ISim.bind hf fun _ _ => hk

theorem ISim.get :
    ISim (H := H) (m := m) P (fun a b w x => P w x ∧ a = w ∧ b = x) (getThe WCore)
      (getThe XCore) := fun w x h => by
  show Couple _ (Pure.pure (w, w)) (Pure.pure (x, x))
  exact Couple.pure ⟨h, rfl, rfl⟩

/-- A step after reading the two lexer states, which keeps the precondition. -/
theorem ISim.get_bind {Q : α → β → WCore → XCore → Prop}
    {k : WCore → StateT WCore (StateT H m) α} {k' : XCore → StateT XCore (StateT H m) β}
    (hk : ∀ w x, P w x → ISim P Q (k w) (k' x)) :
    ISim P Q (getThe WCore >>= k) (getThe XCore >>= k') :=
  ISim.bind ISim.get fun w x => fun w' x' h => by
    obtain ⟨hP, rfl, rfl⟩ := h
    exact hk w x hP w x hP

theorem ISim.modify {Q : Unit → Unit → WCore → XCore → Prop} (f : WCore → WCore)
    (g : XCore → XCore) (h : ∀ w x, P w x → Q () () (f w) (g x)) :
    ISim (H := H) (m := m) P Q (modifyThe WCore f) (modifyThe XCore g) := fun w x hP => by
  show Couple _ (Pure.pure (PUnit.unit, f w)) (Pure.pure (PUnit.unit, g x))
  exact Couple.pure (h w x hP)

/-- The same action of the consumer. -/
theorem ISim.lift (a : StateT H m γ) :
    ISim (H := H) (m := m) P (fun r r' w x => r = r' ∧ P w x) (monadLift a) (monadLift a) :=
  fun w x h => by
    show Couple _ (a >>= fun r => Pure.pure (r, w)) (a >>= fun r => Pure.pure (r, x))
    exact Couple.bind (Couple.refl a) fun r r' e => Couple.pure ⟨e, h⟩

omit [LawfulMonad m] in
theorem ISim.ite {Q : α → β → WCore → XCore → Prop} {c : Prop} [Decidable c]
    {f f' : StateT WCore (StateT H m) α} {g g' : StateT XCore (StateT H m) β}
    (hf : c → ISim P Q f g) (hg : ¬c → ISim P Q f' g') :
    ISim P Q (if c then f else f') (if c then g else g') := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]
    exact hf h
  · rw [ite_eq_right h, ite_eq_right h]
    exact hg h

theorem ISim.mono {P' : WCore → XCore → Prop} {Q Q' : α → β → WCore → XCore → Prop}
    {f : StateT WCore (StateT H m) α} {g : StateT XCore (StateT H m) β}
    (hP : ∀ w x, P' w x → P w x) (hQ : ∀ a b w x, Q a b w x → Q' a b w x)
    (h : ISim P Q f g) : ISim P' Q' f g := fun w x hw =>
  Couple.mono (fun _ _ hab => hQ _ _ _ _ hab) (h w x (hP w x hw))

omit [LawfulMonad m] in
theorem ISim.intro {Q : α → β → WCore → XCore → Prop}
    {f : StateT WCore (StateT H m) α} {g : StateT XCore (StateT H m) β}
    (h : ∀ w x, P w x → ISim (fun w' x' => w' = w ∧ x' = x) Q f g) : ISim P Q f g :=
  fun w x hP => h w x hP w x ⟨rfl, rfl⟩


/-! ## The helpers of the calls -/

theorem countLineFeeds_loop_eq (bytes : ByteSlice) :
    ∀ k i count (afterLast : Option Nat), bytes.size - i = k →
      Lexer.WRustPort.countLineFeeds.loop bytes i count afterLast =
        Lexer.X1BatchInCore.countLineFeeds.loop bytes i count afterLast := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro i count afterLast hk
  rw [Lexer.WRustPort.countLineFeeds.loop, Lexer.X1BatchInCore.countLineFeeds.loop]
  split
  · split
    · exact ih _ (by omega) _ _ _ rfl
    · exact ih _ (by omega) _ _ _ rfl
  · rfl

theorem countLineFeeds_eq (bytes : ByteSlice) :
    Lexer.WRustPort.countLineFeeds bytes = Lexer.X1BatchInCore.countLineFeeds bytes :=
  countLineFeeds_loop_eq bytes _ 0 0 none rfl

/-- The skipping states of the two lexers are the same. -/
def SkipEq (a : Lexer.WRustPort.Skipping) (b : Lexer.X1BatchInCore.Skipping) : Prop :=
  a.skip = b.skip ∧ a.depth = b.depth ∧ a.line = b.line ∧ a.lineStart = b.lineStart

/-- What a byte makes of the skipping states of the two lexers is the same. -/
def SumRel :
    (Nat × Lexer.WRustPort.Skipping) ⊕ Lexer.WRustPort.Skipping →
      (Nat × Lexer.X1BatchInCore.Skipping) ⊕ Lexer.X1BatchInCore.Skipping → Prop
  | .inl (p, a), .inl (q, b) => p = q ∧ SkipEq a b
  | .inr a, .inr b => SkipEq a b
  | _, _ => False

/-- What skipping gives back is the same. -/
def SkipRes (a : Option Nat × Lexer.WRustPort.Skipping)
    (b : Option Nat × Lexer.X1BatchInCore.Skipping) : Prop :=
  a.1 = b.1 ∧ SkipEq a.2 b.2

/-- The end of a step of skipping, from what the byte makes of the skipping states. -/
theorem skipCont_rel (bytes : ByteSlice) (legacy : Bool) (offset index : Nat) (c : UInt8)
    (sW : (Nat × Lexer.WRustPort.Skipping) ⊕ Lexer.WRustPort.Skipping)
    (sX : (Nat × Lexer.X1BatchInCore.Skipping) ⊕ Lexer.X1BatchInCore.Skipping)
    (h : SumRel sW sX)
    (hrec : ∀ a b, SkipEq a b →
      SkipRes (Lexer.WRustPort.skipBytes bytes legacy offset (index + 1) a)
        (Lexer.X1BatchInCore.skipBytes bytes legacy offset (index + 1) b)) :
    SkipRes
      (match (generalizing := false) sW with
        | .inl (position, skipping) => (some position, skipping)
        | .inr skipping =>
          let skipping := if c == 10 then
              { skipping with line := skipping.line + 1, lineStart := offset + index + 1 }
            else skipping
          Lexer.WRustPort.skipBytes bytes legacy offset (index + 1) skipping)
      (match (generalizing := false) sX with
        | .inl (position, skipping) => (some position, skipping)
        | .inr skipping =>
          let skipping := if c == 10 then
              { skipping with line := skipping.line + 1, lineStart := offset + index + 1 }
            else skipping
          Lexer.X1BatchInCore.skipBytes bytes legacy offset (index + 1) skipping) := by
  match sW, sX, h with
  | .inl (p, a), .inl (q, b), h => exact ⟨congrArg some h.1, h.2⟩
  | .inr a, .inr b, h =>
    dsimp only
    apply hrec
    obtain ⟨e1, e2, e3, e4⟩ := h
    split
    · exact ⟨e1, e2, by rw [e3], rfl⟩
    · exact ⟨e1, e2, e3, e4⟩

/-- Splits the conditions of a step of skipping, which are the same in the two lexers. -/
local macro "skip_chain" : tactic => `(tactic| (
  repeat (first
    | exact ⟨rfl, rfl, rfl, rfl⟩
    | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    | split)))

theorem skipBytes_eq (bytes : ByteSlice) (legacy : Bool) (offset : Nat) :
    ∀ k index (a : Lexer.WRustPort.Skipping) (b : Lexer.X1BatchInCore.Skipping),
      bytes.size - index = k → SkipEq a b →
      SkipRes (Lexer.WRustPort.skipBytes bytes legacy offset index a)
        (Lexer.X1BatchInCore.skipBytes bytes legacy offset index b) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro index a b hk hab
  obtain ⟨skip, depth, line, lineStart⟩ := a
  obtain ⟨skip', depth', line', lineStart'⟩ := b
  obtain ⟨e1, e2, e3, e4⟩ := hab
  simp only at e1 e2 e3 e4
  subst e1 e2 e3 e4
  rw [Lexer.WRustPort.skipBytes, Lexer.X1BatchInCore.skipBytes]
  by_cases hi : index < bytes.size
  · rw [dite_eq_left_of_eq_true (eq_true hi), dite_eq_left_of_eq_true (eq_true hi)]
    dsimp only
    refine skipCont_rel bytes legacy offset index _ _ _ ?_
      fun a b hab => ih _ (by omega) _ a b rfl hab
    cases skip <;> dsimp only <;> skip_chain
  · rw [dite_eq_right_of_eq_false (eq_false hi), dite_eq_right_of_eq_false (eq_false hi)]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

omit [LawfulMonad m] in
theorem ISim.ite' {Q : α → β → WCore → XCore → Prop} {c c' : Prop} [Decidable c] [Decidable c']
    {f f' : StateT WCore (StateT H m) α} {g g' : StateT XCore (StateT H m) β} (hc : c ↔ c')
    (hf : c → ISim P Q f g) (hg : ¬c → ISim P Q f' g') :
    ISim P Q (if c then f else f') (if c' then g else g') := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left (hc.mp h)]
    exact hf h
  · rw [ite_eq_right h, ite_eq_right (mt hc.mpr h)]
    exact hg h

/-! ## The lexer states -/

theorem currentLocation_eq {w : WCore} {x : XCore} (h : CoreRel w x) :
    w.currentLocation = x.currentLocation := by
  simp only [Lexer.WRustPort.LexerCore.currentLocation,
    Lexer.X1BatchInCore.LexerCore.currentLocation, Lexer.WRustPort.LexerCore.locationAt,
    Lexer.X1BatchInCore.LexerCore.locationAt, Lexer.WRustPort.LexerCore.offsetAt,
    Lexer.X1BatchInCore.LexerCore.offsetAt, h.offset, h.base, h.line, h.lineStart]

/-- The lexer states are reset alike. -/
theorem reset_sim :
    ISim (H := H) (m := m) (fun w x => CoreRel w x) (fun _ _ => TopRel) Lexer.WRustPort.reset
      Lexer.X1BatchInCore.reset := by
  unfold Lexer.WRustPort.reset Lexer.X1BatchInCore.reset
  refine ISim.modify _ _ fun w x h => ⟨?_, rfl⟩
  exact { h with
    version := h.initialVersion, state := rfl, discard := rfl, consumedDepth := rfl
    lexedDepth := rfl, recoveryState := rfl, tokenStart := rfl, tokenContent := rfl, offset := rfl
    line := rfl, base := rfl, lineStart := rfl, batch := agree_clear _ _ _ _
    capacity := zero_lt_capacity }

/-- The bytes are discarded alike. -/
theorem discardBytes_sim (bytes : ByteSlice) :
    ISim (H := H) (m := m) TopRel (fun _ _ => TopRel) (Lexer.WRustPort.discardBytes bytes)
      (Lexer.X1BatchInCore.discardBytes bytes) := by
  unfold Lexer.WRustPort.discardBytes Lexer.X1BatchInCore.discardBytes
  refine ISim.modify _ _ fun w x h => ?_
  obtain ⟨⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, hv, hb, hcap⟩, hz⟩ := h
  have e := countLineFeeds_eq bytes
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  all_goals
    dsimp only
    rw [e]
    split <;> (try dsimp only) <;> first | assumption | (simp only [*]; done)

theorem ISim.set {Q : Unit → Unit → WCore → XCore → Prop} (w' : WCore) (x' : XCore)
    (h : ∀ w x, P w x → Q () () w' x') :
    ISim (H := H) (m := m) P Q (MonadStateOf.set w' : StateT WCore (StateT H m) PUnit)
      (MonadStateOf.set x' : StateT XCore (StateT H m) PUnit) := fun w x hP => by
  show Couple _ (Pure.pure (PUnit.unit, w')) (Pure.pure (PUnit.unit, x'))
  exact Couple.pure (h w x hP)

/-- `skipBytes_eq` with the arguments of the other lexer given by equations. -/
theorem skipBytes_eq' (bytes : ByteSlice) (legacy legacy' : Bool) (el : legacy = legacy')
    (offset offset' : Nat) (eo : offset = offset') (a : Lexer.WRustPort.Skipping)
    (b : Lexer.X1BatchInCore.Skipping) (hab : SkipEq a b) :
    SkipRes (Lexer.WRustPort.skipBytes bytes legacy offset 0 a)
      (Lexer.X1BatchInCore.skipBytes bytes legacy' offset' 0 b) := by
  subst el eo
  exact skipBytes_eq bytes legacy offset _ 0 a b rfl hab

/-- The bytes are skipped alike while recovering. -/
theorem skipSlice_sim (slice : ByteSlice) (skip : RecoveryState) :
    ISim (H := H) (m := m) TopRel (fun a b w x => a = b ∧ TopRel w x)
      (Lexer.WRustPort.skipSlice slice skip) (Lexer.X1BatchInCore.skipSlice slice skip) := by
  unfold Lexer.WRustPort.skipSlice Lexer.X1BatchInCore.skipSlice
  refine ISim.get_bind fun w x h => ?_
  obtain ⟨hc, hz⟩ := h
  refine ISim.ite' (by rw [hc.consumedDepth]) (fun _ => ISim.pure fun _ _ h => ⟨rfl, h⟩)
    fun _ => ?_
  dsimp only
  generalize (if (skip == RecoveryState.boundary) = true then RecoveryState.plain else skip) = sk
  have hs := skipBytes_eq' slice (w.version == .v2_0) (x.version == .v2_0) (by rw [hc.version])
    w.offset x.offset hc.offset
    { skip := sk, depth := w.consumedDepth, line := w.line, lineStart := w.lineStart }
    { skip := sk, depth := x.consumedDepth, line := x.line, lineStart := x.lineStart }
    ⟨rfl, hc.consumedDepth, hc.line, hc.lineStart⟩
  split <;> split <;>
    (first
      | (rename_i _ _ _ h1 _ _ _ h2; rw [h1, h2] at hs)
      | (rename_i _ _ _ h1 _ _ h2; rw [h1, h2] at hs)
      | (rename_i _ _ h1 _ _ _ h2; rw [h1, h2] at hs)
      | (rename_i _ _ h1 _ _ h2; rw [h1, h2] at hs)) <;>
    obtain ⟨hp, hsk⟩ := hs <;>
    (try dsimp only at hp hsk) <;> (try simp only [reduceCtorEq, Option.some.injEq] at hp)
  · subst hp
    obtain ⟨e1, e2, e3, e4⟩ := hsk
    refine ISim.seq (ISim.set _ _ fun _ _ _ => ?_) (ISim.pure fun _ _ h => ⟨rfl, h⟩)
    exact ⟨{ hc with
      offset := by simp only [hc.offset], consumedDepth := e2, line := e3, lineStart := e4 }, hz⟩
  · obtain ⟨e1, e2, e3, e4⟩ := hsk
    refine ISim.seq (ISim.set _ _ fun _ _ _ => ?_) (ISim.pure fun _ _ h => ⟨rfl, h⟩)
    exact ⟨{ hc with
      offset := by simp only [hc.offset], consumedDepth := e2, line := e3, lineStart := e4
      recoveryState := by simp only [e1] }, hz⟩

end

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]

/-- Equal results, from lexer states related by `TopRel` to lexer states related by it. -/
abbrev TopQ {α : Type} (a b : α) (w : WCore) (x : XCore) : Prop :=
  a = b ∧ TopRel w x

omit [Consume H m R E] in
theorem executeStep_sim {step : StateT WCore (StateT H m) (Except (Failure E) (ControlFlow R))}
    {step' : StateT XCore (StateT H m) (Except (Failure E) (ControlFlow R))}
    (hs : ISim TopRel TopQ step step') :
    ISim TopRel TopQ (Lexer.WRustPort.executeStep step)
      (Lexer.X1BatchInCore.executeStep step') := by
  unfold Lexer.WRustPort.executeStep Lexer.X1BatchInCore.executeStep
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

theorem failCall_sim (abandon : Location → StateT H m Unit) (failure : Failure E)
    (atEnd : Bool) :
    ISim TopRel TopQ (Lexer.WRustPort.fail abandon failure atEnd)
      (Lexer.X1BatchInCore.failCall abandon failure atEnd) := by
  unfold Lexer.WRustPort.fail Lexer.X1BatchInCore.failCall
  refine ISim.get_bind fun w x h => ?_
  refine ISim.ite' (by rw [h.1.recovers]) (fun _ => ISim.pure fun _ _ h => ⟨rfl, h⟩) fun _ => ?_
  dsimp only
  refine ISim.seq (P' := TopRel) (ISim.modify _ _ fun w x h => ⟨coreRel_resumeAt h.1 _ _, rfl⟩) ?_
  refine ISim.bind (ISim.lift _) fun _ _ => ?_
  refine ISim.seq (P' := TopRel) (ISim.modify _ _ fun w x h => ?_) (ISim.pure fun _ _ h => ⟨rfl, h⟩)
  exact ⟨{ h.2.1 with recoveryState := rfl }, h.2.2⟩

theorem lexSliceInner_isim (hcons : ConsumesAlike H m R E) (slice : ByteSlice) :
    ISim TopRel TopQ (Lexer.WRustPort.lexSliceInner (H := H) (m := m) (R := R) (E := E) slice)
      (Lexer.X1BatchInCore.lexSliceInner slice) := fun w x h =>
  Couple.mono (fun _ _ hab => ⟨hab.1, hab.2.1, hab.2.2⟩) (lexSliceInner_sim hcons slice w x h.1)

theorem lexEofInner_isim (hcons : ConsumesAlike H m R E) :
    ISim TopRel TopQ (Lexer.WRustPort.lexEofInner (H := H) (m := m) (R := R) (E := E))
      Lexer.X1BatchInCore.lexEofInner := fun w x h =>
  Couple.mono (fun _ _ hab => ⟨hab.1, hab.2.1, hab.2.2⟩) (lexEofInner_sim hcons w x h.1 h.2)

set_option hygiene false in
/-- The lexing of the slice after the skipping, in a call of the lexers. The names are those of
`lexSliceStep_sim`. -/
local macro "slice_tail" : tactic => `(tactic| (
  refine ISim.get_bind fun w₁ x₁ h₁ => ?_
  try dsimp only
  refine ISim.bind (executeStep_sim (lexSliceInner_isim hcons _)) fun a b =>
    ISim.intro fun w₂ x₂ h₂ => ?_
  obtain ⟨rfl, ht⟩ := h₂
  have hpre : ∀ w' x', w' = w₂ ∧ x' = x₂ → TopRel w' x' := fun _ _ h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ht
  rcases a with f | _ | located
  · exact ISim.bind (ISim.mono hpre (fun _ _ _ _ h => h) (failCall_sim abandon f false))
      fun _ _ => ISim.pure fun _ _ hh => ⟨by rw [hh.1], hh.2⟩
  · exact ISim.pure fun w' x' h => ⟨rfl, hpre w' x' h⟩
  · refine ISim.mono hpre (fun _ _ _ _ h => h) ?_
    refine ISim.seq (P' := TopRel) (ISim.modify _ _ fun w x h => ⟨{ h.1 with discard := rfl },
      h.2⟩) ?_
    rw [← h₁.1.offset]
    exact ISim.bind (discardBytes_sim _) fun _ _ => ISim.pure fun _ _ hh => ⟨rfl, hh⟩))

theorem lexSliceStep_sim (hcons : ConsumesAlike H m R E)
    (abandon recover : Location → StateT H m Unit)
    (slice : ByteSlice) :
    ISim TopRel TopQ (Lexer.WRustPort.lexSliceStep (R := R) (E := E) abandon recover slice)
      (Lexer.X1BatchInCore.lexSliceStep abandon recover slice) := by
  unfold Lexer.WRustPort.lexSliceStep Lexer.X1BatchInCore.lexSliceStep
  refine ISim.get_bind fun w x h => ?_
  refine ISim.ite' (by rw [h.1.discard]) (fun _ => ISim.seq (discardBytes_sim slice)
    (ISim.pure fun _ _ h => ⟨rfl, h⟩)) fun _ => ?_
  dsimp only
  refine ISim.get_bind fun w x h => ?_
  rw [h.1.recoveryState]
  rcases x.recoveryState with _ | skip
  · slice_tail
  · refine ISim.ite (fun _ => ISim.pure fun _ _ h => ⟨rfl, h⟩) fun _ => ?_
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

theorem reset_sim' :
    ISim (H := H) (m := m) TopRel (fun _ _ => TopRel) Lexer.WRustPort.reset
      Lexer.X1BatchInCore.reset :=
  ISim.mono (fun _ _ h => h.1) (fun _ _ _ _ h => h) reset_sim

set_option hygiene false in
/-- The lexing of the end of the input after the recovery, in a call of the lexers. The names
are those of `lexEofStep_sim`. -/
local macro "eof_tail" : tactic => `(tactic| (
  refine ISim.bind (executeStep_sim (lexEofInner_isim hcons)) fun a b =>
    ISim.intro fun w₂ x₂ h₂ => ?_
  obtain ⟨rfl, ht⟩ := h₂
  have hpre : ∀ w' x', w' = w₂ ∧ x' = x₂ → TopRel w' x' := fun _ _ h => by
    obtain ⟨rfl, rfl⟩ := h
    exact ht
  refine ISim.mono hpre (fun _ _ _ _ h => h) ?_
  rcases a with f | flow
  · refine ISim.ite (fun _ => ?_) fun _ => ?_
    · exact ISim.seq reset_sim' (ISim.pure fun _ _ hh => ⟨rfl, hh⟩)
    · exact ISim.bind (failCall_sim abandon f true)
        fun _ _ => ISim.pure fun _ _ hh => ⟨by rw [hh.1], hh.2⟩
  · exact ISim.seq reset_sim' (ISim.pure fun _ _ hh => ⟨rfl, hh⟩)))

theorem lexEofStep_sim (hcons : ConsumesAlike H m R E)
    (abandon recover : Location → StateT H m Unit) :
    ISim TopRel TopQ (Lexer.WRustPort.lexEofStep (R := R) (E := E) abandon recover)
      (Lexer.X1BatchInCore.lexEofStep abandon recover) := by
  unfold Lexer.WRustPort.lexEofStep Lexer.X1BatchInCore.lexEofStep
  refine ISim.get_bind fun w x h => ?_
  refine ISim.ite' (by rw [h.1.discard]) (fun _ => ISim.seq reset_sim'
    (ISim.pure fun _ _ h => ⟨rfl, h⟩)) fun _ => ?_
  dsimp only
  refine ISim.get_bind fun w x h => ?_
  rw [h.1.recoveryState]
  generalize x.recoveryState.isSome = recovered
  refine ISim.ite (fun _ => ?_) fun _ => by eof_tail
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

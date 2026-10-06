import BSmtLib.Proofs.X1BatchInCoreX2Contents.Core

/-!
# The hand-overs of the two lexers

The two lexers hand a batch over to the consumer alike, but for a token handed over alone with
its content in the content buffer, whose cursors are twins (`Twin`). The consumer, which does not
tell twins apart (`ContentBlind`), leaves twin cursors, of which the hand-over reads the same
(`obs`): the stop, the version, the batch but for its array of contents, which the hand-over
replaces, and the categories of the consumed tokens.
-/

namespace BSmtLib.Proofs.X1BatchInCoreX2Contents

open BSmtLib.Proofs.Simulation

section

variable {R E : Type} {floor : Option Nat}

/-- What a hand-over reads of the cursor that the consumer leaves, with the stop: the version,
the batch but for its array of contents, and the folds over the categories of the consumed
tokens. -/
def obs (x : Option (Lexer.Interrupted R E floor) × BatchCursor) :
    Option (Lexer.Interrupted R E floor) × Version × TokenBatch ×
      (Nat → (Nat → TokenCategory → Nat) → Nat) :=
  (x.1, x.2.version, { x.2.intoBatch with bytes := ByteArray.empty },
    fun init g => x.2.foldConsumedCategories init g)

theorem obs_twin {c c' : BatchCursor} (t : Twin c c')
    (stop : Option (Lexer.Interrupted R E floor)) :
    obs (stop, c) = obs (stop, c') := by
  simp only [obs, t.version, t.intoBatch, t.foldConsumedCategories]

end

theorem interrupted_ext {R E : Type} {floor : Option Nat} {i j : Lexer.Interrupted R E floor}
    (hr : i.result = j.result) (hl : i.location = j.location) : i = j := by
  obtain ⟨r, l, a⟩ := i
  obtain ⟨r', l', a'⟩ := j
  simp only at hr hl
  subst hr hl
  rfl

instance : Nonempty BatchCursor := ⟨BatchCursor.new .v2_7 default⟩

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} (hblind : ContentBlind H m R E)
include hblind

theorem flushCursor_sim : ∀ n (c c' : BatchCursor), c.remaining = n → Twin c c' →
    ∀ hfl hfl',
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (obs <$> Lexer.X2Contents.flushCursor (H := H) (m := m) (R := R) (E := E) c hfl)
      (obs <$> Lexer.X1BatchInCore.flushCursor c' hfl') := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro c c' hn t hfl hfl'
  rw [Lexer.X2Contents.flushCursor, Lexer.X1BatchInCore.flushCursor]
  by_cases h : c.HasNext
  · have h' : c'.HasNext := t.hasNext.mpr h
    simp only [h, h', dite_true, map_bind]
    obtain ⟨f, hf⟩ := hblind c c' h h' t
    refine SimF.bind (Q := fun x s => BFits s ∧ ((f x).1 = x.1 ∧ Twin x.2.val (f x).2.val))
      (ψ := f) ?_ fun x => ?_
    · unfold Lexer.X2Contents.callConsumer Lexer.X1BatchInCore.callConsumer
      exact SimF.liftGood (fun s => (hf s).1) fun s => (hf s).2
    refine SimF.of_fact fun ⟨e1, t'⟩ => ?_
    obtain ⟨result, next, consumed⟩ := x
    generalize f (result, ⟨next, consumed⟩) = y at e1 t'
    obtain ⟨result', next', consumed'⟩ := y
    dsimp only at e1 t' ⊢
    subst e1
    have hloc := t'.consumedEndOf consumed consumed'
    cases result' with
    | ok flow =>
      cases flow with
      | «continue» =>
        by_cases hr : next.relexRequested = true
        · have hr' : next'.relexRequested = true := by rw [t'.relexRequested]; exact hr
          simp only [hr, hr', ite_true, map_pure]
          refine SimF.pure (fun _ h => h) ?_
          rw [obs_twin t']
          simp only [obs, id, Prod.mk.injEq, and_true]
          exact congrArg some (interrupted_ext rfl hloc.symm)
        · have hr' : ¬next'.relexRequested = true := by rw [t'.relexRequested]; exact hr
          simp only [hr, hr']
          exact ih _
            (by rw [← hn, BatchCursor.remaining_resetConsumed]; exact consumed.remaining_lt)
            _ _ rfl t'.resetConsumed _ _
      | «break» r =>
        simp only [map_pure]
        refine SimF.pure (fun _ h => h) ?_
        rw [obs_twin t']
        simp only [obs, id, Prod.mk.injEq, and_true]
        exact congrArg some (interrupted_ext rfl hloc.symm)
    | error err =>
      simp only [map_pure]
      refine SimF.pure (fun _ h => h) ?_
      rw [obs_twin t']
      simp only [obs, id, Prod.mk.injEq, and_true]
      exact congrArg some (interrupted_ext rfl hloc.symm)
  · have h' : ¬c'.HasNext := fun h' => h (t.hasNext.mp h')
    simp only [h, h', dite_false, map_pure]
    exact SimF.pure (fun _ h => h) (obs_twin t none)

omit [Consume H m R E] hblind in
theorem storeSpent_sim (spent : TokenBatch) :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.storeSpent (H := H) (m := m) (R := R) (E := E) spent)
      (Lexer.X1BatchInCore.storeSpent spent) :=
  modifyBound_sim _ _ (fun _ _ => rfl) fun _ hc => hc

omit [Consume H m R E] hblind in
theorem takeBatch_sim :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.takeBatch (H := H) (m := m) (R := R) (E := E))
      (Lexer.X1BatchInCore.takeBatch) := by
  unfold Lexer.X2Contents.takeBatch Lexer.X1BatchInCore.takeBatch
  exact SimF.modifyGet (fun _ _ => rfl) fun _ hc => hc

/-- Takes the steps that are the same in both lexers and keep the content buffer. -/
local macro "sim_same" : tactic => `(tactic| repeat (first
    | (with_reducible refine getCore_bind fun _ _ => ?_)
    | ((with_reducible refine SimF.seq (modifyCore_same ?_ ?_) fun _ => ?_); (intro _; rfl);
        (intro _; rfl))
    | (with_reducible refine SimF.seq (storeSpent_sim _) fun _ => ?_)
    | ((with_reducible refine SimF.ite ?_ (fun _ => ?_) fun _ => ?_); exact Iff.rfl)
    | ((with_reducible refine SimF.pure (fun _ h => h) ?_); rfl)
    | (with_reducible exact SimF.throw (fun _ h => h) _)
    | (with_reducible refine SimF.seq (SimF.throw (ψ := id) (fun _ h => h) _) fun _ => ?_)
    | ((with_reducible refine modifyCore_same ?_ ?_); (intro _; rfl); (intro _; rfl))
    | (with_reducible exact storeSpent_sim _)))

/-- The rest of a hand-over reads the cursor only through `obs`. -/
local macro "obs_congr" : tactic => `(tactic| (
    intro ⟨stop, cursor⟩ ⟨stop', cursor'⟩ ho
    simp only [obs, Prod.mk.injEq] at ho
    obtain ⟨hstop, hv, hb, hf⟩ := ho
    subst hstop
    dsimp only
    generalize BatchCursor.foldConsumedCategories (β := Nat) cursor = F at hf ⊢
    generalize BatchCursor.foldConsumedCategories (β := Nat) cursor' = F' at hf ⊢
    have hF : F = F' := funext fun i => funext fun g => congrFun (congrFun hf i) g
    subst hF
    generalize cursor.version = V at hv ⊢
    generalize cursor'.version = V' at hv ⊢
    subst hv
    generalize cursor.intoBatch = B at hb ⊢
    generalize cursor'.intoBatch = B' at hb ⊢
    obtain ⟨l, by1, t, cs, ce, so, sl, sc, eo, el, ec, o, ord⟩ := B
    obtain ⟨l', by1', t', cs', ce', so', sl', sc', eo', el', ec', o', ord'⟩ := B'
    simp only [TokenBatch.mk.injEq] at hb
    obtain ⟨e1, -, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12⟩ := hb
    subst e1 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12
    rfl))

/-- The hand-over of a batch and of the same batch with another array of contents, which gives
each of its tokens the same content. -/
theorem handOver_sim (b2 b1 : TokenBatch) (hs : SameTokens b2 b1 b2.len) (bytesAfter : ByteArray)
    (hfl hfl') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.handOver (H := H) (m := m) (R := R) (E := E) b2 bytesAfter hfl)
      (Lexer.X1BatchInCore.handOver b1 bytesAfter hfl') := by
  unfold Lexer.X2Contents.handOver Lexer.X1BatchInCore.handOver
  refine getCore_bind fun c _ => ?_
  refine SimF.bind_obs obs (flushCursor_sim hblind _ _ _ rfl (twin_new _ hs) _ _) ?_ ?_
    fun x => ?_
  · obs_congr
  · obs_congr
  obtain ⟨stop, cursor⟩ := x
  dsimp only
  refine getCore_bind fun _ _ => ?_
  refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · cases stop
    · dsimp only
      sim_same
    · dsimp only
      -- the two lexers count the consumed parentheses by functions of their own
      refine SimF.seq (modifyCore_same ?_ fun _ => rfl) fun _ => ?_
      · intro c
        simp only [coreMap]
        congr 2 <;> (funext d cat; cases cat <;> rfl)
      · sim_same
  · cases stop <;> dsimp only <;> sim_same

theorem flushBatch_sim :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.flushBatch (H := H) (m := m) (R := R) (E := E))
      (Lexer.X1BatchInCore.flushBatch) := by
  unfold Lexer.X2Contents.flushBatch Lexer.X1BatchInCore.flushBatch
  refine getCore_bind fun c _ => ?_
  refine SimF.ite Iff.rfl (fun _ => SimF.pure (fun _ h => h) rfl) fun _ => ?_
  refine SimF.bind takeBatch_sim fun x => ?_
  obtain ⟨batch, hbatch⟩ := x
  exact SimF.bind (handOver_sim hblind _ _ (sameTokens_refl _ _) _ _ _) fun _ => storeSpent_sim _

theorem handOverStored_sim (ty : TokenCategory) (hty hty' : ty ≠ .endOfFile) (s e : Location)
    (hend : s.offset < e.offset) (hfl hfl') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.handOverStored (H := H) (m := m) (R := R) (E := E) ty hty s e hend hfl)
      (Lexer.X1BatchInCore.handOverStored ty hty' s e hend hfl') := by
  unfold Lexer.X2Contents.handOverStored Lexer.X1BatchInCore.handOverStored
  refine SimF.bind (flushBatch_sim hblind) fun _ => ?_
  refine SimF.bind takeBatch_sim fun x => ?_
  obtain ⟨batch, hbatch⟩ := x
  refine getCore_bind fun c hc => ?_
  exact SimF.bind (handOver_sim hblind _ _ (sameTokens_stored hc _ _ _ _ _ _ _ _ _) _ _ _)
    fun _ => storeSpent_sim _

theorem handOverEof_sim (location : Location) :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := none) (low := low)) id
      (Lexer.X2Contents.handOverEof (H := H) (m := m) (R := R) (E := E) location)
      (Lexer.X1BatchInCore.handOverEof location) := by
  unfold Lexer.X2Contents.handOverEof Lexer.X1BatchInCore.handOverEof
  refine SimF.bind (flushBatch_sim hblind) fun _ => ?_
  refine SimF.bind takeBatch_sim fun x => ?_
  obtain ⟨batch, hbatch⟩ := x
  refine getCore_bind fun c hc => ?_
  exact SimF.bind (handOver_sim hblind _ _ (sameTokens_stored hc _ _ _ _ _ _ _ _ _) _ _ _)
    fun _ => storeSpent_sim _

theorem sinkStored_sim (ty : TokenCategory) (hty hty' : ty ≠ .endOfFile)
    (te : Lexer.Slice.TokenEnd) (s : Location) (base : Nat) (h h') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.sinkStored (H := H) (m := m) (R := R) (E := E) ty hty te s base h)
      (Lexer.X1BatchInCore.sinkStored ty hty' te s base h') := by
  unfold Lexer.X2Contents.sinkStored Lexer.X1BatchInCore.sinkStored
  refine SimF.seq (locationFrom_sim base te.position) fun x => ?_
  exact handOverStored_sim hblind _ _ _ _ _ _ _ _

end

end BSmtLib.Proofs.X1BatchInCoreX2Contents

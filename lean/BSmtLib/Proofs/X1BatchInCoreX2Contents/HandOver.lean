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

open BSmtLib.Lexer.Internal (intoBatch)
open BSmtLib.Proofs.Simulation

section

variable {R E : Type} {floor : Option Nat} {γ γ' : BatchTag}

/-- What a hand-over reads of the cursor that the consumer leaves, with the stop: the version,
the batch but for its array of contents, and the folds over the categories of the consumed
tokens. -/
def obs (x : Option (Lexer.Interrupted R E floor) × BatchCursor γ) :
    Option (Lexer.Interrupted R E floor) × Version × TokenBatch ×
      (Nat → (Nat → TokenCategory → Nat) → Nat) :=
  (x.1, x.2.version, { intoBatch x.2 with bytes := ByteArray.empty },
    fun init g => x.2.foldConsumedCategories init g)

theorem obs_twin {c : BatchCursor γ} {c' : BatchCursor γ'} (t : Twin c c')
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


section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]
  {floor : Option Nat} {low : Nat} {γ γ' : BatchTag} (hblind : ContentBlind H m R E)
include hblind

theorem flushCursor_sim : ∀ n (c : BatchCursor γ) (c' : BatchCursor γ'), c.remaining = n →
    Twin c c' →
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

omit [Consume H m R E] hblind in
/-- What the lexer with the content buffer does after its loop over the cursor, as a function of
what it reads of the cursor (`obs`). -/
def tailX2 (bytesAfter : ByteArray)
    (w : Option (Lexer.Interrupted R E floor) × Version × TokenBatch ×
      (Nat → (Nat → TokenCategory → Nat) → Nat)) :
    Lexer.X2Contents.LexM H m R E floor low TokenBatch := do
  if (← Lexer.X2Contents.getCore).recovers then
    match w.1 with
    | some _ =>
      Lexer.X2Contents.modifyCore fun c =>
        let consumedDepth := w.2.2.2 c.consumedDepth fun depth category =>
          match category with
          | .parenOpen => depth + 1
          | .parenClose => depth - 1
          | _ => depth
        { c with consumedDepth, lexedDepth := consumedDepth }
    | none =>
      Lexer.X2Contents.modifyCore fun c => { c with consumedDepth := c.lexedDepth }
  Lexer.X2Contents.modifyCore fun c => { c with version := w.2.1 }
  let spent : TokenBatch := { w.2.2.1 with bytes := bytesAfter }
  if let some interrupted := w.1 then
    Lexer.X2Contents.storeSpent spent
    throw interrupted
  return spent

omit [Consume H m R E] hblind in
/-- What the lexer with the batch in its state does after its loop over the cursor, as a
function of what it reads of the cursor (`obs`). -/
def tailX1 (bytesAfter : ByteArray)
    (w : Option (Lexer.Interrupted R E floor) × Version × TokenBatch ×
      (Nat → (Nat → TokenCategory → Nat) → Nat)) :
    Lexer.X1BatchInCore.LexM H m R E floor low TokenBatch := do
  if (← Lexer.X1BatchInCore.getCore).recovers then
    match w.1 with
    | some _ =>
      Lexer.X1BatchInCore.modifyCore fun c =>
        let consumedDepth := w.2.2.2 c.consumedDepth fun depth category =>
          match category with
          | .parenOpen => depth + 1
          | .parenClose => depth - 1
          | _ => depth
        { c with consumedDepth, lexedDepth := consumedDepth }
    | none =>
      Lexer.X1BatchInCore.modifyCore fun c => { c with consumedDepth := c.lexedDepth }
  Lexer.X1BatchInCore.modifyCore fun c => { c with version := w.2.1 }
  let spent : TokenBatch := { w.2.2.1 with bytes := bytesAfter }
  if let some interrupted := w.1 then
    Lexer.X1BatchInCore.storeSpent spent
    throw interrupted
  return spent

omit hblind in
/-- The hand-over of the lexer with the content buffer reads the cursor that the consumer
leaves only through `obs`. The two lexers' cursors are over different batches, so their
results are of different types, and are compared through `obs`. -/
theorem handOver_x2 (batch : TokenBatch) (bytesAfter : ByteArray) (hfl) :
    Lexer.X2Contents.handOver (H := H) (m := m) (R := R) (E := E) (floor := floor) (low := low)
      batch bytesAfter hfl =
      Lexer.X2Contents.getCore >>= fun c =>
        (obs <$> Lexer.X2Contents.flushCursor (BatchCursor.new c.version batch)
          fun p hp => BatchCursor.endsAfter_new (hfl p hp) _) >>= tailX2 bytesAfter := by
  unfold Lexer.X2Contents.handOver
  refine congrArg (_ >>= ·) (funext fun c => ?_)
  rw [bind_map_left]
  rfl

omit hblind in
/-- The hand-over of the lexer with the batch in its state reads the cursor that the consumer
leaves only through `obs`. -/
theorem handOver_x1 (batch : TokenBatch) (bytesAfter : ByteArray) (hfl) :
    Lexer.X1BatchInCore.handOver (H := H) (m := m) (R := R) (E := E) (floor := floor)
      (low := low) batch bytesAfter hfl =
      Lexer.X1BatchInCore.getCore >>= fun c =>
        (obs <$> Lexer.X1BatchInCore.flushCursor (BatchCursor.new c.version batch)
          fun p hp => BatchCursor.endsAfter_new (hfl p hp) _) >>= tailX1 bytesAfter := by
  unfold Lexer.X1BatchInCore.handOver
  refine congrArg (_ >>= ·) (funext fun c => ?_)
  rw [bind_map_left]
  rfl

/-- The hand-over of a batch and of the same batch with another array of contents, which gives
each of its tokens the same content. -/
theorem handOver_sim (b2 b1 : TokenBatch) (hs : SameTokens b2 b1 b2.len) (bytesAfter : ByteArray)
    (hfl hfl') :
    SimF BFits BFits (fun _ => BFits) (boundMap (floor := floor) (low := low)) id
      (Lexer.X2Contents.handOver (H := H) (m := m) (R := R) (E := E) b2 bytesAfter hfl)
      (Lexer.X1BatchInCore.handOver b1 bytesAfter hfl') := by
  rw [handOver_x2, handOver_x1]
  refine getCore_bind fun c _ => ?_
  refine SimF.bind (flushCursor_sim hblind _ _ _ rfl (twin_new _ hs) _ _) fun w => ?_
  obtain ⟨stop, version, batch, fold⟩ := w
  unfold tailX2 tailX1
  dsimp only [id]
  refine getCore_bind fun _ _ => ?_
  refine SimF.ite Iff.rfl (fun _ => ?_) fun _ => ?_
  · cases stop <;> dsimp only <;> sim_same
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

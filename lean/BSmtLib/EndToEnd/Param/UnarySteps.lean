import BSmtLib.EndToEnd.Param.Unary

/-!
# The facts of `UL` for each function of the lexer

The helpers of the lexer's state keep the version; the consumer is called only in
`flushCursor`, which hands it cursors in the lexer's version, and `handOver` puts the version of
the cursor the consumer gave back into the lexer, or throws the consumer's error with the batch
empty. Every other function is taken apart by `usim`.
-/

namespace BSmtLib.EndToEnd.Param

open BSmtLib.Lexer BSmtLib.Lexer.Internal
open BSmtLib.Proofs.Adapter

section

variable {consumer : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} {low : Nat}

theorem getCore_usim : UL (getCore : FM consumer floor low LexerCore) := by
  unfold getCore; usim

theorem modifyCore_usim (f : LexerCore → LexerCore) (h)
    (hf : ∀ c, (f c).version = c.version) :
    UL (modifyCore f h : FM consumer floor low Unit) := by
  unfold modifyCore
  exact UL.modifyThe _ fun c => hf c.val

theorem modifyBound_usim (f) (hf : ∀ c h, (f c h).val.version = c.version) :
    UL (modifyBound f : FM consumer floor low Unit) := by
  unfold modifyBound
  exact UL.modifyThe _ fun c => hf c.val c.property

theorem setNormal_usim : UL (setNormal : FM consumer floor low Unit) := by
  unfold setNormal; usim

theorem setTokenState_usim (state start h) :
    UL (setTokenState state start h : FM consumer floor low Unit) := by
  unfold setTokenState; usim

theorem modifyContent_usim (f) : UL (modifyContent f : FM consumer floor low Unit) := by
  unfold modifyContent; usim

theorem extendContent_usim (input start stop) :
    UL (extendContent input start stop : FM consumer floor low Unit) := by
  unfold extendContent; usim

theorem pushContent_usim (c) : UL (pushContent c : FM consumer floor low Unit) := by
  unfold pushContent; usim

theorem startToken_usim (offset base position hframe) :
    UL (startToken offset base position hframe :
      FM consumer floor low
        {start : Location // start.offset = offset + (position - base).toNat}) := by
  unfold startToken; usim

theorem markLineFeedAt_usim (position) :
    UL (markLineFeedAt position : FM consumer floor low Unit) := by
  unfold markLineFeedAt; usim

theorem failWith_usim {α : Type} (kind position failure) :
    UL (failWith kind position failure : FM consumer floor low α) := by
  unfold failWith; usim

theorem failAt_usim {α : Type} (kind position) :
    UL (failAt kind position : FM consumer floor low α) := by
  unfold failAt; usim

theorem fail_usim {α : Type} (kind tokenEnd) :
    UL (fail kind tokenEnd : FM consumer floor low α) := by
  unfold fail; usim

theorem expectDelimiter_usim (next position) :
    UL (expectDelimiter next position : FM consumer floor low Unit) := by
  unfold expectDelimiter; usim

theorem storeSpent_usim (spent) : UL (storeSpent spent : FM consumer floor low Unit) := by
  unfold storeSpent; usim

theorem takeBatch_usim :
    UL (takeBatch : FM consumer floor low
      {batch : TokenBatch // ∀ p, floor = some p → batch.StartsFrom p}) := by
  unfold takeBatch; usim

theorem locationFrom_usim (base position) :
    UL (locationFrom base position :
      FM consumer floor low {location : Location // low ≤ location.offset}) := by
  unfold locationFrom; usim

theorem consumesWhitespaceAndComments_usim :
    UL (consumesWhitespaceAndComments : FM consumer floor low Bool) := by
  unfold consumesWhitespaceAndComments; usim

theorem leave_usim (offset base position batch hframe hbatch) :
    UL (leave offset base position batch hframe hbatch : FM consumer floor low Unit) := by
  unfold leave; usim

theorem leavePending_usim (state start offset base position batch hframe hbatch hstart hfloor) :
    UL (leavePending state start offset base position batch hframe hbatch hstart hfloor :
      FM consumer floor low Unit) := by
  unfold leavePending; usim

end
/-! ## The handover -/

section

variable {consumer : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat} {low : Nat}

theorem bne_self_version (v : Version) : (v != v) = false := by
  cases v <;> rfl

/-- What the consumer's state becomes after a call on the cursor that answered `answer` and gave
back `next`. -/
def flaggedAfter (fl : Flagged consumer) {b : BatchTag} (cursor : BatchCursor b) {α : Type}
    (answer : Except (Option consumer.Error) α) (next : BatchCursor b) : Flagged consumer where
  errored := fl.errored || cursor.version != fl.version || isError answer
  version := next.version
  spoiled := fl.spoiled || fl.errored || cursor.version != fl.version
  layout := if fl.errored then fl.layout else isLayoutAnswer answer

theorem frun_callConsumer {b : BatchTag} (cursor : BatchCursor b) (h : cursor.HasNext) (s fl l) :
    frun (callConsumer cursor h : FM consumer floor low _) s fl l =
      let r := (Answering.consume consumer cursor h).run l
      (((.ok r.1, s), flaggedAfter fl cursor r.1.1 r.1.2.val), r.2) := rfl

theorem frun_getCore (s : {c : LexerCore // c.Bound floor low}) (fl : Flagged consumer) (l) :
    frun (getCore : FM consumer floor low LexerCore) s fl l = (((.ok s.val, s), fl), l) := rfl

theorem frun_pure {α : Type} (a : α) (s : {c : LexerCore // c.Bound floor low})
    (fl : Flagged consumer) (l) :
    frun (Pure.pure a : FM consumer floor low α) s fl l = (((.ok a, s), fl), l) := rfl

theorem frun_modifyCore (f : LexerCore → LexerCore) (h) (s : {c : LexerCore // c.Bound floor low})
    (fl : Flagged consumer) (l) :
    frun (modifyCore f h : FM consumer floor low Unit) s fl l =
      (((.ok (), ⟨f s.val, h s.val s.property⟩), fl), l) := rfl

/-- What a handover of a cursor in the consumer's version gives: a stop, if any, and the cursor
the consumer left, the lexer's version as it was; while nothing went wrong, the consumer's version
is that cursor's; once the consumer answered an error, the stop is that error. -/
theorem flushCursor_flag {b : BatchTag} :
    ∀ (n : Nat) (cursor : BatchCursor b) (hfloor) (s : {c : LexerCore // c.Bound floor low})
      (fl : Flagged consumer) (l), cursor.remaining < n → fl.errored = false →
      cursor.version = fl.version →
      ∃ stop cur, (frun (flushCursor cursor hfloor) s fl l).1.1.1 = .ok (stop, cur) ∧
        (frun (flushCursor cursor hfloor) s fl l).1.1.2.val.version = s.val.version ∧
        ((frun (flushCursor cursor hfloor) s fl l).1.2.errored = false →
          (frun (flushCursor cursor hfloor) s fl l).1.2.version = cur.version) ∧
        ((frun (flushCursor cursor hfloor) s fl l).1.2.errored = true →
          ∃ i, stop = some i ∧ ∃ e, i.result = .error (.consumer e) ∧
            ((frun (flushCursor cursor hfloor) s fl l).1.2.layout = true → e = none)) ∧
        (frun (flushCursor cursor hfloor) s fl l).1.2.spoiled = fl.spoiled
  | 0, _, _, _, _, _, hn, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, cursor, hfloor, s, fl, l, hn, he, hv => by
    rw [flushCursor.eq_1]
    by_cases h : cursor.HasNext
    · rw [dite_eq_left_of_eq_true (eq_true h), frun_bind, frun_getCore]
      dsimp only
      by_cases hold : s.val.holding = true
      · rw [ite_eq_left hold, frun_pure]
        exact ⟨_, _, rfl, rfl, fun _ => hv.symm, fun h' => (by
          have h'' : true = false := h'.symm.trans he; cases h''), rfl⟩
      · rw [ite_eq_right hold, frun_bind, frun_callConsumer]
        dsimp only
        generalize hr : (Answering.consume consumer cursor h).run l = r
        obtain ⟨⟨answer, ⟨next, consumed⟩⟩, l'⟩ := r
        simp only [flaggedAfter, he, hv, bne_self_version, Bool.or_false, Bool.false_or]
        cases answer with
        | error e =>
          dsimp only
          by_cases hd : next.discardRequested = true
          · rw [ite_eq_left hd, frun_bind]
            erw [frun_modifyCore]
            dsimp only
            rw [frun_pure]
            exact ⟨_, _, rfl, rfl, fun h' => by simp [isError] at h',
              fun _ => ⟨_, rfl, e, rfl, fun hl => by cases e <;> simp_all [isLayoutAnswer]⟩, rfl⟩
          · rw [ite_eq_right hd, frun_pure]
            exact ⟨_, _, rfl, rfl, fun h' => by simp [isError] at h',
              fun _ => ⟨_, rfl, e, rfl, fun hl => by cases e <;> simp_all [isLayoutAnswer]⟩, rfl⟩
        | ok flow =>
          simp only [isError]
          by_cases hd : next.discardRequested = true
          · rw [ite_eq_left hd, frun_pure]
            exact ⟨_, _, rfl, rfl, fun _ => rfl, fun h' => (by cases h'), rfl⟩
          · rw [ite_eq_right hd]
            cases flow with
            | «continue» =>
              dsimp only
              by_cases hrel : next.relexRequested = true
              · rw [ite_eq_left hrel, frun_pure]
                exact ⟨_, _, rfl, rfl, fun _ => rfl, fun h' => (by cases h'), rfl⟩
              · rw [ite_eq_right hrel]
                exact flushCursor_flag n next.resetConsumed _ s _ l'
                  (by
                    rw [BatchCursor.remaining_resetConsumed]
                    exact Nat.lt_of_lt_of_le consumed.remaining_lt (Nat.le_of_lt_succ hn))
                  rfl rfl
            | «break» result =>
              dsimp only
              by_cases hn' : next.HasNext
              · rw [dite_eq_left_of_eq_true (eq_true hn'), frun_pure]
                exact ⟨_, _, rfl, rfl, fun _ => rfl, fun h' => (by cases h'), rfl⟩
              · rw [dite_eq_right_of_eq_false (eq_false hn'), frun_pure]
                exact ⟨_, _, rfl, rfl, fun _ => rfl, fun h' => (by cases h'), rfl⟩
    · rw [dite_eq_right_of_eq_false (eq_false h), frun_pure]
      exact ⟨_, _, rfl, rfl, fun _ => hv.symm, fun h' => (by
        have h'' : true = false := h'.symm.trans he; cases h''), rfl⟩

theorem frun_throw {α : Type} (i : Interrupted consumer.Result (Option consumer.Error) floor)
    (s : {c : LexerCore // c.Bound floor low}) (fl : Flagged consumer) (l) :
    frun (MonadExcept.throw i : FM consumer floor low α) s fl l = (((.error i, s), fl), l) := rfl

theorem storeSpent_run (spent : TokenBatch) (s : {c : LexerCore // c.Bound floor low})
    (fl : Flagged consumer) (l) :
    ∃ s', frun (storeSpent spent : FM consumer floor low Unit) s fl l = (((.ok (), s'), fl), l) ∧
      s'.val.batch.len = 0 ∧ s'.val.version = s.val.version :=
  ⟨_, rfl, rfl, rfl⟩

theorem handOver_usim (batch bytesAfter hfloor) :
    UL (handOver batch bytesAfter hfloor : FM consumer floor low TokenBatch) := by
  intro s fl l he hv
  unfold handOver
  rw [frun_bind, frun_getCore]
  dsimp only
  rw [frun_bind]
  obtain ⟨stop, cur, hres, hs, hok, herr, hsp⟩ :=
    flushCursor_flag _ (BatchCursor.new s.val.version batch) _ s fl l (Nat.lt_succ_self _) he hv
  generalize frun (flushCursor (BatchCursor.new s.val.version batch) _) s fl l = r
    at hres hs hok herr hsp
  obtain ⟨⟨⟨res, s'⟩, fl'⟩, l'⟩ := r
  simp only at hres hs hok herr hsp
  subst hres
  dsimp only
  rw [frun_bind, frun_getCore]
  dsimp only
  cases stop with
  | none =>
    have hfalse : fl'.errored = false := by
      cases h : fl'.errored
      · rfl
      · obtain ⟨_, hi, _⟩ := herr h; cases hi
    have hrest := fun s₁ hv₁ =>
      let h := (UL.pure (consumer := consumer) (floor := floor) (low := low)
        ({ intoBatch cur with bytes := bytesAfter } : TokenBatch)) s₁ fl' l' hfalse hv₁
      And.intro h.1 (And.intro h.2.1 (h.2.2.trans hsp))
    by_cases hrec : s'.val.recovers = true
    · rw [ite_eq_left hrec, frun_bind]
      erw [frun_modifyCore]
      dsimp only
      rw [frun_bind]
      erw [frun_modifyCore]
      dsimp only
      exact hrest _ (hok hfalse).symm
    · rw [ite_eq_right hrec, frun_bind]
      erw [frun_modifyCore]
      dsimp only
      exact hrest _ (hok hfalse).symm
  | some i =>
    have hrest : ∀ s₁ : {c : LexerCore // c.Bound floor low}, s₁.val.version = cur.version →
        ((frun (do
            storeSpent ({ intoBatch cur with bytes := bytesAfter } : TokenBatch)
            MonadExcept.throw i
            pure ({ intoBatch cur with bytes := bytesAfter } : TokenBatch) :
            FM consumer floor low TokenBatch) s₁ fl' l').1.2.errored = false →
          (frun (do
            storeSpent ({ intoBatch cur with bytes := bytesAfter } : TokenBatch)
            MonadExcept.throw i
            pure ({ intoBatch cur with bytes := bytesAfter } : TokenBatch) :
            FM consumer floor low TokenBatch) s₁ fl' l').1.1.2.val.version =
          (frun (do
            storeSpent ({ intoBatch cur with bytes := bytesAfter } : TokenBatch)
            MonadExcept.throw i
            pure ({ intoBatch cur with bytes := bytesAfter } : TokenBatch) :
            FM consumer floor low TokenBatch) s₁ fl' l').1.2.version) ∧
        ((frun (do
            storeSpent ({ intoBatch cur with bytes := bytesAfter } : TokenBatch)
            MonadExcept.throw i
            pure ({ intoBatch cur with bytes := bytesAfter } : TokenBatch) :
            FM consumer floor low TokenBatch) s₁ fl' l').1.2.errored = true →
          ConsumerThrow (frun (do
            storeSpent ({ intoBatch cur with bytes := bytesAfter } : TokenBatch)
            MonadExcept.throw i
            pure ({ intoBatch cur with bytes := bytesAfter } : TokenBatch) :
            FM consumer floor low TokenBatch) s₁ fl' l').1.2.layout (frun (do
            storeSpent ({ intoBatch cur with bytes := bytesAfter } : TokenBatch)
            MonadExcept.throw i
            pure ({ intoBatch cur with bytes := bytesAfter } : TokenBatch) :
            FM consumer floor low TokenBatch) s₁ fl' l').1.1.1 ∧
          (frun (do
            storeSpent ({ intoBatch cur with bytes := bytesAfter } : TokenBatch)
            MonadExcept.throw i
            pure ({ intoBatch cur with bytes := bytesAfter } : TokenBatch) :
            FM consumer floor low TokenBatch) s₁ fl' l').1.1.2.val.batch.len = 0) ∧
        (frun (do
            storeSpent ({ intoBatch cur with bytes := bytesAfter } : TokenBatch)
            MonadExcept.throw i
            pure ({ intoBatch cur with bytes := bytesAfter } : TokenBatch) :
            FM consumer floor low TokenBatch) s₁ fl' l').1.2.spoiled = fl.spoiled := by
      intro s₁ hs₁
      rw [frun_bind]
      obtain ⟨s₂, hs₂, hlen, hver⟩ := storeSpent_run
        ({ intoBatch cur with bytes := bytesAfter } : TokenBatch) s₁ fl' l'
      rw [hs₂]
      dsimp only
      rw [frun_bind, frun_throw]
      dsimp only
      refine ⟨fun h => ?_, fun h => ?_, hsp⟩
      · rw [hver, hs₁, hok h]
      · obtain ⟨j, hj, e, he⟩ := herr h
        cases hj
        exact ⟨⟨_, rfl, e, he⟩, hlen⟩
    by_cases hrec : s'.val.recovers = true
    · rw [ite_eq_left hrec, frun_bind]
      erw [frun_modifyCore]
      dsimp only
      rw [frun_bind]
      erw [frun_modifyCore]
      dsimp only
      exact hrest _ rfl
    · rw [ite_eq_right hrec, frun_bind]
      erw [frun_modifyCore]
      dsimp only
      exact hrest _ rfl

end

end BSmtLib.EndToEnd.Param

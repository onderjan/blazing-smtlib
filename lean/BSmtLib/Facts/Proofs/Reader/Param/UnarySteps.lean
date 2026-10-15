module

public import BSmtLib.Facts.Proofs.Reader.Param.Unary
import all BSmtLib.Lexer
import all BSmtLib.Token

@[expose] public section

/-!
# The facts of `UL` for each function of the lexer

The helpers of the lexer's state keep the version; the consumer is called only in
`flushCursor`, which hands it cursors in the lexer's version, and `handOver` puts the version of
the cursor the consumer gave back into the lexer, or throws the consumer's error with the batch
empty. Every other function is taken apart by `usim`.
-/

namespace BSmtLib.Facts.Proofs.Reader.Param.UnarySteps

open BSmtLib.Lexer
open BSmtLib.Token.BatchCursor.Internal (discardRequested resetConsumed remaining relexRequested)
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Reader.Param.Unary

section

variable {F σ R E : Type} [Token.Consume F R (Option E)]
  [∀ b, Token.ConsumeFrom F (Token.BatchCursor b) (StateM σ)] [Watched F σ R E]
  {floor : Option Nat} {low : Nat}

theorem getCore_usim : UL (Internal.getCore : FM F σ floor low LexerCore) := by
  unfold Internal.getCore; usim

theorem modifyCore_usim (f : LexerCore → LexerCore) (h)
    (hf : ∀ c, (f c).version = c.version) :
    UL (Internal.modifyCore f h : FM F σ floor low Unit) := by
  unfold Internal.modifyCore
  exact UL.modifyThe _ fun c => hf c.val

theorem modifyBound_usim (f) (hf : ∀ c h, (f c h).val.version = c.version) :
    UL (Internal.modifyBound f : FM F σ floor low Unit) := by
  unfold Internal.modifyBound
  exact UL.modifyThe _ fun c => hf c.val c.property

theorem setNormal_usim : UL (Internal.setNormal : FM F σ floor low Unit) := by
  unfold Internal.setNormal; usim

theorem setTokenState_usim (state start h) :
    UL (Internal.setTokenState state start h : FM F σ floor low Unit) := by
  unfold Internal.setTokenState; usim

theorem modifyContent_usim (f) : UL (Internal.modifyContent f : FM F σ floor low Unit) := by
  unfold Internal.modifyContent; usim

theorem extendContent_usim (input start stop) :
    UL (Internal.extendContent input start stop : FM F σ floor low Unit) := by
  unfold Internal.extendContent; usim

theorem pushContent_usim (c) : UL (Internal.pushContent c : FM F σ floor low Unit) := by
  unfold Internal.pushContent; usim

theorem startToken_usim (offset base position hframe) :
    UL (Internal.startToken offset base position hframe :
      FM F σ floor low
        {start : Span.Location // start.offset = offset + (position - base).toNat}) := by
  unfold Internal.startToken; usim

theorem markLineFeedAt_usim (position) :
    UL (Internal.markLineFeedAt position : FM F σ floor low Unit) := by
  unfold Internal.markLineFeedAt; usim

theorem failWith_usim {α : Type} (kind position failure) :
    UL (Internal.failWith kind position failure : FM F σ floor low α) := by
  unfold Internal.failWith; usim

theorem failAt_usim {α : Type} (kind position) :
    UL (Internal.failAt kind position : FM F σ floor low α) := by
  unfold Internal.failAt; usim

theorem fail_usim {α : Type} (kind tokenEnd) :
    UL (Internal.fail kind tokenEnd : FM F σ floor low α) := by
  unfold Internal.fail; usim

theorem expectDelimiter_usim (next position) :
    UL (Internal.expectDelimiter next position : FM F σ floor low Unit) := by
  unfold Internal.expectDelimiter; usim

theorem storeSpent_usim (spent) : UL (Internal.storeSpent spent : FM F σ floor low Unit) := by
  unfold Internal.storeSpent; usim

theorem takeBatch_usim :
    UL (Internal.takeBatch : FM F σ floor low
      {batch : Token.Internal.TokenBatch // ∀ p, floor = some p → batch.StartsFrom p}) := by
  unfold Internal.takeBatch; usim

theorem locationFrom_usim (base position) :
    UL (Internal.locationFrom base position :
      FM F σ floor low {location : Span.Location // low ≤ location.offset}) := by
  unfold Internal.locationFrom; usim

theorem consumesWhitespaceAndComments_usim :
    UL (Internal.consumesWhitespaceAndComments : FM F σ floor low Bool) := by
  unfold Internal.consumesWhitespaceAndComments; usim

theorem leave_usim (offset base position batch hframe hbatch) :
    UL (Internal.leave offset base position batch hframe hbatch : FM F σ floor low Unit) := by
  unfold Internal.leave; usim

theorem leavePending_usim (state start offset base position batch hframe hbatch hstart hfloor) :
    UL (Internal.leavePending state start offset base position batch hframe hbatch hstart hfloor :
      FM F σ floor low Unit) := by
  unfold Internal.leavePending; usim

end
/-! ## The handover -/

section

variable {F σ R E : Type} [Token.Consume F R (Option E)]
  [∀ b, Token.ConsumeFrom F (Token.BatchCursor b) (StateM σ)] [Watched F σ R E]
  {floor : Option Nat} {low : Nat}

theorem bne_self_version (v : Token.Version) : (v != v) = false := by
  cases v <;> rfl

/-- `Flagged consumer` keeps the record of what went wrong, in its fields. -/
instance (consumer : BSmtLibSpec.Lexer.Consumer) :
    Watched (Flagged consumer) (List BSmtLibSpec.Lexer.Handed) consumer.Result consumer.Error where
  errored := Flagged.errored
  version := Flagged.version
  spoiled := Flagged.spoiled
  layout := Flagged.layout
  call cursor h fl l he hv := by
    have he' : fl.errored = false := he
    have hv' : cursor.version = fl.version := hv
    refine ⟨?_, rfl, ?_, ?_⟩
    · show (fl.errored || cursor.version != fl.version ||
          Flagged.isError ((Answering.consume consumer cursor h).run l).1.1) = _
      rw [he', hv', bne_self_version]
      rfl
    · show (fl.spoiled || fl.errored || cursor.version != fl.version) = fl.spoiled
      rw [he', hv', bne_self_version]
      simp
    · show (if fl.errored then fl.layout
          else Flagged.isLayoutAnswer ((Answering.consume consumer cursor h).run l).1.1) = _
      rw [he']
      rfl

omit [Watched F σ R E] in
theorem frun_callConsumer {b : Token.BatchTag} (cursor : Token.BatchCursor b) (h : cursor.HasNext)
    (s fl l) :
    frun (Internal.callConsumer cursor h : FM F σ floor low _) s fl l =
      let r := ((Token.ConsumeFrom.consume cursor h : StateT F (StateM σ) _).run fl).run l
      (((.ok r.1.1, s), r.1.2), r.2) := (rfl)

omit [∀ b, Token.ConsumeFrom F (Token.BatchCursor b) (StateM σ)] [Watched F σ R E] in
theorem frun_getCore (s : {c : LexerCore // c.Bound floor low}) (fl : F) (l) :
    frun (Internal.getCore : FM F σ floor low LexerCore) s fl l = (((.ok s.val, s), fl), l) := (rfl)

omit [∀ b, Token.ConsumeFrom F (Token.BatchCursor b) (StateM σ)] [Watched F σ R E] in
theorem frun_pure {α : Type} (a : α) (s : {c : LexerCore // c.Bound floor low})
    (fl : F) (l) :
    frun (Pure.pure a : FM F σ floor low α) s fl l = (((.ok a, s), fl), l) := rfl

omit [∀ b, Token.ConsumeFrom F (Token.BatchCursor b) (StateM σ)] [Watched F σ R E] in
theorem frun_modifyCore (f : LexerCore → LexerCore) (h) (s : {c : LexerCore // c.Bound floor low})
    (fl : F) (l) :
    frun (Internal.modifyCore f h : FM F σ floor low Unit) s fl l =
      (((.ok (), ⟨f s.val, h s.val s.property⟩), fl), l) := (rfl)

/-- What a handover of a cursor in the consumer's version gives: a stop, if any, and the cursor
the consumer left, the lexer's version as it was; while nothing went wrong, the consumer's version
is that cursor's; once the consumer answered an error, the stop is that error. -/
theorem flushCursor_flag {b : Token.BatchTag} :
    ∀ (n : Nat) (cursor : Token.BatchCursor b) (hfloor) (s : {c : LexerCore // c.Bound floor low})
      (fl : F) (l), remaining cursor < n → Watched.errored fl = false →
      cursor.version = Watched.version fl →
      ∃ stop cur, (frun (Internal.flushCursor cursor hfloor) s fl l).1.1.1 = .ok (stop, cur) ∧
        (frun (Internal.flushCursor cursor hfloor) s fl l).1.1.2.val.version = s.val.version ∧
        (Watched.errored (frun (Internal.flushCursor cursor hfloor) s fl l).1.2 = false →
          Watched.version (frun (Internal.flushCursor cursor hfloor) s fl l).1.2 = cur.version) ∧
        (Watched.errored (frun (Internal.flushCursor cursor hfloor) s fl l).1.2 = true →
          ∃ i, stop = some i ∧ ∃ e, i.result = .error (.consumer e) ∧
            (Watched.layout (frun (Internal.flushCursor cursor hfloor) s fl l).1.2 = true → e =
                none)) ∧
        Watched.spoiled (frun (Internal.flushCursor cursor hfloor) s fl l).1.2 = Watched.spoiled fl
  | 0, _, _, _, _, _, hn, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, cursor, hfloor, s, fl, l, hn, he, hv => by
    rw [Internal.flushCursor.eq_1]
    by_cases h : cursor.HasNext
    · rw [dite_eq_left_of_eq_true (eq_true h), frun_bind, frun_getCore]
      dsimp only
      by_cases hold : s.val.holding = true
      · rw [ite_eq_left hold, frun_pure]
        exact ⟨_, _, rfl, rfl, fun _ => hv.symm, fun h' => (by
          have h'' : true = false := h'.symm.trans he; cases h''), rfl⟩
      · rw [ite_eq_right hold, frun_bind, frun_callConsumer]
        dsimp only
        have hcall := Watched.call (R := R) (E := E) cursor h fl l he hv
        dsimp only at hcall
        generalize ((Token.ConsumeFrom.consume cursor h : StateT F (StateM σ) _).run fl).run l = r
          at hcall ⊢
        obtain ⟨⟨⟨answer, ⟨next, consumed⟩⟩, fl'⟩, l'⟩ := r
        obtain ⟨hE, hV, hS, hL⟩ := hcall
        dsimp only at hE hV hS hL
        cases answer with
        | error e =>
          dsimp only
          have hE' : Watched.errored fl' = true := by rw [hE]; rfl
          have hL' : Watched.layout fl' = true → e = none := fun hl => by
            rw [hL] at hl
            cases e <;> simp_all [Flagged.isLayoutAnswer]
          by_cases hd : discardRequested next = true
          · rw [ite_eq_left hd, frun_bind]
            erw [frun_modifyCore]
            dsimp only
            rw [frun_pure]
            exact ⟨_, _, rfl, rfl, fun h' => absurd (hE'.symm.trans h') (by simp),
              fun _ => ⟨_, rfl, e, rfl, hL'⟩, hS⟩
          · rw [ite_eq_right hd, frun_pure]
            exact ⟨_, _, rfl, rfl, fun h' => absurd (hE'.symm.trans h') (by simp),
              fun _ => ⟨_, rfl, e, rfl, hL'⟩, hS⟩
        | ok flow =>
          dsimp only
          have hE' : Watched.errored fl' = false := by rw [hE]; rfl
          have hnot : Watched.errored fl' = true → False := fun h' =>
            absurd (hE'.symm.trans h') (by simp)
          by_cases hd : discardRequested next = true
          · rw [ite_eq_left hd, frun_pure]
            exact ⟨_, _, rfl, rfl, fun _ => hV, fun h' => (hnot h').elim, hS⟩
          · rw [ite_eq_right hd]
            cases flow with
            | «continue» =>
              dsimp only
              by_cases hrel : relexRequested next = true
              · rw [ite_eq_left hrel, frun_pure]
                exact ⟨_, _, rfl, rfl, fun _ => hV, fun h' => (hnot h').elim, hS⟩
              · rw [ite_eq_right hrel]
                obtain ⟨stop, cur, h₁, h₂, h₃, h₄, h₅⟩ := flushCursor_flag n
                    (resetConsumed next) _ s
                  fl' l'
                  (by
                    rw [Token.BatchCursor.remaining_resetConsumed]
                    exact Nat.lt_of_lt_of_le consumed.remaining_lt (Nat.le_of_lt_succ hn))
                  hE' hV.symm
                exact ⟨stop, cur, h₁, h₂, h₃, h₄, h₅.trans hS⟩
            | «break» result =>
              dsimp only
              by_cases hn' : next.HasNext
              · rw [dite_eq_left_of_eq_true (eq_true hn'), frun_pure]
                exact ⟨_, _, rfl, rfl, fun _ => hV, fun h' => (hnot h').elim, hS⟩
              · rw [dite_eq_right_of_eq_false (eq_false hn'), frun_pure]
                exact ⟨_, _, rfl, rfl, fun _ => hV, fun h' => (hnot h').elim, hS⟩
    · rw [dite_eq_right_of_eq_false (eq_false h), frun_pure]
      exact ⟨_, _, rfl, rfl, fun _ => hv.symm, fun h' => (by
        have h'' : true = false := h'.symm.trans he; cases h''), rfl⟩

omit [∀ b, Token.ConsumeFrom F (Token.BatchCursor b) (StateM σ)] [Watched F σ R E] in
theorem frun_throw {α : Type} (i : Interrupted R (Option E) floor)
    (s : {c : LexerCore // c.Bound floor low}) (fl : F) (l) :
    frun (MonadExcept.throw i : FM F σ floor low α) s fl l = (((.error i, s), fl), l) := rfl

omit [∀ b, Token.ConsumeFrom F (Token.BatchCursor b) (StateM σ)] [Watched F σ R E] in
theorem storeSpent_run (spent : Token.Internal.TokenBatch)
    (s : {c : LexerCore // c.Bound floor low})
    (fl : F) (l) :
    ∃ s', frun (Internal.storeSpent spent : FM F σ floor low Unit) s fl l =
        (((.ok (), s'), fl), l) ∧
      s'.val.batch.len = 0 ∧ s'.val.version = s.val.version :=
  ⟨_, rfl, rfl, rfl⟩

theorem handOver_usim (batch bytesAfter hfloor) :
    UL (Internal.handOver batch bytesAfter hfloor : FM F σ floor low
        Token.Internal.TokenBatch) := by
  intro s fl l he hv
  unfold Internal.handOver
  rw [frun_bind, frun_getCore]
  dsimp only
  rw [frun_bind]
  obtain ⟨stop, cur, hres, hs, hok, herr, hsp⟩ :=
    flushCursor_flag _ (Token.BatchCursor.Internal.new s.val.version batch) _ s fl l
        (Nat.lt_succ_self _) he hv
  generalize frun (Internal.flushCursor (Token.BatchCursor.Internal.new s.val.version batch)
      _) s fl l = r
    at hres hs hok herr hsp
  obtain ⟨⟨⟨res, s'⟩, fl'⟩, l'⟩ := r
  simp only at hres hs hok herr hsp
  subst hres
  dsimp only
  rw [frun_bind, frun_getCore]
  dsimp only
  cases stop with
  | none =>
    have hfalse : Watched.errored fl' = false := by
      cases h : Watched.errored fl'
      · rfl
      · obtain ⟨_, hi, _⟩ := herr h; cases hi
    have hrest := fun s₁ hv₁ =>
      let h := (UL.pure (F := F) (floor := floor) (low := low)
        ({ Internal.intoBatch cur with bytes :=
            bytesAfter } : Token.Internal.TokenBatch)) s₁ fl' l' hfalse
            hv₁
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
        let r := frun (do
            Internal.storeSpent ({ Internal.intoBatch cur with bytes := bytesAfter } :
                Token.Internal.TokenBatch)
            MonadExcept.throw i
            pure ({ Internal.intoBatch cur with bytes := bytesAfter } : Token.Internal.TokenBatch) :
            FM F σ floor low Token.Internal.TokenBatch) s₁ fl' l'
        (Watched.errored r.1.2 = false → r.1.1.2.val.version = Watched.version r.1.2) ∧
        (Watched.errored r.1.2 = true →
          ConsumerThrow (Watched.layout r.1.2) r.1.1.1 ∧ r.1.1.2.val.batch.len = 0) ∧
        Watched.spoiled r.1.2 = Watched.spoiled fl := by
      intro s₁ hs₁
      dsimp only
      rw [frun_bind]
      obtain ⟨s₂, hs₂, hlen, hver⟩ := storeSpent_run
        ({ Internal.intoBatch cur with bytes := bytesAfter } : Token.Internal.TokenBatch) s₁ fl' l'
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

end BSmtLib.Facts.Proofs.Reader.Param.UnarySteps

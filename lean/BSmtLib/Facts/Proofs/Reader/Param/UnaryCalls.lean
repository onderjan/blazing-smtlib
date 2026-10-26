module

public import BSmtLib.Facts.Proofs.Reader.Param.UnaryNormal
import all BSmtLib.Lexer
import all BSmtLib.Lexer.Error

@[expose] public section

/-!
# A call whose consumer answered an error fails

The loop over a slice catches the interruptions of its steps: an error of the consumer ends it
with that error, and the batch, empty, hands nothing over again. So the steps of the public
calls on a slice and at the end of the input, run while nothing went wrong and with the versions
agreeing, fail if the consumer answered an error; and on a slice, keep the versions agreeing if
not (`lexSliceStep_flag`, `lexEofStep_flag`).
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Reader.Param.UnaryCalls

open BSmtLib.Lexer
open BSmtLib.Lexer.Internal (BATCH_CAPACITY Stop Interrupted Failure LexerCore InnerM StepM LexM)
open BSmtLib.Facts.Lexer.Adapters
open BSmtLib.Facts.Proofs.Reader.Param.Slice BSmtLib.Facts.Proofs.Reader.Param.Unary
open BSmtLib.Facts.Proofs.Reader.Param.UnaryNormal BSmtLib.Facts.Proofs.Reader.Param.UnarySteps
open BSmtLib.Lexer.Error BSmtLib.Lexer.Internal.Helpers

section

variable {F σ R E : Type} [Token.Consume F R (Option E)]
  [∀ b, Token.ConsumeFrom F (LexerCursor b) (StateM σ)] [Watched F σ R E]

/-- The run of a computation of the consumer's monad from its state and the monad's state. -/
abbrev crun {α : Type} (x : StateT F (StateM σ) α) (fl : F)
    (l : σ) := (x.run fl).run l

theorem crun_bind {α β : Type} (x : StateT F (StateM σ) α)
    (k : α → StateT F (StateM σ) β) (fl l) :
    crun (x >>= k) fl l = crun (k (crun x fl l).1.1) (crun x fl l).1.2 (crun x fl l).2 := rfl

theorem crun_pure {α : Type} (a : α) (fl : F) (l) :
    crun (Pure.pure a : StateT F (StateM σ) α) fl l = ((a, fl), l) := rfl

omit [∀ b, Token.ConsumeFrom F (LexerCursor b) (StateM σ)] [Watched F σ R E] in
theorem crun_bind_frun {floor : Option Nat} {low : Nat} {α β : Type} (f : FM F σ floor low α)
    (s : {c : LexerCore // c.Bound floor low})
    (k : Except (Interrupted R (Option E) floor) α ×
      {c : LexerCore // c.Bound floor low} → StateT F (StateM σ) β) (fl l) :
    crun (StateT.run (ExceptT.run f) s >>= k) fl l =
      crun (k (frun f s fl l).1.1) (frun f s fl l).1.2 (frun f s fl l).2 := rfl

/-- Whether the exit of the loop over a slice is a failure: by the consumer's error `none` if
`layout`. -/
def exitFails {R ε : Type} {floor : Option Nat} (layout : Bool) :
    Internal.SliceExit R (Option ε) floor → Prop
  | .done (.error failure) => layout = true → failure.cause = .consumer none
  | _ => False

omit [Watched F σ R E] in
/-- An empty batch is handed over without the consumer. -/
theorem flushBatch_empty {floor : Option Nat} (s : {c : LexerCore // c.Bound floor 0})
    (hs : s.val.batch.len = 0) (fl : F) (l) :
    frun (Internal.flushBatch : FM F σ floor 0 Unit) s fl l = (((.ok (), s), fl), l) := by
  unfold Internal.flushBatch
  rw [frun_bind, frun_getCore]
  simp only [hs, beq_self_eq_true, ite_true]
  rfl

/-- A computation of the consumer's monad that starts with a step of the lexer: what follows the
step, from where the step leaves the lexer and the consumer, as `UL` says. -/
theorem crun_bind_UL {floor : Option Nat} {low : Nat} {α β : Type} {f : FM F σ floor low α}
    {s : {c : LexerCore // c.Bound floor low}}
    {k : Except (Interrupted R (Option E) floor) α ×
      {c : LexerCore // c.Bound floor low} → StateT F (StateM σ) β} {fl l}
    (P : (β × F) × σ → Prop) (hf : UL f)
    (he : Watched.errored fl = false) (hv : s.val.version = Watched.version fl)
    (hk : ∀ res s' (fl' : F) l',
      (Watched.errored fl' = false → s'.val.version = Watched.version fl') →
      (Watched.errored fl' = true → ConsumerThrow (Watched.layout fl') res ∧ s'.val.batch.len = 0) →
      Watched.spoiled fl' = Watched.spoiled fl →
      P (crun (k (res, s')) fl' l')) :
    P (crun (StateT.run (ExceptT.run f) s >>= k) fl l) := by
  rw [crun_bind_frun]
  obtain ⟨h₁, h₂, h₃⟩ := hf s fl l he hv
  exact hk _ _ _ _ h₁ h₂ h₃

/-- After the loop over a slice: while nothing went wrong the versions agree, once the consumer
answered an error the loop failed, and whether the consumer was spoiled is `spoiled`. -/
def SliceOk {floor : Option Nat} (spoiled : Bool)
    (r : ((Internal.SliceExit R (Option E) floor ×
      {c : LexerCore // c.Bound floor 0}) × F) × σ) :
          Prop :=
  (Watched.errored r.1.2 = false → r.1.1.2.val.version = Watched.version r.1.2) ∧
    (Watched.errored r.1.2 = true → exitFails (Watched.layout r.1.2) r.1.1.1) ∧
      Watched.spoiled r.1.2 = spoiled

theorem lexSliceRun_flag_lt {floor : Option Nat} (input : Internal.CharClass.Input) :
    ∀ (n : Nat) (position : USize) (fnResult : Except (Failure (Option E))
      (ControlFlow R)) (core : {c : LexerCore // c.Bound floor 0})
      (fl : F) (l), runMeasure input position fnResult < n →
      (Watched.errored fl = false → core.val.version = Watched.version fl →
        SliceOk (Watched.spoiled fl) (crun (Internal.lexSliceRun input position fnResult core) fl
            l)) ∧
      (Watched.errored fl = true → (∃ e, fnResult = .error e) → core.val.batch.len = 0 →
        crun (Internal.lexSliceRun input position fnResult core) fl l =
            (((.done fnResult, core), fl), l))
  | 0, _, _, _, _, _, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, position, fnResult, core, fl, l, hn => by
    rw [Internal.lexSliceRun.eq_def]
    rcases fnResult with e | f
    · -- a failure is still to be returned: the batch is handed over
      simp only [Bool.or_true, dite_true]
      refine ⟨fun he hv => ?_, fun he _ hb => ?_⟩
      · refine crun_bind_UL (SliceOk (Watched.spoiled fl)) flushBatch_usim he hv ?_
        intro res s' fl' l' h₁ h₂ h₃
        rcases res with ⟨result, span, location, stopAfter⟩ | ⟨⟩
        · cases result with
          | ok stop =>
            refine ⟨fun h => h₁ h, fun h => ?_, h₃⟩
            obtain ⟨⟨i, hi, e, he, -⟩, -⟩ := h₂ h
            cases hi
            cases he
          | error cause =>
            refine ⟨fun h => h₁ h, fun h => ?_, h₃⟩
            obtain ⟨⟨i, hi, e, he, hl⟩, -⟩ := h₂ h
            cases hi
            cases he
            exact fun hlay => by rw [hl hlay]
        · refine ⟨fun h => h₁ h, fun h => ?_, h₃⟩
          obtain ⟨⟨i, hi, -⟩, -⟩ := h₂ h
          cases hi
      · rw [crun_bind_frun, flushBatch_empty core hb]
        rfl
    · simp only [Bool.or_false]
      refine ⟨fun he hv => ?_, fun _ ⟨_, h⟩ _ => by cases h⟩
      by_cases hflush : position ≥ input.stop
      · rw [dite_eq_left_of_eq_true (by simpa using hflush)]
        refine crun_bind_UL (SliceOk (Watched.spoiled fl)) flushBatch_usim he hv ?_
        intro res s' fl' l' h₁ h₂ h₃
        rcases res with ⟨result, span, location, stopAfter⟩ | ⟨⟩
        · cases result with
          | ok stop =>
            refine ⟨fun h => h₁ h, fun h => ?_, h₃⟩
            obtain ⟨⟨i, hi, e, he, -⟩, -⟩ := h₂ h
            cases hi
            cases he
          | error cause =>
            refine ⟨fun h => h₁ h, fun h => ?_, h₃⟩
            obtain ⟨⟨i, hi, e, he, hl⟩, -⟩ := h₂ h
            cases hi
            cases he
            exact fun hlay => by rw [hl hlay]
        · refine ⟨fun h => h₁ h, fun h => ?_, h₃⟩
          obtain ⟨⟨i, hi, -⟩, -⟩ := h₂ h
          cases hi
      · rw [dite_eq_right_of_eq_false (by simpa using hflush)]
        have hlt : position.toNat < input.stop.toNat := by
          simp only [ge_iff_le, USize.le_iff_toNat_le] at hflush
          omega
        try dsimp only
        refine crun_bind_UL (SliceOk (Watched.spoiled fl)) (lexStep_usim _ _ _ _ _ _ _) he hv ?_
        intro res s' fl' l' h₁ h₂ h₃
        rcases res with ⟨result, span, location, stopAfter⟩ | ⟨next, hnext⟩
        · cases result with
          | ok stop => exact ⟨fun h => h₁ h, fun h => (by
              obtain ⟨⟨i, hi, e, he, -⟩, -⟩ := h₂ h
              cases hi
              cases he), h₃⟩
          | error cause =>
            dsimp only
            cases hfl : Watched.errored fl' with
            | false =>
              rw [← h₃]
              refine (lexSliceRun_flag_lt input n position _ _ fl' l' ?_).1 hfl (h₁ hfl)
              simp only [runMeasure] at hn ⊢
              omega
            | true =>
              obtain ⟨⟨i, hi, e, he, hl⟩, hb⟩ := h₂ hfl
              cases hi
              cases he
              rw [(lexSliceRun_flag_lt input n position _ _ fl' l' (by
                simp only [runMeasure] at hn ⊢
                omega)).2 hfl ⟨_, rfl⟩ hb]
              exact ⟨fun h => absurd (h.symm.trans hfl) Bool.false_ne_true,
                fun _ hlay => by rw [hl hlay], h₃⟩
        · dsimp only
          cases hfl : Watched.errored fl' with
          | false =>
            rw [← h₃]
            refine (lexSliceRun_flag_lt input n next _ _ fl' l' ?_).1 hfl ?_
            · simp only [runMeasure] at hn ⊢
              omega
            · exact h₁ hfl
          | true =>
            obtain ⟨⟨i, hi, -⟩, -⟩ := h₂ hfl
            cases hi

theorem lexSliceRun_flag {floor : Option Nat} (input : Internal.CharClass.Input) (position : USize)
    (fnResult : Except (Failure (Option E)) (ControlFlow R))
    (core : {c : LexerCore // c.Bound floor 0}) (fl : F) (l)
    (he : Watched.errored fl = false) (hv : core.val.version = Watched.version fl) :
    SliceOk (Watched.spoiled fl) (crun (Internal.lexSliceRun input position fnResult core) fl l) :=
  (lexSliceRun_flag_lt input _ position fnResult core fl l (Nat.lt_succ_self _)).1 he hv

/-- Whether the result is an error: by the consumer's error `none`, as its cause says, if
`layout`. -/
def FailsBy {α β : Type} (cause : α → LexerErrorCause (Option E)) (layout : Bool) :
    Except α β → Prop
  | .error a => layout = true → cause a = .consumer none
  | .ok _ => False

/-- After a call's step: while nothing went wrong the versions agree, once the consumer answered
an error the step failed, by the consumer's error `none` if the consumer was handed whitespace or a
comment there, and whether the consumer was spoiled is `spoiled`. -/
def StepOk {α β : Type} (cause : α → LexerErrorCause (Option E)) (spoiled : Bool)
    (r : ((Except α β × LexerCore) × F) × σ) : Prop :=
  (Watched.errored r.1.2 = false → r.1.1.2.version = Watched.version r.1.2) ∧
    (Watched.errored r.1.2 = true → FailsBy cause (Watched.layout r.1.2) r.1.1.1) ∧
      Watched.spoiled r.1.2 = spoiled

theorem lexSliceFrom_flag_lt (input : Internal.CharClass.Input) (initialOffset : Nat) :
    ∀ (n floor : Nat) (hfloor : initialOffset ≤ floor + 1) (position : USize)
      (fnResult : Except (Failure (Option E)) (ControlFlow R))
      (held : Option (Span.Located R))
          (core : {c : LexerCore // c.Bound (some floor) 0})
      (fl : F) (l), fromMeasure input initialOffset floor < n →
      Watched.errored fl = false → core.val.version = Watched.version fl →
      StepOk Failure.cause (Watched.spoiled fl)
        (crun (Internal.lexSliceFrom input initialOffset floor hfloor position fnResult held core)
            fl l)
  | 0, _, _, _, _, _, _, _, _, hn, _, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, floor, hfloor, position, fnResult, held, core, fl, l, hn, he, hv => by
    rw [Internal.lexSliceFrom.eq_def, crun_bind]
    obtain ⟨h₁, h₂, h₃⟩ := lexSliceRun_flag input position fnResult core fl l he hv
    generalize crun (Internal.lexSliceRun input position fnResult core) fl l = r at h₁ h₂ h₃
    obtain ⟨⟨⟨exit, core'⟩, fl'⟩, l'⟩ := r
    dsimp only at h₁ h₂ h₃ ⊢
    cases exit with
    | done result =>
      refine ⟨h₁, fun h => ?_, h₃⟩
      have := h₂ h
      cases result with
      | error _ => exact this
      | ok _ => exact absurd this id
    | stopped stop location after =>
      cases hfl : Watched.errored fl' with
      | true => exact absurd (h₂ hfl) id
      | false =>
        have hafter := after floor rfl
        cases stop with
        | relex =>
          dsimp only
          split
          · rename_i hresumed
            rw [← h₃]
            refine lexSliceFrom_flag_lt input initialOffset n _ _ _ _ _ _ fl' l' ?_ hfl (h₁ hfl)
            simp only [fromMeasure] at hn ⊢
            omega
          · exact ⟨fun _ => h₁ hfl, fun h => absurd (h.symm.trans hfl) (by decide), h₃⟩
        | finished result =>
          dsimp only
          split
          · rename_i hresumed
            rw [← h₃]
            refine lexSliceFrom_flag_lt input initialOffset n _ _ _ _ _ _ fl' l' ?_ hfl (h₁ hfl)
            simp only [fromMeasure] at hn ⊢
            omega
          · exact ⟨fun _ => h₁ hfl, fun h => absurd (h.symm.trans hfl) (by decide), h₃⟩
        | discarded result =>
          dsimp only
          cases result with
          | some _ => exact ⟨fun _ => h₁ hfl, fun h => absurd (h.symm.trans hfl) (by decide), h₃⟩
          | none => exact ⟨fun _ => h₁ hfl, fun h => absurd (h.symm.trans hfl) (by decide), h₃⟩

/-- The run of an action on the lexer's state from it, the consumer's state and the monad's
state. -/
abbrev irun {α : Type} (f : InnerM F (StateM σ) α) (c : LexerCore)
    (fl : F) (l : σ) := ((f.run c).run fl).run l

theorem lexSliceInner_flag (input : Internal.CharClass.Input) (c : LexerCore) (fl : F) (l)
    (he : Watched.errored fl = false) (hv : c.version = Watched.version fl) :
    StepOk Failure.cause (Watched.spoiled fl) (irun (Internal.lexSliceInner input) c fl l) :=
  lexSliceFrom_flag_lt input _ _ _ _ _ _ _ _ fl l (Nat.lt_succ_self _) he hv

/-- An action that leaves the consumer's state and the monad's state as they are and keeps the
lexer's version. -/
def Inert {α : Type} (f : InnerM F (StateM σ) α) : Prop :=
  ∀ c fl l, (irun f c fl l).1.2 = fl ∧ (irun f c fl l).2 = l ∧
    (irun f c fl l).1.1.2.version = c.version

theorem irun_getThe_bind {α : Type} (k : LexerCore → InnerM F (StateM σ) α)
    (c : LexerCore) (fl : F) (l) :
    irun (getThe LexerCore >>= k) c fl l = irun (k c) c fl l := rfl

theorem irun_bind {α β : Type} (x : InnerM F (StateM σ) α)
    (k : α → InnerM F (StateM σ) β) (c : LexerCore) (fl : F) (l) :
    irun (x >>= k) c fl l =
      irun (k (irun x c fl l).1.1.1) (irun x c fl l).1.1.2 (irun x c fl l).1.2 (irun x c fl l).2 :=
  rfl

theorem irun_modifyThe (f : LexerCore → LexerCore) (c : LexerCore) (fl : F) (l : σ) :
    irun (modifyThe LexerCore f) c fl l = (((PUnit.unit, f c), fl), l) := rfl

theorem skipSlice_inert (slice : ByteSlice) (skip : RecoveryState) :
    Inert (Internal.skipSlice slice skip : InnerM F (StateM σ) (Option Nat)) := by
  intro c fl l
  unfold Internal.skipSlice
  rw [irun_getThe_bind]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · dsimp only
    split <;> exact ⟨rfl, rfl, rfl⟩

theorem failCall_inert (failure : Failure (Option E)) (atEnd : Bool) :
    Inert (Internal.failCall (Recovery.LexerRecovery.abandon (H := F)
        (m := StateM σ) Recovery.FailFast)
      failure atEnd : InnerM F (StateM σ) (LexerError (Option E))) := by
  intro c fl l
  unfold Internal.failCall
  rw [irun_getThe_bind]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- The error a failure turns into has the failure's cause. -/
theorem failCall_cause (failure : Failure (Option E)) (atEnd : Bool) (c fl l) :
    (irun (Internal.failCall (Recovery.LexerRecovery.abandon (H := F)
    (m := StateM σ) Recovery.FailFast)
      failure atEnd : InnerM F (StateM σ) (LexerError (Option E)))
      c fl l).1.1.1.cause = failure.cause := by
  unfold Internal.failCall
  rw [irun_getThe_bind]
  split
  · rfl
  · rfl

theorem irun_pure {α : Type} (a : α) (c : LexerCore) (fl : F) (l) :
    irun (Pure.pure a : InnerM F (StateM σ) α) c fl l = (((a, c), fl), l) := rfl

/-- An inert action, then the rest. -/
theorem irun_inert_bind {α β : Type} {x : InnerM F (StateM σ) α}
    (hx : Inert x) (k : α → InnerM F (StateM σ) β) (c fl l)
    (P : ((β × LexerCore) × F) × σ → Prop)
    (hk : ∀ a c', c'.version = c.version → P (irun (k a) c' fl l)) :
    P (irun (x >>= k) c fl l) := by
  rw [irun_bind]
  obtain ⟨h₁, h₂, h₃⟩ := hx c fl l
  rw [h₁, h₂]
  exact hk _ _ h₃

theorem lexFitting_flag (slice : ByteSlice) (h : slice.stop < USize.size) (c : LexerCore)
    (fl : F) (l) (he : Watched.errored fl = false) (hv : c.version = Watched.version fl) :
    StepOk LexerError.cause (Watched.spoiled fl) (irun
        (Internal.lexFitting (Recovery.LexerRecovery.abandon
      (H := F) (m := StateM σ) Recovery.FailFast) slice h) c fl l) := by
  unfold Internal.lexFitting
  rw [irun_bind]
  obtain ⟨h₁, h₂, h₃⟩ := lexSliceInner_flag (Internal.CharClass.Input.ofSlice slice h) c fl l he hv
  generalize irun
      (Internal.lexSliceInner (Internal.CharClass.Input.ofSlice slice h)) c fl l = r at h₁ h₂ h₃
  obtain ⟨⟨⟨res, c'⟩, fl'⟩, l'⟩ := r
  dsimp only at h₁ h₂ h₃ ⊢
  cases res with
  | ok held =>
    rw [irun_pure]
    exact ⟨h₁, fun h => absurd (h₂ h) id, h₃⟩
  | error failure =>
    rw [irun_bind]
    obtain ⟨e₁, e₂, e₃⟩ := failCall_inert failure false c' fl' l'
    have e₄ := failCall_cause failure false c' fl' l'
    generalize irun (Internal.failCall (Recovery.LexerRecovery.abandon (H := F) (m := StateM σ)
      Recovery.FailFast) failure false) c' fl' l' = q at e₁ e₂ e₃ e₄
    obtain ⟨⟨⟨err, c''⟩, fl''⟩, l''⟩ := q
    dsimp only at e₁ e₂ e₃ e₄
    subst e₁ e₂
    rw [irun_pure]
    exact ⟨fun h => e₃.trans (h₁ h), fun h hl => by rw [e₄]; exact h₂ h hl, h₃⟩

theorem lexSliceFitting_flag (slice : ByteSlice) (h : slice.stop < USize.size) (c : LexerCore)
    (fl : F) (l) (he : Watched.errored fl = false) (hv : c.version = Watched.version fl) :
    StepOk LexerError.cause (Watched.spoiled fl) (irun (Internal.lexSliceFitting
      (Recovery.LexerRecovery.abandon (H := F) (m := StateM σ) Recovery.FailFast)
      (Recovery.LexerRecovery.recover (H := F) (m := StateM σ) Recovery.FailFast) slice
          h)
      c fl l) := by
  unfold Internal.lexSliceFitting
  rw [irun_getThe_bind]
  split
  · rw [irun_pure]
    exact ⟨fun _ => hv, fun h => absurd (h.symm.trans he) (by decide), rfl⟩
  · rw [irun_getThe_bind]
    split
    · split
      · rw [irun_pure]
        exact ⟨fun _ => hv, fun h => absurd (h.symm.trans he) (by decide), rfl⟩
      · refine irun_inert_bind (skipSlice_inert _ _) _ c fl l
          (StepOk LexerError.cause (Watched.spoiled fl))
          fun skipped c' hc => ?_
        split
        · rw [irun_bind, irun_modifyThe]
          dsimp only
          rw [irun_getThe_bind]
          exact lexFitting_flag _ _ _ fl l he (hc.trans hv)
        · rw [irun_pure]
          exact ⟨fun _ => hc.trans hv, fun h => absurd (h.symm.trans he) (by decide), rfl⟩
    · exact lexFitting_flag _ _ _ fl l he hv

/-- A step of a call, then the rest. -/
theorem irun_bind_step {α β γ : Type} {cause : α → LexerErrorCause (Option E)}
    {x : InnerM F (StateM σ) (Except α β)}
    {k : Except α β → InnerM F (StateM σ) γ} {c : LexerCore}
    {fl : F} {l} {spoiled : Bool}
    (P : ((γ × LexerCore) × F) × σ → Prop)
    (hx : StepOk cause spoiled (irun x c fl l))
    (hk : ∀ res c' (fl' : F) l', (Watched.errored fl' = false → c'.version = Watched.version fl') →
      (Watched.errored fl' = true → FailsBy cause (Watched.layout fl') res) →
      Watched.spoiled fl' = spoiled →
      P (irun (k res) c' fl' l')) :
    P (irun (x >>= k) c fl l) := by
  rw [irun_bind]
  exact hk _ _ _ _ hx.1 hx.2.1 hx.2.2

theorem lexChunks_flag (slice : ByteSlice) (position : Nat)
    (held : Option (Span.Located R)) (c : LexerCore) (fl : F) (l)
    (he : Watched.errored fl = false) (hv : c.version = Watched.version fl) :
    StepOk LexerError.cause (Watched.spoiled fl) (irun (Internal.lexChunks
      (Recovery.LexerRecovery.abandon (H := F) (m := StateM σ) Recovery.FailFast)
      (Recovery.LexerRecovery.recover (H := F) (m := StateM σ) Recovery.FailFast) slice
      position held) c fl l) := by
  rw [Internal.lexChunks.eq_def]
  split
  · rename_i hlt
    dsimp only
    refine irun_bind_step (StepOk LexerError.cause (Watched.spoiled fl))
      (lexSliceFitting_flag _ _ c fl l he hv) ?_
    intro res c' fl' l' h₁ h₂ h₃
    cases res with
    | ok chunkHeld =>
      cases hfl : Watched.errored fl' with
      | true => exact absurd (h₂ hfl) id
      | false =>
        rw [← h₃]
        exact lexChunks_flag slice _ _ c' fl' l' hfl (h₁ hfl)
    | error err =>
      rw [irun_pure]
      exact ⟨h₁, h₂, h₃⟩
  · rw [irun_pure]
    exact ⟨fun _ => hv, fun h => absurd (h.symm.trans he) (by decide), rfl⟩
termination_by slice.size - position
decreasing_by simp only [Internal.CHUNK_SIZE] at *; omega

/-- On a slice, the step of the public call, run while nothing went wrong and with the versions
agreeing:
- if nothing went wrong after, the versions agree;
- if the consumer answered an error, the call fails, with the error `none` if the consumer was
  handed whitespace or a comment there;
- the consumer is not spoiled by it. -/
theorem lexSliceStep_flag (slice : ByteSlice) (c : LexerCore) (fl : F) (l)
    (he : Watched.errored fl = false) (hv : c.version = Watched.version fl) :
    StepOk LexerError.cause (Watched.spoiled fl) (irun (Internal.lexSliceStep
      (Recovery.LexerRecovery.abandon (H := F) (m := StateM σ) Recovery.FailFast)
      (Recovery.LexerRecovery.recover (H := F) (m := StateM σ) Recovery.FailFast) slice)
      c fl l) := by
  unfold Internal.lexSliceStep
  split
  · exact lexSliceFitting_flag _ _ c fl l he hv
  · exact lexChunks_flag _ _ _ c fl l he hv

/-! ## At the end of the input -/

omit [∀ b, Token.ConsumeFrom F (LexerCursor b) (StateM σ)] [Watched F σ R E] in
theorem frun_tryCatch {floor : Option Nat} {low : Nat} {α : Type} (x : FM F σ floor low α)
    (h : Interrupted R (Option E) floor → FM F σ floor low α)
    (s fl l) :
    frun (tryCatch x h) s fl l =
      match frun x s fl l with
      | (((.ok a, s'), fl'), l') => (((.ok a, s'), fl'), l')
      | (((.error e, s'), fl'), l') => frun (h e) s' fl' l' := by
  simp only [frun, ExceptT.run, tryCatch, tryCatchThe, MonadExcept.tryCatch,
    MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.mk, StateT.run_bind]
  generalize StateT.run ((StateT.run x s).run fl) l = r
  obtain ⟨⟨⟨r, s'⟩, fl'⟩, l'⟩ := r
  cases r <;> rfl

/-- A failing action with a handler that throws the consumer's errors again. -/
theorem _root_.BSmtLib.Facts.Proofs.Reader.Param.Unary.UL.tryCatch {floor : Option Nat} {low : Nat}
    {α : Type} {x : FM F σ floor low α}
    {h : Interrupted R (Option E) floor → FM F σ floor low α}
    (hx : UL x) (hh : ∀ i, UL (h i))
    (hrethrow : ∀ i e, i.result = .error (.consumer e) → h i = MonadExcept.throw i) :
    UL (tryCatch x h) := by
  intro s fl l he hv
  rw [UnaryCalls.frun_tryCatch]
  obtain ⟨h₁, h₂, h₃⟩ := hx s fl l he hv
  rcases hrun : frun x s fl l with ⟨⟨⟨r, s'⟩, fl'⟩, l'⟩
  rw [hrun] at h₁ h₂ h₃
  cases r with
  | ok a => exact ⟨h₁, h₂, h₃⟩
  | error i =>
    dsimp only
    cases hfl : Watched.errored fl' with
    | false =>
      obtain ⟨k₁, k₂, k₃⟩ := hh i s' fl' l' hfl (h₁ hfl)
      exact ⟨k₁, k₂, k₃.trans h₃⟩
    | true =>
      obtain ⟨⟨j, hj, e, hc, hl⟩, hb⟩ := h₂ hfl
      cases hj
      rw [hrethrow i e hc, frun_throw]
      exact ⟨fun h => absurd (h.symm.trans hfl) (by decide), fun _ => ⟨⟨i, rfl, e, hc, hl⟩, hb⟩,
        h₃⟩

/-- After the end of the input: once the consumer answered an error, the call failed, by the
consumer's error `none` if the consumer was handed whitespace or a comment there; and whether the
consumer was spoiled is `spoiled`. -/
def EofOk {α β : Type} (cause : α → LexerErrorCause (Option E)) (spoiled : Bool)
    (r : ((Except α β × LexerCore) × F) × σ) : Prop :=
  (Watched.errored r.1.2 = true → FailsBy cause (Watched.layout r.1.2) r.1.1.1) ∧
    Watched.spoiled r.1.2 = spoiled

theorem lexEofInner_flag (c : LexerCore) (fl : F) (l) (he : Watched.errored fl = false)
    (hv : c.version = Watched.version fl) :
    EofOk Failure.cause (Watched.spoiled fl) (irun (Internal.lexEofInner (H := F) (m := StateM σ)
      (R := R) (E := Option E)) c fl l) := by
  show EofOk Failure.cause (Watched.spoiled fl) (crun (Internal.lexEofInner c) fl l)
  unfold Internal.lexEofInner
  dsimp only
  refine crun_bind_UL (EofOk Failure.cause (Watched.spoiled fl)) ?_ he hv ?_
  · refine UL.bind (UL.tryCatch ?_ ?_ ?_) fun _ => ?_
    · usim
    · intro i
      usim
    · intro i e hi
      simp only [hi]
    · usim
  · intro res s' fl' l' h₁ h₂ h₃
    rcases res with ⟨r, location, stopAfter⟩ | u
    · cases r with
      | error cause =>
        refine ⟨fun hfl => ?_, h₃⟩
        obtain ⟨⟨i, hi, e, hc, hl⟩, -⟩ := h₂ hfl
        cases hi
        cases hc
        exact fun hlay => congrArg LexerErrorCause.consumer (hl hlay)
      | ok stop =>
        refine ⟨fun hfl => ?_, by rcases stop with _ | _ | (_ | _) <;> exact h₃⟩
        obtain ⟨⟨i, hi, e, hc, -⟩, -⟩ := h₂ (by
          revert hfl
          rcases stop with _ | _ | (_ | _) <;> exact id)
        cases hi
        cases hc
    · refine ⟨fun hfl => ?_, h₃⟩
      obtain ⟨⟨i, hi, -⟩, -⟩ := h₂ hfl
      cases hi

theorem executeStep_flag (step : InnerM F (StateM σ)
      (Except (Failure (Option E)) (ControlFlow R)))
    (c : LexerCore) (fl : F) (l) {spoiled : Bool}
    (hstep : EofOk Failure.cause spoiled (irun step c fl l)) :
    EofOk Failure.cause spoiled (irun (Internal.executeStep step) c fl l) := by
  unfold Internal.executeStep
  rw [irun_bind]
  generalize irun step c fl l = r at hstep ⊢
  obtain ⟨⟨⟨res, c'⟩, fl'⟩, l'⟩ := r
  rcases res with f | (_ | v)
  · exact ⟨hstep.1, hstep.2⟩
  · exact ⟨fun h => absurd (hstep.1 h) id, hstep.2⟩
  · exact ⟨fun h => absurd (hstep.1 h) id, hstep.2⟩

/-- The inner step at the end of the input, then what follows it: a success goes on without
failing and without touching the consumer, a failure gives an error of the same cause without
touching it. -/
theorem eofBind_flag
    (k : Except (Failure (Option E)) (ControlFlow (Span.Located R)) →
      InnerM F (StateM σ)
        (Except (LexerError (Option E)) (ControlFlow (Span.Located R))))
    (hok : ∀ flow c fl l, (irun (k (.ok flow)) c fl l).1.2 = fl ∧
      Flagged.isError (irun (k (.ok flow)) c fl l).1.1.1 = false)
    (herr : ∀ f c fl l, (irun (k (.error f)) c fl l).1.2 = fl ∧
      ∃ err, (irun (k (.error f)) c fl l).1.1.1 = .error err ∧ err.cause = f.cause)
    (c : LexerCore) (fl : F) (l) (he : Watched.errored fl = false)
    (hv : c.version = Watched.version fl) :
    EofOk LexerError.cause (Watched.spoiled fl) (irun
        (Internal.executeStep Internal.lexEofInner >>= k) c fl l) := by
  rw [irun_bind]
  have h₁ := executeStep_flag Internal.lexEofInner c fl l (lexEofInner_flag c fl l he hv)
  generalize irun (Internal.executeStep Internal.lexEofInner) c fl l = r at h₁ ⊢
  obtain ⟨⟨⟨res, c'⟩, fl'⟩, l'⟩ := r
  rcases res with f | flow
  · dsimp only
    obtain ⟨h₂, err, h₃, h₄⟩ := herr f c' fl' l'
    refine ⟨fun h => ?_, ?_⟩
    · rw [h₃]
      rw [h₂] at h ⊢
      intro hl
      rw [h₄]
      exact h₁.1 h hl
    · rw [h₂]
      exact h₁.2
  · obtain ⟨h₂, h₃⟩ := hok flow c' fl' l'
    refine ⟨fun h => ?_, ?_⟩
    · rw [h₂] at h
      exact absurd (h₁.1 h) id
    · rw [h₂]
      exact h₁.2

theorem irun_recover_bind {β : Type} (location : Span.Location)
    (k : PUnit → InnerM F (StateM σ) β) (c : LexerCore) (fl : F) (l) :
    irun (liftM (Recovery.LexerRecovery.recover (H := F)
        (m := StateM σ) Recovery.FailFast
      location) >>= k) c fl l = irun (k ()) c fl l := rfl

/-- At the end of the input, the step of the public call, run while nothing went wrong and with
the versions agreeing: if the consumer answered an error, the call fails, with the error `none` if
the consumer was handed whitespace or a comment there; the consumer is not spoiled by it. -/
theorem lexEofStep_flag (c : LexerCore) (fl : F) (l) (he : Watched.errored fl = false)
    (hv : c.version = Watched.version fl) :
    EofOk LexerError.cause (Watched.spoiled fl) (irun (Internal.lexEofStep (R := R)
      (E := Option E)
      (Recovery.LexerRecovery.abandon (H := F) (m := StateM σ) Recovery.FailFast)
      (Recovery.LexerRecovery.recover (H := F) (m := StateM σ) Recovery.FailFast)) c fl
          l) := by
  unfold Internal.lexEofStep
  rw [irun_getThe_bind]
  dsimp only
  split
  · rw [irun_bind, irun_modifyThe]
    dsimp only
    rw [irun_getThe_bind, irun_recover_bind]
    refine eofBind_flag _ (fun _ _ _ _ => ⟨rfl, rfl⟩) (fun _ _ _ _ => ⟨rfl, _, rfl, rfl⟩) _ fl l
      he ?_
    exact hv
  · refine eofBind_flag _ (fun _ _ _ _ => ⟨rfl, rfl⟩) (fun f c fl l => ?_) _ fl l he hv
    dsimp only
    rw [irun_bind]
    exact ⟨(failCall_inert _ _ c fl l).1, _, rfl, failCall_cause f true c fl l⟩

end

end BSmtLib.Facts.Proofs.Reader.Param.UnaryCalls

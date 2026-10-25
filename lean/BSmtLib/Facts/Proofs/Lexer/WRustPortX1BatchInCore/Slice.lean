module

public import BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Steps
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The loops over a slice

The loops over a slice (`lexSliceRun`, `lexSliceFrom`) are the same code over the steps and the
hand-over of the batch shown alike before. They run in the consumer's monad and pass the lexer
states along as values, which correspond, with the same arrays of contents of the batches
(`CoreRelB`); the two loops are coupled (`Couple`) step by step.
-/

open BSmtLib.Lexer.Cursor (LexerCursor)

namespace BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Slice

open BSmtLib.Lexer.Internal (BATCH_CAPACITY Interrupted Failure Stop)
open BSmtLib.Lexer.Internal.WRustPort (Ops)
open BSmtLib.Facts.Proofs.Lexer.Simulation BSmtLib.Facts.Proofs.Lexer.Simulation.Batch
open BSmtLib.Facts.Proofs.Lexer.Simulation.Relation
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Ops
open BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Steps

/-- The two lexer states correspond, with the same arrays of contents of the batches. -/
def CoreRelB (w x : Core) : Prop :=
  Core.CoreRel w x ∧ w.batch.bytes = x.batch.bytes

theorem coreRel_advance {w x : Core} (h : Core.CoreRel w x) (position : Nat) :
    Core.CoreRel (w.advance position) (x.advance position) :=
  { h with
    offset := by
      simp only [Lexer.Internal.WRustPort.LexerCore.advance,
          Lexer.Internal.WRustPort.LexerCore.offsetAt,
        h.offset, h.base]
    base := rfl }

theorem coreRel_resumeAt {w x : Core} (h : Core.CoreRel w x) (location : Span.Location)
    (position : Nat) : Core.CoreRel (w.resumeAt location position) (x.resumeAt location position) :=
  { h with
    offset := rfl, base := rfl, line := rfl, lineStart := rfl, state := rfl
    tokenContent := by
      simp only [Lexer.Internal.WRustPort.LexerCore.resumeAt]; exact ContentAgree.clear _ _
    tokenStart := rfl, batch := agree_clear _ _ _ _, capacity := Core.zero_lt_capacity }

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Token.Consume H R E]
  [∀ batch, Token.ConsumeFrom H (LexerCursor batch) m]
  {o₁ o₂ : Ops H m R E}
  {LRel : Ops.Locals H m R E (self := o₁) → Ops.Locals H m R E (self := o₂) → Nat → Nat → Prop}

/-- How the two loops over a slice end, alike. -/
def ExitRel {floor : Option Nat} :
    Lexer.Internal.WRustPort.SliceExit R E floor → Lexer.Internal.WRustPort.SliceExit R E floor →
        Prop
  | .done r, .done r' => r = r'
  | .stopped s l _, .stopped s' l' _ => s = s' ∧ l = l'
  | _, _ => False

/-- The first batch has no tokens where its loop over a slice is done. -/
def DoneEmpty {floor : Option Nat} : Lexer.Internal.WRustPort.SliceExit R E floor → Core → Prop
  | .done _, c => c.batch.len = 0
  | .stopped .., _ => True

/-- What the two loops over a slice give back correspond. -/
def SliceRel {floor : Option Nat}
    (a b : Lexer.Internal.WRustPort.SliceExit R E floor × {c : Core // c.Bound floor 0}) : Prop :=
  ExitRel a.1 b.1 ∧ CoreRelB a.2.val b.2.val ∧ DoneEmpty a.1 a.2.val

/-- What the steps give back correspond. -/
def StepRel {floor : Option Nat} {lo lo' start : Nat}
    (a : Except (Interrupted R E floor) {next : Nat // start < next} ×
      {c : Core // c.Bound floor lo})
    (b : Except (Interrupted R E floor) {next : Nat // start < next} ×
      {c : Core // c.Bound floor lo'}) : Prop :=
  (match a.1, b.1 with
    | .ok n, .ok n' => n.val = n'.val
    | .error e, .error e' => e = e'
    | _, _ => False) ∧ CoreRelB a.2.val b.2.val

variable {floor : Option Nat}

omit [∀ batch, Token.ConsumeFrom H (LexerCursor batch) m] in
/-- A step of the two runs from states that correspond, with the same arrays of contents, in the
same lexer state. -/
theorem lexStep_couple (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (lo lo' : Nat) (elo : lo = lo')
    (state state' : Lexer.Internal.Helpers.LexerState) (estate : state = state')
    (tokenStart tokenStart' : Span.Location) (etoken : tokenStart = tokenStart') (base base' : Nat)
    (ebase : base = base') (hp hp') (s : {c : Core // c.Bound floor lo})
    (t : {c : Core // c.Bound floor lo'}) (hst : CoreRelB s.val t.val) :
    Couple (StepRel (R := R) (E := E))
      ((Lexer.Internal.WRustPort.lexStep (ops := o₁) (H := H) (m := m)
          (low := lo) input start hstart
        state tokenStart base hp).run.run s)
      ((Lexer.Internal.WRustPort.lexStep (ops := o₂)
          (low := lo') input start hstart state' tokenStart' base'
        hp').run.run t) := by
  subst elo estate etoken ebase
  refine Couple.mono (fun a b hab => ?_)
    (SimR.couple (lexStep_sim ho input start hstart state tokenStart base hp)
      ⟨hst.1, fun _ => hst.2⟩)
  obtain ⟨r, c⟩ := a
  obtain ⟨r', c'⟩ := b
  cases r <;> cases r' <;> simp only [GoodR'] at hab
  · exact ⟨hab.1, hab.2.1, hab.2.2 rfl⟩
  · exact ⟨hab.1, hab.2.1, hab.2.2 rfl⟩

/-- The measure of the loop over a slice: the bytes left, and whether an error is pending. -/
def runMeasure (input : ByteSlice) (position : Nat)
    (fnResult : Except (Failure E) (ControlFlow R)) : Nat :=
  2 * (input.size - position) + match fnResult with
    | .ok _ => 1
    | .error _ => 0

omit [∀ batch, Token.ConsumeFrom H (LexerCursor batch) m] in
theorem lexSliceRun_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) :
    ∀ k position (fnResult : Except (Failure E) (ControlFlow R)),
      runMeasure input position fnResult = k →
      ∀ (w x : {c : Core // c.Bound floor 0}), CoreRelB w.val x.val →
      Couple SliceRel
        (Lexer.Internal.WRustPort.lexSliceRun (ops := o₁) (H := H)
            (m := m) input position fnResult w)
        (Lexer.Internal.WRustPort.lexSliceRun (ops := o₂) input position fnResult x) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro position fnResult hk w x hwx
  rw [Lexer.Internal.WRustPort.lexSliceRun.eq_def (ops := o₁),
    Lexer.Internal.WRustPort.lexSliceRun.eq_def (ops := o₂)]
  dsimp only
  refine Couple.dite (fun hflush => ?_) fun hflush => ?_
  · refine Couple.bind (SimR.couple
      (ho.flushBatch (strict := true) w.val.line w.val.lineStart)
      ⟨⟨hwx.1, rfl, rfl⟩, fun _ => hwx.2⟩) fun a b hab => ?_
    obtain ⟨r, c⟩ := a
    obtain ⟨r', c'⟩ := b
    cases r <;> cases r' <;> simp only [GoodR'] at hab
    · obtain ⟨rfl, ⟨hcr, hby⟩, hlen⟩ := hab
      rename_i i
      obtain ⟨result, span, location, stopAfter⟩ := i
      cases result with
      | ok stop => exact Couple.pure ⟨⟨rfl, rfl⟩, ⟨hcr, hby rfl⟩, trivial⟩
      | error cause => exact Couple.pure ⟨rfl, ⟨hcr, hby rfl⟩, hlen⟩
    · exact Couple.pure ⟨rfl, ⟨hab.1.1.1, hab.2 rfl⟩, hab.1.2⟩
  · have hok : ∃ v, fnResult = .ok v := by
      cases fnResult with
      | ok v => exact ⟨v, rfl⟩
      | error => simp at hflush
    have hpos : position < input.size := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hflush
      omega
    refine Couple.bind (lexStep_couple ho input position hpos _ _ hwx.1.offset _ _
      hwx.1.state _ _ hwx.1.tokenStart _ _ hwx.1.base _ _ _ _ hwx) fun a b hab => ?_
    obtain ⟨r, c⟩ := a
    obtain ⟨r', c'⟩ := b
    obtain ⟨hr, hcr, hby⟩ := hab
    cases r with
    | ok n =>
      cases r' with
      | ok n' =>
        obtain ⟨next, hnext⟩ := n
        obtain ⟨next', hnext'⟩ := n'
        simp only at hr
        subst hr
        obtain ⟨v, rfl⟩ := hok
        refine ih _ ?_ next _ rfl _ _ ⟨coreRel_advance hcr next, hby⟩
        subst hk
        simp only [runMeasure]
        omega
      | error => exact hr.elim
    | error e =>
      cases r' with
      | ok => exact hr.elim
      | error e' =>
        simp only at hr
        subst hr
        obtain ⟨result, span, location, stopAfter⟩ := e
        cases result with
        | ok stop => exact Couple.pure ⟨⟨rfl, rfl⟩, ⟨hcr, hby⟩, trivial⟩
        | error cause =>
          obtain ⟨v, rfl⟩ := hok
          refine ih _ ?_ position _ rfl _ _ ⟨hcr, hby⟩
          subst hk
          simp only [runMeasure]
          omega

/-- What the two loops over the stops in a slice give back correspond: the same result, and
states that correspond with batches without tokens. -/
def FromRel (a b : Except (Failure E) (Option (Span.Located R)) × Core) : Prop :=
  a.1 = b.1 ∧ Core.CoreRel a.2 b.2 ∧ a.2.batch.len = 0

omit [∀ batch, Token.ConsumeFrom H (LexerCursor batch) m] in
theorem lexSliceFrom_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (initialOffset : Nat) :
    ∀ k (floor : Nat), input.size + 1 - (floor + 1 - initialOffset) = k →
      ∀ hfloor position (fnResult : Except (Failure E) (ControlFlow R))
      (held : Option (Span.Located R))
      (w x : {c : Core // c.Bound (some floor) 0}), CoreRelB w.val x.val →
      Couple FromRel
        (Lexer.Internal.WRustPort.lexSliceFrom (ops := o₁) (H := H)
            (m := m) input initialOffset floor
          hfloor position fnResult held w)
        (Lexer.Internal.WRustPort.lexSliceFrom (ops := o₂) input initialOffset floor hfloor position
          fnResult held x) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro floor hk hfloor position fnResult held w x hwx
  rw [Lexer.Internal.WRustPort.lexSliceFrom.eq_def (ops := o₁),
    Lexer.Internal.WRustPort.lexSliceFrom.eq_def (ops := o₂)]
  dsimp only
  refine Couple.bind (lexSliceRun_sim ho input _ position fnResult rfl w x hwx)
    fun a b hab => ?_
  obtain ⟨e, c⟩ := a
  obtain ⟨e', c'⟩ := b
  obtain ⟨hex, hcr, hdone⟩ := hab
  cases e with
  | done r =>
    cases e' with
    | done r' =>
      simp only [ExitRel] at hex
      subst hex
      exact Couple.pure ⟨rfl, hcr.1, hdone⟩
    | stopped => exact hex.elim
  | stopped stop location after =>
    cases e' with
    | done => exact hex.elim
    | stopped stop' location' after' =>
      obtain ⟨rfl, rfl⟩ := hex
      have hafter := after floor rfl
      have hres := coreRel_resumeAt hcr.1 location (location.offset - initialOffset)
      have hby : (c.val.resumeAt location (location.offset - initialOffset)).batch.bytes =
          (c'.val.resumeAt location (location.offset - initialOffset)).batch.bytes := by
        simp only [Lexer.Internal.WRustPort.LexerCore.resumeAt, Token.Internal.TokenBatch.clear]
        exact hcr.2
      dsimp only
      cases stop with
      | relex =>
        refine Couple.dite (fun hres' => ?_) fun _ => ?_
        · refine ih _ ?_ location.offset rfl _ _ _ _ _ _ ⟨hres, hby⟩
          subst hk
          omega
        · exact Couple.pure ⟨rfl, hres, rfl⟩
      | finished result =>
        refine Couple.dite (fun hres' => ?_) fun _ => ?_
        · refine ih _ ?_ location.offset rfl _ _ _ _ _ _ ⟨{ hres with holding := rfl }, hby⟩
          subst hk
          omega
        · exact Couple.pure ⟨rfl, { hres with holding := rfl }, rfl⟩
      | discarded result =>
        cases result with
        | some result =>
          exact Couple.pure ⟨rfl, { hres with discardedFrom := rfl, holding := rfl }, rfl⟩
        | none => exact Couple.pure ⟨rfl, { hres with discardedFrom := rfl }, rfl⟩

omit [∀ batch, Token.ConsumeFrom H (LexerCursor batch) m] in
/-- `lexSliceFrom_sim` with the offsets of the two runs given by equations. -/
theorem lexSliceFrom_sim' (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice)
    (initialOffset initialOffset' : Nat) (ei : initialOffset = initialOffset') (floor floor' : Nat)
    (ef : floor = floor') (hfloor hfloor') (position : Nat)
    (fnResult : Except (Failure E) (ControlFlow R)) (held : Option (Span.Located R))
    (w : {c : Core // c.Bound (some floor) 0})
    (x : {c : Core // c.Bound (some floor') 0}) (hwx : CoreRelB w.val x.val) :
    Couple FromRel
      (Lexer.Internal.WRustPort.lexSliceFrom (ops := o₁) (H := H) (m := m) input initialOffset floor
        hfloor position fnResult held w)
      (Lexer.Internal.WRustPort.lexSliceFrom (ops := o₂) input initialOffset' floor' hfloor'
          position
        fnResult held x) := by
  subst ei ef
  exact lexSliceFrom_sim ho input initialOffset _ floor rfl hfloor position fnResult held w x hwx

omit [∀ batch, Token.ConsumeFrom H (LexerCursor batch) m] in
theorem lexSliceInner_sim (ho : OpsSim o₁ o₂ LRel) (input : ByteSlice) (w x : Core)
    (hwx : Core.CoreRel w x) :
    Couple FromRel (Lexer.Internal.WRustPort.lexSliceInner (ops := o₁) (H := H) (m := m) input w)
      (Lexer.Internal.WRustPort.lexSliceInner (ops := o₂) input x) := by
  unfold Lexer.Internal.WRustPort.lexSliceInner
  dsimp only
  exact lexSliceFrom_sim' ho input _ _ hwx.offset _ _ (by rw [hwx.offset]) _ _ _ _ _ _ _
    ⟨{ hwx with
      base := rfl, batch := agree_of_len_zero rfl rfl, capacity := Core.zero_lt_capacity }, rfl⟩

end

end BSmtLib.Facts.Proofs.Lexer.WRustPortX1BatchInCore.Slice

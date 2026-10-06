import BSmtLib.Proofs.WRustPortX1BatchInCore.Steps

/-!
# The loops over a slice

The loops over a slice of the two lexers (`lexSliceRun`, `lexSliceFrom`) are the same code over
the steps and the hand-over of the batch shown alike before. They run in the consumer's monad
and pass the lexer states along as values, which correspond, with the same arrays of contents of
the batches (`CoreRelB`); the two loops are coupled (`Couple`) step by step.
-/

namespace BSmtLib.Proofs.WRustPortX1BatchInCore

open BSmtLib.Proofs.Simulation (M runM)
open BSmtLib.Lexer (BATCH_CAPACITY Interrupted Failure Stop)

/-- The two lexer states correspond, with the same arrays of contents of the batches. -/
def CoreRelB (w : WCore) (x : XCore) : Prop :=
  CoreRel w x ∧ w.batch.bytes = x.batch.bytes

theorem coreRel_advance {w : WCore} {x : XCore} (h : CoreRel w x) (position : Nat) :
    CoreRel (w.advance position) (x.advance position) :=
  { h with
    offset := by
      simp only [Lexer.WRustPort.LexerCore.advance, Lexer.X1BatchInCore.LexerCore.advance,
        Lexer.WRustPort.LexerCore.offsetAt, Lexer.X1BatchInCore.LexerCore.offsetAt, h.offset,
        h.base]
    base := rfl }

theorem coreRel_resumeAt {w : WCore} {x : XCore} (h : CoreRel w x) (location : Location)
    (position : Nat) : CoreRel (w.resumeAt location position) (x.resumeAt location position) :=
  { h with
    offset := rfl, base := rfl, line := rfl, lineStart := rfl, state := rfl, tokenContent := rfl
    tokenStart := rfl, batch := agree_clear _ _ _ _, capacity := zero_lt_capacity }

section

variable {H : Type} {m : Type → Type} {R E : Type} [Monad m] [LawfulMonad m] [Consume H m R E]

/-- How the two loops over a slice end, alike. -/
def ExitRel {floor : Option Nat} :
    Lexer.WRustPort.SliceExit R E floor → Lexer.X1BatchInCore.SliceExit R E floor → Prop
  | .done r, .done r' => r = r'
  | .stopped s l _, .stopped s' l' _ => s = s' ∧ l = l'
  | _, _ => False

/-- The Rust port's batch has no tokens where its loop over a slice is done. -/
def DoneEmpty {floor : Option Nat} : Lexer.WRustPort.SliceExit R E floor → WCore → Prop
  | .done _, c => c.batch.len = 0
  | .stopped .., _ => True

/-- What the two loops over a slice give back correspond. -/
def SliceRel {floor : Option Nat}
    (a : Lexer.WRustPort.SliceExit R E floor × {c : WCore // c.Bound floor 0})
    (b : Lexer.X1BatchInCore.SliceExit R E floor × {c : XCore // c.Bound floor 0}) : Prop :=
  ExitRel a.1 b.1 ∧ CoreRelB a.2.val b.2.val ∧ DoneEmpty a.1 a.2.val

/-- What the steps give back correspond. -/
def StepRel {floor : Option Nat} {lo lo' start : Nat}
    (a : Except (Interrupted R E floor) {next : Nat // start < next} ×
      {c : WCore // c.Bound floor lo})
    (b : Except (Interrupted R E floor) {next : Nat // start < next} ×
      {c : XCore // c.Bound floor lo'}) : Prop :=
  (match a.1, b.1 with
    | .ok n, .ok n' => n.val = n'.val
    | .error e, .error e' => e = e'
    | _, _ => False) ∧ CoreRelB a.2.val b.2.val

variable {floor : Option Nat}

/-- A step of the two lexers from states that correspond, with the same arrays of contents, in
the same lexer state. The bounds of the states are given by the offsets of the two states,
which are equal. -/
theorem lexStep_couple (hcons : ConsumesAlike H m R E) (input : ByteSlice) (start : Nat)
    (hstart : start < input.size) (lo lo' : Nat) (elo : lo = lo')
    (state state' : Lexer.LexerState) (estate : state = state') (tokenStart tokenStart' : Location)
    (etoken : tokenStart = tokenStart') (base base' : Nat) (ebase : base = base') (hp hp')
    (s : {c : WCore // c.Bound floor lo})
    (t : {c : XCore // c.Bound floor lo'}) (hst : CoreRelB s.val t.val) :
    Couple (StepRel (R := R) (E := E))
      ((Lexer.WRustPort.lexStep (H := H) (m := m) (low := lo) input start hstart state tokenStart
        base hp).run.run s)
      ((Lexer.X1BatchInCore.lexStep (low := lo') input start hstart state' tokenStart' base'
        hp').run.run t) := by
  subst elo estate etoken ebase
  refine Couple.mono (fun a b hab => ?_)
    (SimR.couple (lexStep_sim hcons input start hstart state tokenStart base hp hp')
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

theorem lexSliceRun_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) :
    ∀ k position (fnResult : Except (Failure E) (ControlFlow R)),
      runMeasure input position fnResult = k →
      ∀ (w : {c : WCore // c.Bound floor 0}) (x : {c : XCore // c.Bound floor 0}),
      CoreRelB w.val x.val →
      Couple SliceRel (Lexer.WRustPort.lexSliceRun (H := H) (m := m) input position fnResult w)
        (Lexer.X1BatchInCore.lexSliceRun input position fnResult x) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro position fnResult hk w x hwx
  rw [Lexer.WRustPort.lexSliceRun.eq_def, Lexer.X1BatchInCore.lexSliceRun.eq_def]
  dsimp only
  refine Couple.dite (fun hflush => ?_) fun hflush => ?_
  · refine Couple.bind (SimR.couple
      (flushBatch_simZ (strict := true) hcons w.val.line w.val.lineStart)
      ⟨⟨hwx.1, rfl, rfl⟩, fun _ => hwx.2⟩) fun a b hab => ?_
    obtain ⟨r, c⟩ := a
    obtain ⟨r', c'⟩ := b
    cases r <;> cases r' <;> simp only [GoodR'] at hab
    · obtain ⟨rfl, ⟨hcr, hby⟩, hlen⟩ := hab
      rename_i i
      obtain ⟨result, location, stopAfter⟩ := i
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
    refine Couple.bind (lexStep_couple hcons input position hpos _ _ hwx.1.offset _ _
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
        obtain ⟨result, location, stopAfter⟩ := e
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
def FromRel (a : Except (Failure E) (ControlFlow R) × WCore)
    (b : Except (Failure E) (ControlFlow R) × XCore) : Prop :=
  a.1 = b.1 ∧ CoreRel a.2 b.2 ∧ a.2.batch.len = 0

theorem lexSliceFrom_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice)
    (initialOffset : Nat) :
    ∀ k (floor : Nat), input.size + 1 - (floor + 1 - initialOffset) = k →
      ∀ hfloor position (fnResult : Except (Failure E) (ControlFlow R))
      (w : {c : WCore // c.Bound (some floor) 0}) (x : {c : XCore // c.Bound (some floor) 0}),
      CoreRelB w.val x.val →
      Couple FromRel
        (Lexer.WRustPort.lexSliceFrom (H := H) (m := m) input initialOffset floor hfloor position
          fnResult w)
        (Lexer.X1BatchInCore.lexSliceFrom input initialOffset floor hfloor position fnResult
          x) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro floor hk hfloor position fnResult w x hwx
  rw [Lexer.WRustPort.lexSliceFrom.eq_def, Lexer.X1BatchInCore.lexSliceFrom.eq_def]
  dsimp only
  refine Couple.bind (lexSliceRun_sim hcons input _ position fnResult rfl w x hwx)
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
      dsimp only
      cases stop with
      | relex =>
        refine Couple.dite (fun hres => ?_) fun _ => ?_
        · refine ih _ ?_ location.offset rfl _ _ _ _ _ ⟨coreRel_resumeAt hcr.1 _ _, hcr.2⟩
          subst hk
          omega
        · exact Couple.pure ⟨rfl, coreRel_resumeAt hcr.1 _ _, rfl⟩
      | finished result => exact Couple.pure ⟨rfl, coreRel_resumeAt hcr.1 _ _, rfl⟩

/-- `lexSliceFrom_sim` with the offsets of the two lexers given by equations. -/
theorem lexSliceFrom_sim' (hcons : ConsumesAlike H m R E) (input : ByteSlice)
    (initialOffset initialOffset' : Nat) (ei : initialOffset = initialOffset') (floor floor' : Nat)
    (ef : floor = floor') (hfloor hfloor') (position : Nat)
    (fnResult : Except (Failure E) (ControlFlow R)) (w : {c : WCore // c.Bound (some floor) 0})
    (x : {c : XCore // c.Bound (some floor') 0}) (hwx : CoreRelB w.val x.val) :
    Couple FromRel
      (Lexer.WRustPort.lexSliceFrom (H := H) (m := m) input initialOffset floor hfloor position
        fnResult w)
      (Lexer.X1BatchInCore.lexSliceFrom input initialOffset' floor' hfloor' position fnResult
        x) := by
  subst ei ef
  exact lexSliceFrom_sim hcons input initialOffset _ floor rfl hfloor position fnResult w x hwx

theorem lexSliceInner_sim (hcons : ConsumesAlike H m R E) (input : ByteSlice) (w : WCore)
    (x : XCore) (hwx : CoreRel w x) :
    Couple FromRel (Lexer.WRustPort.lexSliceInner (H := H) (m := m) input w)
      (Lexer.X1BatchInCore.lexSliceInner input x) := by
  unfold Lexer.WRustPort.lexSliceInner Lexer.X1BatchInCore.lexSliceInner
  dsimp only
  exact lexSliceFrom_sim' hcons input _ _ hwx.offset _ _ (by rw [hwx.offset]) _ _ _ _ _ _
    ⟨{ hwx with
      base := rfl, batch := agree_of_len_zero rfl rfl, capacity := zero_lt_capacity }, rfl⟩

end

end BSmtLib.Proofs.WRustPortX1BatchInCore

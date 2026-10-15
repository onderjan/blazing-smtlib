module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.LexStep
import all BSmtLib.Lexer.Internal.WRustPort

@[expose] public section

/-!
# The Rust port's loop over a slice, up to a stop of the consumer, with every consumer

`sliceRun_ok`: the loop `lexSliceRun` over a slice, from a lexer state that is the naive lexer's
pure state at an index, with a batch that holds lexemes, ends as the outcome of the naive lexer's
run from there says (`SliceOut`): with the batch handed over, in the pure state at the end of
the slice; with a lexical error where the run fails; or where the consumer stops, with the
interruption of the stop (`ExitMatches`). It is proved by induction on the bytes left, with
`lexStep_wp` for each step; after a lexical error the loop hands over the batch as it was left
(`sliceRun_error`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Slice

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Batch
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Feed
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.LexStep
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Model
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Push BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Step
open BSmtLib.Lexer.Error BSmtLib.Lexer.Internal.VNaive

section

variable {C : BSmtLibSpec.Lexer.Consumer} {floor : Option Nat}

theorem answering_eq' (a b : Answering C) : a = b := by
  cases a; cases b; rfl

/-- What running a computation of the consumer's monad from the tokens taken gives; the consumer
itself has no state. -/
abbrev runS {β : Type} (y : StateT (Answering C) AnswerM β) (coll : List Handed) :
    β × List Handed :=
  (((y.run {}).run coll).1.1, ((y.run {}).run coll).2)

theorem runS_eq {β : Type} (y : StateT (Answering C) AnswerM β) (coll : List Handed) :
    (y.run {}).run coll = (((runS y coll).1, {}), (runS y coll).2) := by
  unfold runS
  generalize (y.run {}).run coll = r
  obtain ⟨⟨b, h⟩, t⟩ := r
  rw [answering_eq' h {}]

/-- Running a step inside the loop over a slice. -/
theorem run_step {low : Nat} {α β : Type} (x : WP.M C floor low α) (s : WP.BS floor low)
    (k : Except (WP.Intr C floor) α × WP.BS floor low → StateT (Answering C) AnswerM β)
    (coll : List Handed) :
    runS (StateT.run (ExceptT.run x) s >>= k) coll =
      runS (k (WP.runM x s coll).1) (WP.runM x s coll).2 := by
  simp only [runS, StateT.run_bind]
  generalize hr : ((x.run.run s).run {}).run coll = r
  obtain ⟨⟨a, h⟩, t⟩ := r
  rw [answering_eq' h {}]
  rfl

/-- What the lexer state says of the location at the end of the input: that of its offset, on
its line. -/
def EofLoc (c : WP.WCore) (location : Span.Location) : Prop :=
  location.offset = c.offset ∧ location.line = c.line ∧
    c.lineStart + location.column = location.offset

/-- The failure is trailing input that starts at the location. -/
def IsTrailingFailure (location : Span.Location)
    (failure : Lexer.Internal.Failure (Option C.Error)) : Prop
    :=
  failure.cause = .lexical .unexpectedTrailingToken ∧ failure.span.start = location

/-- How the loop over a slice ends where the consumer stopped. -/
def ExitMatches : Model.Stop C → Lexer.Internal.WRustPort.SliceExit C.Result
    (Option C.Error) floor → Prop
  | .trailing l, x => ∃ g, x = .done (.error g) ∧ IsTrailingFailure l.start g
  | .fail e _ _, x => ∃ g, x = .done (.error g) ∧ g.cause = .consumer (some e)
  | .layout _, x => ∃ g, x = .done (.error g) ∧ g.cause = .consumer none
  | .brk r l nx, x => (∃ a, x = .stopped (.finished r) l.end a) ∨
      ∃ l2 g, nx = some l2 ∧ x = .done (.error g) ∧ IsTrailingFailure l2.start g
  | .brkX r l, x => ∃ a, x = .stopped (.finished r) l.end a
  | .discard r l, x => ∃ a, x = .stopped (.discarded r) l.end a
  | .relex l, x => ∃ a, x = .stopped .relex l.end a

/-- The lexer state after the loop stopped with the consumer having done `p`, discarding from `d`
if `d` is some. -/
structure AfterStop (hd : Bool) (iv : Token.Version) (bytes : ByteArray) (p : Prog)
    (d : Option Span.Location)
    (c : WP.WCore) :
    Prop where
  version : c.version = p.ver
  recovers : c.recovers = false
  holding : c.holding = hd
  discardedFrom : c.discardedFrom = d
  recoveryState : c.recoveryState = none
  initial : c.initialVersion = iv
  bytes : c.batch.bytes = bytes

/-- How the loop over a slice ends after an interruption. -/
def exitOf (e : WP.Intr C floor) : Lexer.Internal.WRustPort.SliceExit C.Result
    (Option C.Error) floor :=
  match e with
  | { result := .ok stop, location, stopAfter, .. } =>
    .stopped stop location fun p hp => stopAfter p hp stop rfl
  | { result := .error cause, span, location, .. } => .done (.error { cause, span, location })

theorem exitMatches_of {s : Model.Stop C} {e : WP.Intr C floor} (h : Matches s e) :
    ExitMatches s (exitOf e) := by
  obtain ⟨result, _, location, stopAfter⟩ := e
  cases s with
  | trailing l =>
    obtain ⟨h1, h2⟩ := h
    simp only at h1
    subst h1
    exact ⟨_, rfl, rfl, h2⟩
  | fail err d l =>
    simp only [Matches] at h
    subst h
    exact ⟨_, rfl, rfl⟩
  | layout l =>
    simp only [Matches] at h
    subst h
    exact ⟨_, rfl, rfl⟩
  | brk r l nx =>
    rcases h with ⟨h1, h2⟩ | ⟨l2, h1, h2, h3⟩
    · simp only at h1 h2
      subst h1 h2
      exact .inl ⟨_, rfl⟩
    · simp only at h2
      subst h2
      exact .inr ⟨l2, _, h1, rfl, rfl, h3⟩
  | brkX r l =>
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    subst h1 h2
    exact ⟨_, rfl⟩
  | discard r l =>
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    subst h1 h2
    exact ⟨_, rfl⟩
  | relex l =>
    obtain ⟨h1, h2⟩ := h
    simp only at h1 h2
    subst h1 h2
    exact ⟨_, rfl⟩

/-- What the loop over a slice from the naive lexer's pure state `st` at `location` at the
index `position`, under the version `ver`, with the tokens taken `coll` and the lexemes `held`
in the batch, ends with. -/
def SliceOut (C : BSmtLibSpec.Lexer.Consumer) (v : Token.Version) (hd : Bool) (iv : Token.Version)
    (input : ByteSlice) (st : St) (location : Span.Location) (position : Nat) (ver : Token.Version)
    (coll : List Handed) (held : List Lexeme)
    (r : (Lexer.Internal.WRustPort.SliceExit C.Result (Option C.Error) floor × WP.BS floor 0) ×
      List Handed) : Prop :=
  match outcome C hd (pending C hd ver coll held) (feedFrom v C.concrete input st location
    position) with
  | .endOk st' location' p =>
    r.1.1 = .done (.ok .continue) ∧ Fixed v hd iv r.1.2.val ∧ r.1.2.val.version = p.ver ∧
      StAgrees v C.concrete st' r.1.2.val ∧ EofLoc r.1.2.val location' ∧ r.2 = p.taken
  | .endErr p =>
    (∃ g, r.1.1 = .done (.error g) ∧ ∃ kind : LexicalErrorKind, g.cause = .lexical kind ∧
      kind ≠ .unexpectedTrailingToken) ∧ AfterStop hd iv input.byteArray p none r.1.2.val ∧
      r.2 = p.taken
  | .stopped s p =>
    ExitMatches s r.1.1 ∧ AfterStop hd iv input.byteArray p s.discards r.1.2.val ∧ r.2 = p.taken

variable {v : Token.Version} {hd : Bool} {iv : Token.Version}

/-- The hand-over of the batch at the end of the loop over a slice: the result to return once
the batch is handed over, or where the consumer stopped. -/
theorem sliceRun_flush (input : ByteSlice) (position : Nat)
    (fnResult : Except (Lexer.Internal.Failure (Option C.Error)) (ControlFlow C.Result))
    (core : WP.BS floor 0) (coll : List Handed) (ls : List Lexeme)
    (hH : Holds core.val.batch ls) (hrec : core.val.recovers = false)
    (hflush : position ≥ input.size ∨ ∃ f, fnResult = .error f) :
    ∀ r, r = runS (Lexer.Internal.WRustPort.lexSliceRun (H := Answering C) (m := AnswerM)
      (R := C.Result) (E := Option C.Error) input position fnResult core) coll →
    (∃ c' : WP.BS floor 0, r.1 = (.done fnResult, c') ∧ key c'.val = key core.val ∧
      c'.val.batch.bytes = core.val.batch.bytes ∧
      pending C core.val.holding c'.val.version r.2 [] =
        pending C core.val.holding core.val.version coll ls) ∨
    (∃ e p d, Stops C core.val.holding core.val.version coll ls e p d ∧
      StopState core.val p d r.1.2.val core.val.batch.bytes ∧ r.1.1 = exitOf e ∧
        r.2 = p.taken) := by
  intro r hr
  subst hr
  rw [Lexer.Internal.WRustPort.lexSliceRun.eq_def]
  rw [dite_eq_left (by rcases hflush with h | ⟨f, rfl⟩ <;> simp [*])]
  rw [run_step]
  have hw := flushBatch_wp ls core hH coll hrec
    (Q := fun _ s' coll' => key s'.val = key core.val ∧
      s'.val.batch.bytes = core.val.batch.bytes ∧
      pending C core.val.holding s'.val.version coll' [] =
        pending C core.val.holding core.val.version coll ls)
    (QE := fun e s' coll' => ∃ p d, Stops C core.val.holding core.val.version coll ls e p d ∧
      StopState core.val p d s'.val core.val.batch.bytes ∧ coll' = p.taken)
    (fun s' coll' hk hb hc => ⟨hk, by rw [hb]; rfl, hc⟩)
    (fun e s' p d hs hst => ⟨p, d, hs, hst, rfl⟩)
  unfold WP at hw
  generalize WP.runM Lexer.Internal.WRustPort.Rust.flushBatch core coll = q at hw ⊢
  obtain ⟨⟨res, c'⟩, coll'⟩ := q
  cases res with
  | ok u => exact .inl ⟨c', rfl, hw.1, hw.2.1, hw.2.2⟩
  | error e =>
    obtain ⟨p, d, hs, hst, rfl⟩ := hw
    obtain ⟨result, _, location, stopAfter⟩ := e
    cases result <;> exact .inr ⟨_, p, d, hs, hst, rfl, rfl⟩

/-- The loop over a slice after a lexical error hands over the batch it was left with. -/
theorem sliceRun_error (input : ByteSlice) (position : Nat)
    (f : Lexer.Internal.Failure (Option C.Error))
    (core : WP.BS floor 0) (coll : List Handed) (ls : List Lexeme) (hH : Holds core.val.batch ls)
    (hfix : Fixed v hd iv core.val) {kind : LexicalErrorKind} (hf : f.cause = .lexical kind)
    (hk : kind ≠ .unexpectedTrailingToken) (hby : core.val.batch.bytes = input.byteArray) :
    ∀ r, r = runS (Lexer.Internal.WRustPort.lexSliceRun (H := Answering C) (m := AnswerM)
      (R := C.Result) (E := Option C.Error) input position (.error f) core) coll →
    match outcome C hd (pending C hd core.val.version coll ls) (.error []) with
    | .endOk _ _ _ => False
    | .endErr p =>
      (∃ g, r.1.1 = .done (.error g) ∧ ∃ kind : LexicalErrorKind, g.cause = .lexical kind ∧
        kind ≠ .unexpectedTrailingToken) ∧ AfterStop hd iv input.byteArray p none r.1.2.val ∧
        r.2 = p.taken
    | .stopped s p =>
      ExitMatches s r.1.1 ∧ AfterStop hd iv input.byteArray p s.discards r.1.2.val ∧
        r.2 = p.taken := by
  intro r hr
  have h := sliceRun_flush (C := C) input position (.error f) core coll ls hH hfix.recovers
    (.inr ⟨f, rfl⟩) r hr
  rcases h with ⟨c', h1, hk', hby', hc⟩ | ⟨e, p, d, hs, hst, h1, h2⟩
  · rw [hfix.holding, pending_nil] at hc
    rw [← hc]
    simp only [outcome, handAll_nil, Model.finish]
    obtain ⟨⟨-, e1'⟩, -, e3, e4, e5, -⟩ := key_fields hk'
    simp only [Prod.mk.injEq] at e3
    rw [h1]
    refine ⟨⟨f, rfl, kind, hf, hk⟩, ⟨rfl, e4.trans hfix.recovers, e3.2.trans hfix.holding,
      e3.1.trans hfix.discardedFrom, e5.trans hfix.recoveryState, e1'.trans hfix.initial,
      hby'.trans hby⟩, ?_⟩
    trivial
  · rw [hfix.holding] at hs
    obtain ⟨stop, hst', hm, hsd⟩ := outcome_of_stops hs (.error [])
    rw [hst']
    refine ⟨h1 ▸ exitMatches_of hm, ⟨hst.version, hst.recovers.trans hfix.recovers,
      hst.holding.trans hfix.holding,
      by rw [hst.discardedFrom, hfix.discardedFrom, discardsAfter_none, hsd],
      hst.recoveryState.trans hfix.recoveryState, hst.initial.trans hfix.initial,
      hst.bytes.trans hby⟩, h2⟩

/-- How the loop ends depends only on the outcome of the run from where it is. -/
theorem sliceOut_congr {input : ByteSlice} {st st' : St} {location location' : Span.Location}
    {position position' : Nat} {ver ver' : Token.Version} {coll coll' : List Handed}
    {held held' : List Lexeme}
    {r : (Lexer.Internal.WRustPort.SliceExit C.Result
    (Option C.Error) floor × WP.BS floor 0) × List Handed}
    (h : outcome C hd (pending C hd ver coll held)
        (feedFrom v C.concrete input st location position) =
      outcome C hd (pending C hd ver' coll' held')
        (feedFrom v C.concrete input st' location' position'))
    (hs : SliceOut C v hd iv input st' location' position' ver' coll' held' r) :
    SliceOut C v hd iv input st location position ver coll held r := by
  unfold SliceOut at hs ⊢
  rw [h]
  exact hs

theorem sliceRun_ok (v : Token.Version) (input : ByteSlice) :
    ∀ (n position : Nat), input.size - position < n →
    ∀ (core : WP.BS floor 0) (coll : List Handed) (st : St) (location : Span.Location)
      (held : List Lexeme), StepPre C v hd iv input st location held position core.val →
      SliceOut C v hd iv input st location position core.val.version coll held
        (runS (Lexer.Internal.WRustPort.lexSliceRun (H := Answering C) (m := AnswerM)
            (R := C.Result)
          (E := Option C.Error) input position (.ok .continue) core) coll) := by
  intro n
  induction n with
  | zero => intro position hn; omega
  | succ n ih =>
  intro position hn core coll st location held hpre
  by_cases hp : position < input.size
  · rw [Lexer.Internal.WRustPort.lexSliceRun]
    rw [dite_eq_right_of_eq_false (eq_false (by simp; omega))]
    extract_lets hposition offset hpending step
    rw [run_step]
    have hw := lexStep_wp v input position hposition core.val.state core.val.tokenStart
      core.val.base hpending ⟨core.val, ⟨Nat.le_refl _, core.property.2⟩⟩ coll st location held
      hpre rfl rfl rfl rfl
    unfold WP at hw
    generalize WP.runM step ⟨core.val, ⟨Nat.le_refl _, core.property.2⟩⟩ coll = r at hw ⊢
    obtain ⟨⟨res, c'⟩, coll'⟩ := r
    cases res with
    | ok nx =>
      obtain ⟨next, hnext⟩ := nx
      obtain ⟨st', location', held', hfix, hb, hagree, hloc, hholds, hbytes, heq⟩ := hw
      dsimp only
      refine sliceOut_congr heq (ih next (by omega) ⟨c'.val.advance next,
        c'.property.weaken.advance next⟩ coll' st' location' held' ?_)
      refine ⟨⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, rfl, by cases st' <;>
          exact hagree, ?_,
        hholds, hbytes⟩
      obtain ⟨h1, h2, h3⟩ := hloc
      dsimp only at h1 hb
      refine ⟨?_, h2, h3⟩
      show location'.offset = c'.val.offset + (next - c'.val.base) + (next - next)
      omega
    | error e =>
      simp only at hw
      unfold SliceOut
      rcases hw with ⟨⟨err, he, hk⟩, held', hH, hfix, hby, h⟩ | ⟨stop, p, h, hm, hc, hv, hb, hr, hh,
        hd', hrs, hi, hby⟩
      · rw [h]
        obtain ⟨result, span, location, stopAfter⟩ := e
        simp only at he
        subst he
        have hse := sliceRun_error (C := C) input position ⟨.lexical err, span, location⟩
          ⟨c'.val, c'.property.weaken⟩ coll' held' hH hfix rfl hk hby _ rfl
        dsimp only at hse ⊢
        revert hse
        cases outcome C hd (pending C hd c'.val.version coll' held') (.error []) with
        | endOk _ _ _ => intro h; exact h.elim
        | endErr p => intro h; exact h
        | stopped s p => intro h; exact h
      · rw [h]
        subst hc
        have hx := exitMatches_of hm
        obtain ⟨result, span, location, stopAfter⟩ := e
        cases result with
        | ok stp =>
          exact ⟨hx, ⟨hv, hr, hh, hd', hrs, hi, hby⟩, rfl⟩
        | error cause =>
          have hf := sliceRun_flush (C := C) input position (.error { cause, span, location })
            ⟨c'.val, c'.property.weaken⟩ p.taken [] hb hr (.inr ⟨_, rfl⟩) _ rfl
          rcases hf with ⟨c2, h1, hk', hby2, hc⟩ | ⟨e2, p2, d2, hs, -, -, -⟩
          · simp only [pending_nil, HandOut.cont.injEq, Prog.mk.injEq] at hc
            obtain ⟨hc1, hc2⟩ := hc
            obtain ⟨⟨-, e1'⟩, -, e3, e4, e5, -⟩ := key_fields hk'
            simp only [Prod.mk.injEq] at e3
            dsimp only at h1 hc1 ⊢
            rw [h1]
            exact ⟨hx, ⟨hc2.trans hv, e4.trans hr, e3.2.trans hh, e3.1.trans hd',
              e5.trans hrs, e1'.trans hi, hby2.trans hby⟩, hc1⟩
          · simp [Stops, pending_nil] at hs
  · have hf := sliceRun_flush (C := C) input position (.ok .continue) core coll held hpre.holds
      hpre.fixed.recovers (.inl (by omega)) _ rfl
    unfold SliceOut
    rw [feedFrom_ge hp]
    rw [hpre.fixed.holding] at hf
    rcases hf with ⟨c', h1, hk, -, hc⟩ | ⟨e, p, d, hs, hst, h1, h2⟩
    · rw [pending_nil] at hc
      rw [← hc]
      simp only [outcome, handAll_nil, Model.finish]
      rw [h1]
      obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
      refine ⟨rfl, fixed_of_key hpre.fixed hk, by first | rfl | trivial,
        stAgrees_of_key hpre.agrees hk, ?_, by first | rfl | trivial⟩
      obtain ⟨g1, g2, g3⟩ := hpre.loc
      show location.offset = c'.val.offset ∧ location.line = c'.val.line ∧
        c'.val.lineStart + location.column = location.offset
      refine ⟨?_, by rw [k10]; exact g2, by rw [k11]; exact g3⟩
      rw [k8, g1, hpre.base]
      omega
    · obtain ⟨stop, hst', hm, hsd⟩ := outcome_of_stops hs (.ok (st, location, []))
      rw [hst']
      refine ⟨h1 ▸ exitMatches_of hm, ⟨hst.version, hst.recovers.trans hpre.fixed.recovers,
        hst.holding.trans hpre.fixed.holding,
        by rw [hst.discardedFrom, hpre.fixed.discardedFrom, discardsAfter_none, hsd],
        hst.recoveryState.trans hpre.fixed.recoveryState, hst.initial.trans hpre.fixed.initial,
        hst.bytes.trans hpre.bytes⟩,
        h2⟩

end

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Slice

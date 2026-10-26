module

public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Loop
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Eof
public import BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VEof
public import BSmtLib.Facts.Proofs.Lexer.Consumers.AlikeF
import all BSmtLib.Lexer.Internal.VNaive
import all BSmtLib.Lexer.Internal.WRustPort
import all BSmtLib.Span
import all BSmtLib.Lexer.Error

@[expose] public section

/-!
# The Rust port with every consumer, against the naive lexer

`lexing_wRustPort_vNaive`: what the adapter makes of the Rust port `WRustPort` with every consumer
of the specification formalism (`BSmtLibSpec`) is what it makes of the naive lexer
(`Adapters.lexing`).

Between two calls the Rust port's lexer state corresponds to the naive lexer's (`CR`): they have
the same version and holding, and either the state is the naive lexer's pure state at its
location, or both discard from the same location. The calls give results the formalism does not
tell apart (`CallAlike`), which is what `lexing_alikeF` needs:
- a call on a slice (`slice_step`) lexes it by the loop over its stops (`loop`, via
  `inner_loop`) or discards it, where both lexers stay;
- a call at the end of the input (`eof_step`) gives what both do there (`eofRes_unique`).

With a consumer that does not take whitespace and comments, the Rust port's calls never fail with
the adapter's error `none`, which the adapter's consumer answers when it is handed one
(`slice_step_noNone`, `eof_step_noNone`).
-/

open BSmtLib.Facts.Lexer.Adapters BSmtLib.Facts.Proofs.Lexer.Consumers.AlikeF
open BSmtLib.Facts.Proofs.Lexer.Consumers.VEnd BSmtLib.Facts.Proofs.Lexer.Consumers.VHold
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSession
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSession.Core BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps
open BSmtLib.Facts.Proofs.Lexer.VNaive.Run BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Agree
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Eof
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.EofModel
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.HandOver
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Loop
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Slice
open BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.VEof BSmtLib.Lexer.Error
open BSmtLib.Lexer.Internal.VNaive

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls

open BSmtLibSpec.Lexer (Handed)

variable {C : BSmtLibSpec.Lexer.Consumer}

theorem runIA_bind {α β : Type} (x : Lexer.Internal.WRustPort.InnerM (Answering C) AnswerM α)
    (f : α → Lexer.Internal.WRustPort.InnerM (Answering C) AnswerM β) (c : WP.WCore)
    (coll : List Handed) :
    runIA (x >>= f) c coll = runIA (f (runIA x c coll).1.1) (runIA x c coll).1.2
        (runIA x c coll).2 := by
  simp only [runIA, StateT.run_bind]
  generalize ((x.run c).run {}).run coll = r
  obtain ⟨⟨⟨a, c'⟩, h⟩, t⟩ := r
  rw [answering_eq' h {}]
  rfl

theorem runIA_getThe (c : WP.WCore) (coll : List Handed) :
    runIA (C := C) (getThe Lexer.Internal.WRustPort.LexerCore) c coll = ((c, c), coll) := rfl

theorem runIA_pure {α : Type} (a : α) (c : WP.WCore) (coll : List Handed) :
    runIA (C := C) (pure a) c coll = ((a, c), coll) := rfl

theorem runIA_modifyThe (f : WP.WCore → WP.WCore) (c : WP.WCore) (coll : List Handed) :
    runIA (C := C) (modifyThe Lexer.Internal.WRustPort.LexerCore f) c coll =
        (((), f c), coll) := rfl

/-- The Rust port's lexer state is the naive lexer's between two calls: the same version,
holding, and the naive lexer's pure state at its location, or both discard from the same
location. -/
structure CR (C : BSmtLibSpec.Lexer.Consumer) (c : WP.WCore) (n : Core) : Prop where
  version : c.version = n.version
  initial : c.initialVersion = n.initialVersion
  holding : c.holding = n.holding
  recovers : c.recovers = false
  recoveryState : c.recoveryState = none
  loc : EofLoc c n.location
  rest : (∃ st, n.activity = st.activity ∧ StAgrees n.version C.concrete st c ∧
      c.discardedFrom = none) ∨
    (∃ s, n.activity = .discarding s ∧ c.discardedFrom = some s ∧ c.state = .normal)

theorem lexOps_lexSliceStepW (core : WP.WCore) (held : Option (Span.Located C.Result))
    (slice : ByteSlice) (taken : List Handed) :
    (WRustPort.lexOps.lexSliceStep (consumer := C) ⟨{}, core, held⟩ slice).run taken =
      match runIA (Lexer.Internal.WRustPort.lexSliceStep (H := Answering C) (m := AnswerM)
          (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ()) slice)
          core taken with
      | ((r, core'), taken') => ((r, ⟨{}, core', held⟩), taken') := by
  simp only [WRustPort.lexOps, Lexer.Internal.WRustPort.Lexer.run, StateT.run_bind]
  unfold runIA
  generalize (((Lexer.Internal.WRustPort.lexSliceStep (H := Answering C) (m := AnswerM)
      (R := C.Result)
    (E := Option C.Error) (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
    (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast) slice).run core).run
    {}).run taken = r
  obtain ⟨⟨⟨res, core'⟩, h⟩, taken'⟩ := r
  rw [answering_eq' h {}]
  rfl

theorem lexOps_lexEofStepW (core : WP.WCore) (held : Option (Span.Located C.Result))
    (taken : List Handed) :
    (WRustPort.lexOps.lexEofStep (consumer := C) ⟨{}, core, held⟩).run taken =
      match runIA (Lexer.Internal.WRustPort.lexEofStep (H := Answering C) (m := AnswerM)
          (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ()))
          core taken with
      | ((r, core'), taken') => ((r, ⟨{}, core', held⟩), taken') := by
  simp only [WRustPort.lexOps, Lexer.Internal.WRustPort.Lexer.run, StateT.run_bind]
  unfold runIA
  generalize (((Lexer.Internal.WRustPort.lexEofStep (H := Answering C) (m := AnswerM)
      (R := C.Result)
    (E := Option C.Error) (Lexer.Recovery.LexerRecovery.abandon Lexer.Recovery.FailFast)
    (Lexer.Recovery.LexerRecovery.recover Lexer.Recovery.FailFast)).run core).run {}).run taken = r
  obtain ⟨⟨⟨res, core'⟩, h⟩, taken'⟩ := r
  rw [answering_eq' h {}]
  rfl

/-- Lexing a slice from the lexer state that is the naive lexer's pure state, as the naive
lexer's loop over its bytes. -/
theorem inner_loop (c : WP.WCore) (n : Core) (st : St) (bytes : List UInt8) (taken : List Handed)
    (hfix : Fixed n.version n.holding n.initialVersion c) (hag : StAgrees n.version C.concrete st c)
    (hloc : EofLoc c n.location) (hver : c.version = n.version)
    (hact : n.activity = st.activity) :
    LoopRel C
      (runIA (Lexer.Internal.WRustPort.lexSliceInner (H := Answering C) (m := AnswerM)
          (R := C.Result)
        (E := Option C.Error) bytes.toByteArray.toByteSlice) c taken)
      (vBytes C n none bytes taken) := by
  rw [show vBytes C n none bytes taken = vBytes C n none (bytes.drop 0) taken by
    rw [List.drop_zero]]
  unfold runIA Lexer.Internal.WRustPort.lexSliceInner
  refine loop (C := C) bytes c.offset (bytes.length + 2) (c.offset - 1) (by omega) 0 none _ taken
    n st (by omega) ?_ hver hact (by rw [hloc.1]; rfl) (Nat.zero_le _)
  obtain ⟨h1, h2, h3⟩ := hloc
  exact ⟨⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, rfl, by cases st <;> exact hag,
    ⟨by show n.location.offset = c.offset + (0 - 0); omega, h2, h3⟩,
    holds_of_len_zero rfl, rfl⟩

/-- The span of a consumer's error of the Rust port is that of the last token taken. -/
def SpanAlike {C : BSmtLibSpec.Lexer.Consumer} {β : Type}
    (x : Except (LexerError (Option C.Error)) β) (t : List Handed) : Prop :=
  ∀ e, x = .error e → ∀ c, e.cause = .consumer (some c) → e.span = Cursor.handedSpan t

/-- What a call of the Rust port and one of the naive lexer give alike: an error of the Rust port
does not go on, the results are alike as `preciseOf` says, the same tokens are taken, the lexer
states correspond again when the call does not fail, and the version and discarding are the same
always. -/
def CallAlike (C : BSmtLibSpec.Lexer.Consumer) {β : Type}
    (rW : (Except (LexerError (Option C.Error)) β × WP.WCore) × List Handed)
    (rV : VRes (Except (LexerError (Option C.Error)) β)) : Prop :=
  (∀ e, rW.1.1 = .error e → e.continuesFrom = none) ∧
    rW.1.1.mapError preciseOf = rV.1.1.mapError preciseOf ∧ rW.2 = rV.2 ∧
    (rW.1.1.isOk = true → CR C rW.1.2 rV.1.2) ∧ rW.1.2.version = rV.1.2.version ∧
    rW.1.2.discardedFrom = discardedOf rV.1.2 ∧ SpanAlike rW.1.1 rW.2

/-- A call of the Rust port that lexes a slice, against the naive lexer's. -/
theorem slice_step (c : WP.WCore) (n : Core) (bytes : List UInt8) (taken : List Handed)
    (h : CR C c n) :
    CallAlike C
      (runIA (Lexer.Internal.WRustPort.lexSliceStep (H := Answering C) (m := AnswerM)
        (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())
        bytes.toByteArray.toByteSlice) c taken)
      (vRun C (Lexer.Internal.VNaive.lexSliceStep (H := Answering C) false (fun _ => pure ())
        (fun _ => pure ()) bytes.toByteArray.toByteSlice n) taken) := by
  rcases h.rest with ⟨st, hact, hag, hdf⟩ | ⟨s, hact, hdf, hstate⟩
  · have hp : (Plain n) := by unfold Core.Plain; rw [hact]; cases st <;> trivial
    rw [lexSliceStep_vBytes C n hp bytes taken]
    unfold Lexer.Internal.WRustPort.lexSliceStep
    rw [runIA_bind, runIA_getThe]
    rw [ite_eq_right (by simp [hdf])]
    dsimp only
    rw [runIA_bind, runIA_getThe]
    dsimp only
    rw [h.recoveryState]
    dsimp only
    rw [runIA_bind]
    have hl := inner_loop (C := C) c n st bytes taken ⟨by rw [h.version], h.recovers, hdf,
      h.holding, h.recoveryState, h.initial⟩ hag h.loc h.version hact
    generalize runIA (Lexer.Internal.WRustPort.lexSliceInner (H := Answering C) (m := AnswerM)
      (R := C.Result) (E := Option C.Error) bytes.toByteArray.toByteSlice) c taken = R at hl ⊢
    obtain ⟨⟨res, c'⟩, t⟩ := R
    generalize vBytes C n none bytes taken = rv at hl ⊢
    obtain ⟨⟨resv, n'⟩, tv⟩ := rv
    obtain ⟨ht, hv, hm⟩ := hl
    simp only at ht hv hm
    subst ht
    cases res with
    | ok held =>
      cases resv with
      | error _ => exact hm.elim
      | ok held' =>
        obtain ⟨rfl, hok⟩ := hm
        dsimp only
        rcases hok.rest with ⟨st', a1, a2, a3, a4⟩ | ⟨s, a1, a2, a3, a4, a5⟩
        · refine ⟨(fun e he => by cases he),
            rfl, rfl, fun _ => ⟨hok.version, hok.initial, hok.holding, hok.recovers,
            hok.recoveryState, a4, .inl ⟨st', a1, a2, a3⟩⟩, hok.version, ?_,
            fun e he => by cases he⟩
          show c'.discardedFrom = discardedOf n'
          rw [a3]
          unfold discardedOf
          rw [a1]
          cases st' <;> rfl
        · refine ⟨(fun e he => by cases he),
            rfl, rfl, fun _ => ⟨hok.version, hok.initial, hok.holding, hok.recovers,
            hok.recoveryState, by rw [a5]; exact a4, .inr ⟨s, a1, a2, a3⟩⟩, hok.version, ?_,
            fun e he => by cases he⟩
          show c'.discardedFrom = discardedOf n'
          rw [a2]
          unfold discardedOf
          rw [a1]
    | error f =>
      cases resv with
      | ok _ => exact hm.elim
      | error g =>
        obtain ⟨hcf, hdWV, hrec, hsr⟩ := hm
        dsimp only
        unfold Lexer.Internal.WRustPort.fail
        rw [runIA_bind, runIA_bind, runIA_getThe]
        simp only [hrec, Bool.not_false, ↓reduceIte]
        refine ⟨(fun e he => by cases he; rfl), ?_, rfl, nofun, hv, hdWV, ?_⟩
        · exact congrArg Except.error hcf
        · intro e he
          cases he
          exact hsr.2.2
  · have hp : (Plain n) := by unfold Core.Plain; rw [hact]; trivial
    rw [lexSliceStep_vBytes C n hp bytes taken]
    obtain ⟨n', hvb, b1, b2, b3, b4, b5⟩ := vBytes_discarding C bytes n none taken hact
    rw [hvb]
    unfold Lexer.Internal.WRustPort.lexSliceStep
    rw [runIA_bind, runIA_getThe]
    rw [ite_eq_left (by simp [hdf])]
    refine ⟨(fun e he => by cases he),
        rfl, rfl, fun _ => ⟨h.version.trans b1.symm, h.initial.trans b5.symm,
      h.holding.trans b4.symm, h.recovers, h.recoveryState, by rw [b3]; exact h.loc,
      .inr ⟨s, b2, hdf, hstate⟩⟩, h.version.trans b1.symm, ?_, fun e he => by cases he⟩
    show c.discardedFrom = discardedOf n'
    rw [hdf]
    unfold discardedOf
    rw [b2]

/-- With a consumer that does not take whitespace and comments, a call of the Rust port that lexes
a slice from a state that is the naive lexer's does not fail with the adapter's error `none`: the
consumer is handed no whitespace or comment. -/
theorem slice_step_noNone (c : WP.WCore) (n : Core) (bytes : List UInt8) (taken : List Handed)
    (h : CR C c n) (hc : C.concrete = false) :
    ∀ e, (runIA (Lexer.Internal.WRustPort.lexSliceStep (H := Answering C) (m := AnswerM)
        (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())
        bytes.toByteArray.toByteSlice) c taken).1.1 = .error e → e.cause ≠ .consumer none := by
  rcases h.rest with ⟨st, hact, hag, hdf⟩ | ⟨s, hact, hdf, hstate⟩
  · unfold Lexer.Internal.WRustPort.lexSliceStep
    rw [runIA_bind, runIA_getThe]
    rw [ite_eq_right (by simp [hdf])]
    dsimp only
    rw [runIA_bind, runIA_getThe]
    dsimp only
    rw [h.recoveryState]
    dsimp only
    rw [runIA_bind]
    have hl := inner_loop (C := C) c n st bytes taken ⟨by rw [h.version], h.recovers, hdf,
      h.holding, h.recoveryState, h.initial⟩ hag h.loc h.version hact
    generalize runIA (Lexer.Internal.WRustPort.lexSliceInner (H := Answering C) (m := AnswerM)
      (R := C.Result) (E := Option C.Error) bytes.toByteArray.toByteSlice) c taken = R at hl ⊢
    obtain ⟨⟨res, c'⟩, t⟩ := R
    generalize vBytes C n none bytes taken = rv at hl
    obtain ⟨⟨resv, n'⟩, tv⟩ := rv
    obtain ⟨-, -, hm⟩ := hl
    simp only at hm
    cases res with
    | ok held =>
      intro e he
      cases he
    | error f =>
      cases resv with
      | ok _ => exact hm.elim
      | error g =>
        obtain ⟨-, -, hrec, hnn⟩ := hm
        dsimp only
        unfold Lexer.Internal.WRustPort.fail
        rw [runIA_bind, runIA_bind, runIA_getThe]
        simp only [hrec, Bool.not_false, ↓reduceIte]
        intro e he
        cases he
        exact hnn.1 hc
  · unfold Lexer.Internal.WRustPort.lexSliceStep
    rw [runIA_bind, runIA_getThe]
    rw [ite_eq_left (by simp [hdf])]
    intro e he
    cases he

/-- A call of the Rust port at the end of the input, against the naive lexer's. -/
theorem eof_step (c : WP.WCore) (n : Core) (taken : List Handed) (h : CR C c n) :
    CallAlike C
      (runIA (Lexer.Internal.WRustPort.lexEofStep (H := Answering C) (m := AnswerM)
        (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())) c taken)
      (vEnd C n taken) := by
  obtain ⟨st, hag, hd0, hV⟩ : ∃ st, StAgrees n.version C.concrete st c ∧
      c.discardedFrom = discardedOf n ∧
      (n.activity = st.activity ∨ (st = .idle ∧ ∃ s, n.activity = .discarding s)) := by
    rcases h.rest with ⟨st, hact, hag, hdf⟩ | ⟨s, hact, hdf, hstate⟩
    · refine ⟨st, hag, ?_, .inl hact⟩
      rw [hdf]
      unfold discardedOf
      rw [hact]
      cases st <;> rfl
    · refine ⟨.idle, hstate, ?_, .inr ⟨rfl, s, hact⟩⟩
      rw [hdf]
      unfold discardedOf
      rw [hact]
  have hVr := vEnd_eofRes C n st taken hV
  have hWall := lexEofInner_eof (C := C) n.version c taken st n.location h.recovers hag h.loc
  have hW := hWall.1
  have hWs := hWall.2.2
  unfold EofFin at hW
  rw [h.holding, h.version, hd0] at hW
  rw [h.holding, h.version] at hWs
  unfold Lexer.Internal.WRustPort.lexEofStep
  rw [runIA_bind, runIA_getThe]
  simp only [h.recoveryState]
  rw [ite_eq_right (by simp)]
  rw [runIA_bind]
  unfold Lexer.Internal.WRustPort.executeStep
  rw [runIA_bind]
  generalize runIA (Lexer.Internal.WRustPort.lexEofInner (H := Answering C) (m := AnswerM)
    (R := C.Result) (E := Option C.Error)) c taken = R at hW hWs ⊢
  obtain ⟨⟨res, c'⟩, t⟩ := R
  obtain ⟨hW, hkeep⟩ := hW
  obtain ⟨hVr, hreset⟩ := hVr
  generalize vEnd C n taken = rv at hVr hreset ⊢
  obtain ⟨⟨resv, n'⟩, tv⟩ := rv
  dsimp only at hW hVr hkeep hreset
  have hspan : ∀ f, res = .error f → ∀ x, f.cause = .consumer (some x) →
      f.span = Cursor.handedSpan t := by
    intro f hf x hx
    obtain ⟨l, hl, hs⟩ := hWs f hf x hx
    obtain ⟨e, b, p, d, ho, y, hy1, hy2, hy3⟩ := Eof.eofOut_failTaken hl
    have hW' := hW
    rw [ho] at hW'
    have ht : t = p.taken := hW'.2.2.2
    rw [hs, ht]
    exact (Cursor.handedSpan_eq hy1 hy2 hy3).symm
  obtain ⟨hres, htk, hweak⟩ := eofRes_unique hW hVr
  subst htk
  have hcur : c'.currentLocation = n.location := by
    obtain ⟨h1, h2, h3⟩ := h.loc
    show Span.Location.Internal.new (c'.offset + (c'.base - c'.base)) c'.line
      (c'.offset + (c'.base - c'.base) - c'.lineStart) = n.location
    rw [hkeep.offset, hkeep.line, hkeep.lineStart]
    apply Span.Location.ext <;>
      simp only [Span.Location.Internal.offset_new, Span.Location.Internal.line_new,
        Span.Location.Internal.column_new] <;>
      omega
  have hrec : c'.recovers = false := hkeep.recovers.trans h.recovers
  rcases res with f | flow
  · simp only [runIA_pure]
    rw [ite_eq_right (by simp)]
    rw [runIA_bind]
    unfold Lexer.Internal.WRustPort.fail
    rw [runIA_bind, runIA_getThe]
    simp only [hrec, Bool.not_false, ↓reduceIte, runIA_pure]
    obtain ⟨hv, hd⟩ := hweak rfl
    exact ⟨(fun e he => by cases he; rfl), hres, rfl, nofun, hv, hd,
      fun e he x hx => by cases he; exact hspan f rfl x hx⟩
  · cases flow with
    | «continue» =>
      have hr : resv = .ok .continue := by
        cases resv <;> simp_all [innerRes, Except.mapError]
      subst hr
      have hn' := hreset rfl
      subst hn'
      simp only [runIA_pure]
      rw [runIA_bind]
      unfold Lexer.Internal.WRustPort.reset
      rw [runIA_modifyThe]
      exact ⟨(fun e he => by cases he),
          rfl, rfl, fun _ => ⟨hkeep.initial.trans h.initial, hkeep.initial.trans h.initial, rfl,
        hrec, rfl, ⟨rfl, rfl, rfl⟩, .inl ⟨.idle, rfl, rfl, rfl⟩⟩,
        hkeep.initial.trans h.initial, rfl, fun e he => by cases he⟩
    | «break» r =>
      have hr : resv = .ok (.break (Span.Located.Internal.new r n.location)) := by
        cases resv <;> simp_all [innerRes, Except.mapError]
      subst hr
      have hn' := hreset rfl
      subst hn'
      simp only [runIA_bind, runIA_getThe, runIA_pure]
      unfold Lexer.Internal.WRustPort.reset
      rw [runIA_modifyThe]
      refine ⟨(fun e he => by cases he),
          ?_, rfl, fun _ => ⟨hkeep.initial.trans h.initial, hkeep.initial.trans h.initial, rfl,
        hrec, rfl, ⟨rfl, rfl, rfl⟩, .inl ⟨.idle, rfl, rfl, rfl⟩⟩,
        hkeep.initial.trans h.initial, rfl, fun e he => by cases he⟩
      rw [hcur]

/-- With a consumer that does not take whitespace and comments, a call of the Rust port at the end
of the input from a state that is the naive lexer's does not fail with the adapter's error
`none`: the consumer is handed no whitespace or comment. -/
theorem eof_step_noNone (c : WP.WCore) (n : Core) (taken : List Handed) (h : CR C c n)
    (hc : C.concrete = false) :
    ∀ e, (runIA (Lexer.Internal.WRustPort.lexEofStep (H := Answering C) (m := AnswerM)
        (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())) c
        taken).1.1 = .error e → e.cause ≠ .consumer none := by
  obtain ⟨st, hag⟩ : ∃ st, StAgrees n.version C.concrete st c := by
    rcases h.rest with ⟨st, -, hag, -⟩ | ⟨s, -, -, hstate⟩
    · exact ⟨st, hag⟩
    · exact ⟨.idle, hstate⟩
  have hW := lexEofInner_eof (C := C) n.version c taken st n.location h.recovers hag h.loc
  unfold Lexer.Internal.WRustPort.lexEofStep
  rw [runIA_bind, runIA_getThe]
  simp only [h.recoveryState]
  rw [ite_eq_right (by simp)]
  rw [runIA_bind]
  unfold Lexer.Internal.WRustPort.executeStep
  rw [runIA_bind]
  generalize runIA (Lexer.Internal.WRustPort.lexEofInner (H := Answering C) (m := AnswerM)
    (R := C.Result) (E := Option C.Error)) c taken = R at hW ⊢
  obtain ⟨⟨res, c'⟩, t⟩ := R
  obtain ⟨⟨-, hkeep⟩, hnn⟩ := hW
  dsimp only at hkeep hnn
  have hrec : c'.recovers = false := hkeep.recovers.trans h.recovers
  rcases res with f | flow
  · simp only [runIA_pure]
    rw [ite_eq_right (by simp)]
    rw [runIA_bind]
    unfold Lexer.Internal.WRustPort.fail
    rw [runIA_bind, runIA_getThe]
    simp only [hrec, Bool.not_false, ↓reduceIte, runIA_pure]
    intro e he
    cases he
    exact hnn.1 hc f rfl
  · cases flow with
    | «continue» =>
      simp only [runIA_pure]
      rw [runIA_bind]
      unfold Lexer.Internal.WRustPort.reset
      rw [runIA_modifyThe]
      intro e he
      cases he
    | «break» r =>
      simp only [runIA_bind, runIA_getThe, runIA_pure]
      intro e he
      cases he

theorem cr_weak {c : WP.WCore} {n : Core} (h : CR C c n) : c.discardedFrom = discardedOf n := by
  rcases h.rest with ⟨st, hact, -, hdf⟩ | ⟨s, hact, hdf, -⟩
  · rw [hdf]
    unfold discardedOf
    rw [hact]
    cases st <;> rfl
  · rw [hdf]
    unfold discardedOf
    rw [hact]

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls

namespace BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls

/-- Lexers of the Rust port and of the naive lexer that correspond between two calls: the same
held result, and states that correspond (`CR`). -/
def WVRel (C : BSmtLibSpec.Lexer.Consumer) (w : WRustPort.lexOps.Lexer C)
    (n : VNaive.lexOps.Lexer C) : Prop :=
  w.held = n.held ∧ CR C w.core n.core

/-- What is left of `WVRel` after a call that failed: the same version and discarding. -/
def WVWeak (C : BSmtLibSpec.Lexer.Consumer) (w : WRustPort.lexOps.Lexer C)
    (n : VNaive.lexOps.Lexer C) : Prop :=
  w.core.version = n.core.version ∧ w.core.discardedFrom = discardedOf n.core

theorem wvRel_new (C : BSmtLibSpec.Lexer.Consumer) (version : Version) :
    WVRel C (WRustPort.lexOps.new C {} version) (VNaive.lexOps.new C {} version) :=
  ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, .inl ⟨.idle, rfl, rfl, rfl⟩⟩⟩

theorem wv_sliceP (C : BSmtLibSpec.Lexer.Consumer) (slice : BSmtLibSpec.Regex.Chars) :
    StepsAlikeG WRustPort.lexOps VNaive.lexOps (WVRel C) (WVWeak C) preciseOf
      (fun a => WRustPort.lexOps.lexSliceStep a slice.toByteArray.toByteSlice)
      (fun b => VNaive.lexOps.lexSliceStep b slice.toByteArray.toByteSlice) := by
  intro a b taken ⟨hh, hcr⟩
  obtain ⟨ha, ca, hda⟩ := a
  obtain ⟨hb, cb, hdb⟩ := b
  rw [answering_eq' ha {}, answering_eq' hb {}]
  simp only at hh hcr
  rw [lexOps_lexSliceStepW, lexOps_lexSliceStep]
  have hs := slice_step ca cb slice taken hcr
  generalize runIA (Lexer.Internal.WRustPort.lexSliceStep (H := Answering C) (m := AnswerM)
    (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())
    slice.toByteArray.toByteSlice) ca taken = rW at hs ⊢
  generalize vRun C (Lexer.Internal.VNaive.lexSliceStep (H := Answering C) false
      (fun _ => pure ())
    (fun _ => pure ()) slice.toByteArray.toByteSlice cb) taken = rV at hs ⊢
  obtain ⟨⟨r, c'⟩, t⟩ := rW
  obtain ⟨⟨r', n'⟩, t'⟩ := rV
  obtain ⟨-, e1, e2, e3, e4, e5⟩ := hs
  exact ⟨e1, e2, fun hok => ⟨hh, e3 hok⟩, e4, e5.1⟩

theorem wv_eofP (C : BSmtLibSpec.Lexer.Consumer) :
    StepsAlikeG WRustPort.lexOps VNaive.lexOps (WVRel C) (WVWeak C) preciseOf
      WRustPort.lexOps.lexEofStep VNaive.lexOps.lexEofStep := by
  intro a b taken ⟨hh, hcr⟩
  obtain ⟨ha, ca, hda⟩ := a
  obtain ⟨hb, cb, hdb⟩ := b
  rw [answering_eq' ha {}, answering_eq' hb {}]
  simp only at hh hcr
  rw [lexOps_lexEofStepW, lexOps_lexEofStep]
  have hs := eof_step ca cb taken hcr
  generalize runIA (Lexer.Internal.WRustPort.lexEofStep (H := Answering C) (m := AnswerM)
    (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())) ca taken = rW
    at hs ⊢
  generalize vEnd C cb taken = rV at hs ⊢
  obtain ⟨⟨r, c'⟩, t⟩ := rW
  obtain ⟨⟨r', n'⟩, t'⟩ := rV
  obtain ⟨-, e1, e2, e3, e4, e5⟩ := hs
  exact ⟨e1, e2, fun hok => ⟨hh, e3 hok⟩, e4, e5.1⟩

/-- A call of the Rust port on a slice, from a lexer that corresponds to the naive lexer's, fails
with a consumer's error only with the span of the last token taken, and, with a consumer that does
not take whitespace and comments, not with the adapter's error `none`. -/
theorem wv_slice_span (C : BSmtLibSpec.Lexer.Consumer) (slice : BSmtLibSpec.Regex.Chars)
    (a : WRustPort.lexOps.Lexer C) (b : VNaive.lexOps.Lexer C)
    (taken : List BSmtLibSpec.Lexer.Handed) (h : WVRel C a b) :
    SpanAlike ((WRustPort.lexOps.lexSliceStep a slice.toByteArray.toByteSlice).run taken).1.1
      ((WRustPort.lexOps.lexSliceStep a slice.toByteArray.toByteSlice).run taken).2 ∧
    (C.concrete = false → ∀ e,
      ((WRustPort.lexOps.lexSliceStep a slice.toByteArray.toByteSlice).run taken).1.1 =
        .error e → e.cause ≠ .consumer none) := by
  obtain ⟨hh, hcr⟩ := h
  obtain ⟨ha, ca, hda⟩ := a
  obtain ⟨hb, cb, hdb⟩ := b
  rw [answering_eq' ha {}]
  rw [lexOps_lexSliceStepW]
  have hs := slice_step ca cb slice taken hcr
  have hn := fun hc => slice_step_noNone ca cb slice taken hcr hc
  generalize runIA (Lexer.Internal.WRustPort.lexSliceStep (H := Answering C) (m := AnswerM)
    (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())
    slice.toByteArray.toByteSlice) ca taken = rW at hs hn ⊢
  obtain ⟨⟨r, c'⟩, t⟩ := rW
  exact ⟨hs.2.2.2.2.2.2, hn⟩

/-- A call of the Rust port at the end of the input, from a lexer that corresponds to the naive
lexer's, fails with a consumer's error only with the span of the last token taken, and, with a
consumer that does not take whitespace and comments, not with the adapter's error `none`. -/
theorem wv_eof_span (C : BSmtLibSpec.Lexer.Consumer)
    (a : WRustPort.lexOps.Lexer C) (b : VNaive.lexOps.Lexer C)
    (taken : List BSmtLibSpec.Lexer.Handed) (h : WVRel C a b) :
    SpanAlike ((WRustPort.lexOps.lexEofStep a).run taken).1.1
      ((WRustPort.lexOps.lexEofStep a).run taken).2 ∧
    (C.concrete = false → ∀ e, ((WRustPort.lexOps.lexEofStep a).run taken).1.1 = .error e →
      e.cause ≠ .consumer none) := by
  obtain ⟨hh, hcr⟩ := h
  obtain ⟨ha, ca, hda⟩ := a
  obtain ⟨hb, cb, hdb⟩ := b
  rw [answering_eq' ha {}]
  rw [lexOps_lexEofStepW]
  have hs := eof_step ca cb taken hcr
  have hn := fun hc => eof_step_noNone ca cb taken hcr hc
  generalize runIA (Lexer.Internal.WRustPort.lexEofStep (H := Answering C) (m := AnswerM)
    (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())) ca taken = rW
    at hs hn ⊢
  obtain ⟨⟨r, c'⟩, t⟩ := rW
  exact ⟨hs.2.2.2.2.2.2, hn⟩

/-- A call of the Rust port on a slice, from a lexer that corresponds to the naive lexer's, fails
with an error that does not go on. -/
theorem wv_slice_none (C : BSmtLibSpec.Lexer.Consumer) (slice : BSmtLibSpec.Regex.Chars)
    (a : WRustPort.lexOps.Lexer C) (b : VNaive.lexOps.Lexer C)
    (taken : List BSmtLibSpec.Lexer.Handed)
    (h : WVRel C a b) (e : LexerError (Option C.Error))
    (he : ((WRustPort.lexOps.lexSliceStep a slice.toByteArray.toByteSlice).run taken).1.1 =
      .error e) :
    e.continuesFrom = none := by
  obtain ⟨hh, hcr⟩ := h
  obtain ⟨ha, ca, hda⟩ := a
  obtain ⟨hb, cb, hdb⟩ := b
  rw [answering_eq' ha {}] at he
  rw [lexOps_lexSliceStepW] at he
  have hs := (slice_step ca cb slice taken hcr).1
  generalize runIA (Lexer.Internal.WRustPort.lexSliceStep (H := Answering C) (m := AnswerM)
    (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())
    slice.toByteArray.toByteSlice) ca taken = rW at hs he
  obtain ⟨⟨r, c'⟩, t⟩ := rW
  exact hs e he

/-- A call of the Rust port at the end of the input, from a lexer that corresponds to the naive
lexer's, fails with an error that does not go on. -/
theorem wv_eof_none (C : BSmtLibSpec.Lexer.Consumer)
    (a : WRustPort.lexOps.Lexer C) (b : VNaive.lexOps.Lexer C)
    (taken : List BSmtLibSpec.Lexer.Handed)
    (h : WVRel C a b) (e : LexerError (Option C.Error))
    (he : ((WRustPort.lexOps.lexEofStep a).run taken).1.1 = .error e) :
    e.continuesFrom = none := by
  obtain ⟨hh, hcr⟩ := h
  obtain ⟨ha, ca, hda⟩ := a
  obtain ⟨hb, cb, hdb⟩ := b
  rw [answering_eq' ha {}] at he
  rw [lexOps_lexEofStepW] at he
  have hs := (eof_step ca cb taken hcr).1
  generalize runIA (Lexer.Internal.WRustPort.lexEofStep (H := Answering C) (m := AnswerM)
    (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())) ca taken = rW
    at hs he
  obtain ⟨⟨r, c'⟩, t⟩ := rW
  exact hs e he

theorem wv_slice (C : BSmtLibSpec.Lexer.Consumer) (slice : BSmtLibSpec.Regex.Chars) :
    StepsAlikeF WRustPort.lexOps VNaive.lexOps (WVRel C) (WVWeak C)
      (fun a => WRustPort.lexOps.lexSliceStep a slice.toByteArray.toByteSlice)
      (fun b => VNaive.lexOps.lexSliceStep b slice.toByteArray.toByteSlice) :=
  (wv_sliceP C slice).toF _ _ _ _ Prod.fst preciseOf_fst

theorem wv_eof (C : BSmtLibSpec.Lexer.Consumer) :
    StepsAlikeF WRustPort.lexOps VNaive.lexOps (WVRel C) (WVWeak C) WRustPort.lexOps.lexEofStep
      VNaive.lexOps.lexEofStep :=
  (wv_eofP C).toF _ _ _ _ Prod.fst preciseOf_fst

/-- The Rust port does with every consumer of the formalism what the naive lexer does. -/
theorem lexing_wRustPort_vNaive : lexing WRustPort.lexOps = lexing VNaive.lexOps :=
  lexing_alikeF _ _ WVRel WVWeak wvRel_new wv_slice wv_eof (fun _ _ _ h => h.1)
    (fun _ _ _ _ h => ⟨rfl, h.2⟩) (fun _ _ _ h => ⟨h.2.version, cr_weak h.2⟩)
    (fun _ _ _ h => h.1) (fun _ _ _ h => h.2)

end BSmtLib.Facts.Proofs.Lexer.VNaiveWRustPort.Calls

import BSmtLib.Proofs.VNaiveWRustPort.Loop
import BSmtLib.Proofs.VNaiveWRustPort.Eof
import BSmtLib.Proofs.VNaiveWRustPort.VEof
import BSmtLib.Proofs.Consumers.AlikeF

/-!
# The Rust port with every consumer, against the naive lexer

`lexing_wRustPort_vNaive`: what the adapter makes of the Rust port `WRustPort` with every
consumer of the spec is what it makes of the naive lexer (`Adapter.lexing`). Between two calls
the Rust port's lexer state corresponds to the naive lexer's (`CR`): the same version and
holding, and the naive lexer's pure state at its location, or both discard from the same
location. A call on a slice (`slice_step`) lexes it by the loop over its stops (`loop`, via
`inner_loop`) or discards it, where both lexers stay; a call at the end of the input (`eof_step`)
gives what both do there (`eofRes_unique`). The calls give results the spec does not tell apart
(`CallAlike`), which is what `lexing_alikeF` needs. With a consumer that does not take whitespace
and comments, the Rust port's calls never fail with the adapter's error `none`, which the
adapter's consumer answers when it is handed one (`slice_step_noNone`, `eof_step_noNone`).
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open BSmtLib.Proofs.Adapter VNaive BSmtLib.Proofs.Simulation
open Spec.Lexer (Handed)

variable {C : Spec.Lexer.Consumer}

theorem runIA_bind {α β : Type} (x : Lexer.WRustPort.InnerM (Answering C) AnswerM α)
    (f : α → Lexer.WRustPort.InnerM (Answering C) AnswerM β) (c : WCore) (coll : List Handed) :
    runIA (x >>= f) c coll = runIA (f (runIA x c coll).1.1) (runIA x c coll).1.2
        (runIA x c coll).2 := by
  simp only [runIA, StateT.run_bind]
  generalize ((x.run c).run {}).run coll = r
  obtain ⟨⟨⟨a, c'⟩, h⟩, t⟩ := r
  rw [answering_eq' h {}]
  rfl

theorem runIA_getThe (c : WCore) (coll : List Handed) :
    runIA (C := C) (getThe Lexer.WRustPort.LexerCore) c coll = ((c, c), coll) := rfl

theorem runIA_pure {α : Type} (a : α) (c : WCore) (coll : List Handed) :
    runIA (C := C) (pure a) c coll = ((a, c), coll) := rfl

theorem runIA_modifyThe (f : WCore → WCore) (c : WCore) (coll : List Handed) :
    runIA (C := C) (modifyThe Lexer.WRustPort.LexerCore f) c coll = (((), f c), coll) := rfl

/-- The Rust port's lexer state is the naive lexer's between two calls: the same version,
holding, and the naive lexer's pure state at its location, or both discard from the same
location. -/
structure CR (C : Spec.Lexer.Consumer) (c : WCore) (n : Core) : Prop where
  version : c.version = n.version
  initial : c.initialVersion = n.initialVersion
  holding : c.holding = n.holding
  recovers : c.recovers = false
  recoveryState : c.recoveryState = none
  loc : EofLoc c n.location
  rest : (∃ st, n.activity = st.activity ∧ StAgrees n.version C.concrete st c ∧
      c.discardedFrom = none) ∨
    (∃ s, n.activity = .discarding s ∧ c.discardedFrom = some s ∧ c.state = .normal)

theorem lexOps_lexSliceStepW (core : WCore) (held : Option (Located C.Result))
    (slice : ByteSlice) (taken : List Handed) :
    (WRustPort.lexOps.lexSliceStep (consumer := C) ⟨{}, core, held⟩ slice).run taken =
      match runIA (Lexer.WRustPort.lexSliceStep (H := Answering C) (m := AnswerM)
          (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ()) slice)
          core taken with
      | ((r, core'), taken') => ((r, ⟨{}, core', held⟩), taken') := by
  simp only [WRustPort.lexOps, Lexer.WRustPort.Lexer.run, StateT.run_bind]
  unfold runIA
  generalize (((Lexer.WRustPort.lexSliceStep (H := Answering C) (m := AnswerM) (R := C.Result)
    (E := Option C.Error) (LexRecovery.abandon Recovery.failFast)
    (LexRecovery.recover Recovery.failFast) slice).run core).run {}).run taken = r
  obtain ⟨⟨⟨res, core'⟩, h⟩, taken'⟩ := r
  rw [answering_eq' h {}]
  rfl

theorem lexOps_lexEofStepW (core : WCore) (held : Option (Located C.Result))
    (taken : List Handed) :
    (WRustPort.lexOps.lexEofStep (consumer := C) ⟨{}, core, held⟩).run taken =
      match runIA (Lexer.WRustPort.lexEofStep (H := Answering C) (m := AnswerM)
          (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ()))
          core taken with
      | ((r, core'), taken') => ((r, ⟨{}, core', held⟩), taken') := by
  simp only [WRustPort.lexOps, Lexer.WRustPort.Lexer.run, StateT.run_bind]
  unfold runIA
  generalize (((Lexer.WRustPort.lexEofStep (H := Answering C) (m := AnswerM) (R := C.Result)
    (E := Option C.Error) (LexRecovery.abandon Recovery.failFast)
    (LexRecovery.recover Recovery.failFast)).run core).run {}).run taken = r
  obtain ⟨⟨⟨res, core'⟩, h⟩, taken'⟩ := r
  rw [answering_eq' h {}]
  rfl

/-- Lexing a slice from the lexer state that is the naive lexer's pure state, as the naive
lexer's loop over its bytes. -/
theorem inner_loop (c : WCore) (n : Core) (st : St) (bytes : List UInt8) (taken : List Handed)
    (hfix : Fixed n.version n.holding n.initialVersion c) (hag : StAgrees n.version C.concrete st c)
    (hloc : EofLoc c n.location) (hver : c.version = n.version)
    (hact : n.activity = st.activity) :
    LoopRel C
      (runIA (Lexer.WRustPort.lexSliceInner (H := Answering C) (m := AnswerM) (R := C.Result)
        (E := Option C.Error) bytes.toByteArray.toByteSlice) c taken)
      (vBytes C n none bytes taken) := by
  rw [show vBytes C n none bytes taken = vBytes C n none (bytes.drop 0) taken by
    rw [List.drop_zero]]
  unfold runIA Lexer.WRustPort.lexSliceInner
  refine loop (C := C) bytes c.offset (bytes.length + 2) (c.offset - 1) (by omega) 0 none _ taken
    n st (by omega) ?_ hver hact (by rw [hloc.1]; rfl) (Nat.zero_le _)
  obtain ⟨h1, h2, h3⟩ := hloc
  exact ⟨⟨hfix.1, hfix.2, hfix.3, hfix.4, hfix.5, hfix.6⟩, rfl, by cases st <;> exact hag,
    ⟨by show n.location.offset = c.offset + (0 - 0); omega, h2, h3⟩,
    holds_of_len_zero rfl, rfl⟩

/-- What a call of the Rust port and one of the naive lexer give alike: results the spec does
not tell apart, the same tokens taken, lexer states that correspond again when the call does not
fail, and the same version and discarding always. -/
def CallAlike (C : Spec.Lexer.Consumer) {β : Type}
    (rW : (Except (LexError (Option C.Error)) β × WCore) × List Handed)
    (rV : VRes (Except (LexError (Option C.Error)) β)) : Prop :=
  rW.1.1.mapError failureOf = rV.1.1.mapError failureOf ∧ rW.2 = rV.2 ∧
    (rW.1.1.isOk = true → CR C rW.1.2 rV.1.2) ∧ rW.1.2.version = rV.1.2.version ∧
    rW.1.2.discardedFrom = discardedOf rV.1.2

/-- A call of the Rust port that lexes a slice, against the naive lexer's. -/
theorem slice_step (c : WCore) (n : Core) (bytes : List UInt8) (taken : List Handed)
    (h : CR C c n) :
    CallAlike C
      (runIA (Lexer.WRustPort.lexSliceStep (H := Answering C) (m := AnswerM)
        (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())
        bytes.toByteArray.toByteSlice) c taken)
      (vRun C (VNaive.lexSliceStep (H := Answering C) false (fun _ => pure ())
        (fun _ => pure ()) bytes.toByteArray.toByteSlice n) taken) := by
  rcases h.rest with ⟨st, hact, hag, hdf⟩ | ⟨s, hact, hdf, hstate⟩
  · have hp : n.Plain := by unfold Core.Plain; rw [hact]; cases st <;> trivial
    rw [lexSliceStep_vBytes C n hp bytes taken]
    unfold Lexer.WRustPort.lexSliceStep
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
    generalize runIA (Lexer.WRustPort.lexSliceInner (H := Answering C) (m := AnswerM)
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
        · refine ⟨rfl, rfl, fun _ => ⟨hok.version, hok.initial, hok.holding, hok.recovers,
            hok.recoveryState, a4, .inl ⟨st', a1, a2, a3⟩⟩, hok.version, ?_⟩
          show c'.discardedFrom = discardedOf n'
          rw [a3]
          unfold discardedOf
          rw [a1]
          cases st' <;> rfl
        · refine ⟨rfl, rfl, fun _ => ⟨hok.version, hok.initial, hok.holding, hok.recovers,
            hok.recoveryState, by rw [a5]; exact a4, .inr ⟨s, a1, a2, a3⟩⟩, hok.version, ?_⟩
          show c'.discardedFrom = discardedOf n'
          rw [a2]
          unfold discardedOf
          rw [a1]
    | error f =>
      cases resv with
      | ok _ => exact hm.elim
      | error g =>
        obtain ⟨hcf, hdWV, hrec⟩ := hm
        dsimp only
        unfold Lexer.WRustPort.fail
        rw [runIA_bind, runIA_bind, runIA_getThe]
        simp only [hrec, Bool.not_false, ↓reduceIte]
        refine ⟨?_, rfl, nofun, hv, hdWV⟩
        exact congrArg Except.error hcf
  · have hp : n.Plain := by unfold Core.Plain; rw [hact]; trivial
    rw [lexSliceStep_vBytes C n hp bytes taken]
    obtain ⟨n', hvb, b1, b2, b3, b4, b5⟩ := vBytes_discarding C bytes n none taken hact
    rw [hvb]
    unfold Lexer.WRustPort.lexSliceStep
    rw [runIA_bind, runIA_getThe]
    rw [ite_eq_left (by simp [hdf])]
    refine ⟨rfl, rfl, fun _ => ⟨h.version.trans b1.symm, h.initial.trans b5.symm,
      h.holding.trans b4.symm, h.recovers, h.recoveryState, by rw [b3]; exact h.loc,
      .inr ⟨s, b2, hdf, hstate⟩⟩, h.version.trans b1.symm, ?_⟩
    show c.discardedFrom = discardedOf n'
    rw [hdf]
    unfold discardedOf
    rw [b2]

/-- A call of the Rust port that lexes a slice, from a state that is the naive lexer's, with a
consumer that does not take whitespace and comments, does not fail with the adapter's error
`none`: the consumer is handed no whitespace or comment. -/
theorem slice_step_noNone (c : WCore) (n : Core) (bytes : List UInt8) (taken : List Handed)
    (h : CR C c n) (hc : C.concrete = false) :
    ∀ e, (runIA (Lexer.WRustPort.lexSliceStep (H := Answering C) (m := AnswerM)
        (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())
        bytes.toByteArray.toByteSlice) c taken).1.1 = .error e → e.cause ≠ .consumer none := by
  rcases h.rest with ⟨st, hact, hag, hdf⟩ | ⟨s, hact, hdf, hstate⟩
  · unfold Lexer.WRustPort.lexSliceStep
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
    generalize runIA (Lexer.WRustPort.lexSliceInner (H := Answering C) (m := AnswerM)
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
        unfold Lexer.WRustPort.fail
        rw [runIA_bind, runIA_bind, runIA_getThe]
        simp only [hrec, Bool.not_false, ↓reduceIte]
        intro e he
        cases he
        exact hnn hc
  · unfold Lexer.WRustPort.lexSliceStep
    rw [runIA_bind, runIA_getThe]
    rw [ite_eq_left (by simp [hdf])]
    intro e he
    cases he

/-- A call of the Rust port at the end of the input, against the naive lexer's. -/
theorem eof_step (c : WCore) (n : Core) (taken : List Handed) (h : CR C c n) :
    CallAlike C
      (runIA (Lexer.WRustPort.lexEofStep (H := Answering C) (m := AnswerM)
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
  have hW := (lexEofInner_eof (C := C) n.version c taken st n.location h.recovers hag h.loc).1
  unfold EofFin at hW
  rw [h.holding, h.version, hd0] at hW
  unfold Lexer.WRustPort.lexEofStep
  rw [runIA_bind, runIA_getThe]
  simp only [h.recoveryState]
  rw [ite_eq_right (by simp)]
  rw [runIA_bind]
  unfold Lexer.WRustPort.executeStep
  rw [runIA_bind]
  generalize runIA (Lexer.WRustPort.lexEofInner (H := Answering C) (m := AnswerM)
    (R := C.Result) (E := Option C.Error)) c taken = R at hW ⊢
  obtain ⟨⟨res, c'⟩, t⟩ := R
  obtain ⟨hW, hkeep⟩ := hW
  obtain ⟨hVr, hreset⟩ := hVr
  generalize vEnd C n taken = rv at hVr hreset ⊢
  obtain ⟨⟨resv, n'⟩, tv⟩ := rv
  dsimp only at hW hVr hkeep hreset
  obtain ⟨hres, htk, hweak⟩ := eofRes_unique hW hVr
  subst htk
  have hcur : c'.currentLocation = n.location := by
    obtain ⟨h1, h2, h3⟩ := h.loc
    show Location.mk (c'.offset + (c'.base - c'.base)) c'.line
      (c'.offset + (c'.base - c'.base) - c'.lineStart) = n.location
    rw [hkeep.offset, hkeep.line, hkeep.lineStart]
    cases hn : n.location
    rw [hn] at h1 h2 h3
    simp only at h1 h2 h3
    simp only [Location.mk.injEq]
    omega
  have hrec : c'.recovers = false := hkeep.recovers.trans h.recovers
  rcases res with f | flow
  · simp only [runIA_pure]
    rw [ite_eq_right (by simp)]
    rw [runIA_bind]
    unfold Lexer.WRustPort.fail
    rw [runIA_bind, runIA_getThe]
    simp only [hrec, Bool.not_false, ↓reduceIte, runIA_pure]
    obtain ⟨hv, hd⟩ := hweak rfl
    exact ⟨hres, rfl, nofun, hv, hd⟩
  · cases flow with
    | «continue» =>
      have hr : resv = .ok .continue := by
        cases resv <;> simp_all [innerRes, Except.mapError]
      subst hr
      have hn' := hreset rfl
      subst hn'
      simp only [runIA_pure]
      rw [runIA_bind]
      unfold Lexer.WRustPort.reset
      rw [runIA_modifyThe]
      exact ⟨rfl, rfl, fun _ => ⟨hkeep.initial.trans h.initial, hkeep.initial.trans h.initial, rfl,
        hrec, rfl, ⟨rfl, rfl, rfl⟩, .inl ⟨.idle, rfl, rfl, rfl⟩⟩,
        hkeep.initial.trans h.initial, rfl⟩
    | «break» r =>
      have hr : resv = .ok (.break ⟨r, n.location⟩) := by
        cases resv <;> simp_all [innerRes, Except.mapError]
      subst hr
      have hn' := hreset rfl
      subst hn'
      simp only [runIA_bind, runIA_getThe, runIA_pure]
      unfold Lexer.WRustPort.reset
      rw [runIA_modifyThe]
      refine ⟨?_, rfl, fun _ => ⟨hkeep.initial.trans h.initial, hkeep.initial.trans h.initial, rfl,
        hrec, rfl, ⟨rfl, rfl, rfl⟩, .inl ⟨.idle, rfl, rfl, rfl⟩⟩,
        hkeep.initial.trans h.initial, rfl⟩
      rw [hcur]

/-- A call of the Rust port at the end of the input, from a state that is the naive lexer's, with
a consumer that does not take whitespace and comments, does not fail with the adapter's error
`none`: the consumer is handed no whitespace or comment. -/
theorem eof_step_noNone (c : WCore) (n : Core) (taken : List Handed) (h : CR C c n)
    (hc : C.concrete = false) :
    ∀ e, (runIA (Lexer.WRustPort.lexEofStep (H := Answering C) (m := AnswerM)
        (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())) c
        taken).1.1 = .error e → e.cause ≠ .consumer none := by
  obtain ⟨st, hag⟩ : ∃ st, StAgrees n.version C.concrete st c := by
    rcases h.rest with ⟨st, -, hag, -⟩ | ⟨s, -, -, hstate⟩
    · exact ⟨st, hag⟩
    · exact ⟨.idle, hstate⟩
  have hW := lexEofInner_eof (C := C) n.version c taken st n.location h.recovers hag h.loc
  unfold Lexer.WRustPort.lexEofStep
  rw [runIA_bind, runIA_getThe]
  simp only [h.recoveryState]
  rw [ite_eq_right (by simp)]
  rw [runIA_bind]
  unfold Lexer.WRustPort.executeStep
  rw [runIA_bind]
  generalize runIA (Lexer.WRustPort.lexEofInner (H := Answering C) (m := AnswerM)
    (R := C.Result) (E := Option C.Error)) c taken = R at hW ⊢
  obtain ⟨⟨res, c'⟩, t⟩ := R
  obtain ⟨⟨-, hkeep⟩, hnn⟩ := hW
  dsimp only at hkeep hnn
  have hrec : c'.recovers = false := hkeep.recovers.trans h.recovers
  rcases res with f | flow
  · simp only [runIA_pure]
    rw [ite_eq_right (by simp)]
    rw [runIA_bind]
    unfold Lexer.WRustPort.fail
    rw [runIA_bind, runIA_getThe]
    simp only [hrec, Bool.not_false, ↓reduceIte, runIA_pure]
    intro e he
    cases he
    exact hnn hc f rfl
  · cases flow with
    | «continue» =>
      simp only [runIA_pure]
      rw [runIA_bind]
      unfold Lexer.WRustPort.reset
      rw [runIA_modifyThe]
      intro e he
      cases he
    | «break» r =>
      simp only [runIA_bind, runIA_getThe, runIA_pure]
      intro e he
      cases he

theorem cr_weak {c : WCore} {n : Core} (h : CR C c n) : c.discardedFrom = discardedOf n := by
  rcases h.rest with ⟨st, hact, -, hdf⟩ | ⟨s, hact, hdf, -⟩
  · rw [hdf]
    unfold discardedOf
    rw [hact]
    cases st <;> rfl
  · rw [hdf]
    unfold discardedOf
    rw [hact]

end BSmtLib.Proofs.Lexer.VNaiveWRustPort

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open BSmtLib.Proofs.Adapter VNaive

/-- The Rust port does with every consumer of the spec what the naive lexer does. -/
theorem lexing_wRustPort_vNaive : lexing WRustPort.lexOps = lexing VNaive.lexOps := by
  refine lexing_alikeF _ _ (fun C w n => w.held = n.held ∧ CR C w.core n.core)
    (fun C w n => w.core.version = n.core.version ∧ w.core.discardedFrom = discardedOf n.core)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro C version
    exact ⟨rfl, ⟨rfl, rfl, rfl, rfl, rfl, ⟨rfl, rfl, rfl⟩, .inl ⟨.idle, rfl, rfl, rfl⟩⟩⟩
  · intro C slice a b taken ⟨hh, hcr⟩
    obtain ⟨ha, ca, hda⟩ := a
    obtain ⟨hb, cb, hdb⟩ := b
    rw [answering_eq' ha {}, answering_eq' hb {}]
    simp only at hh hcr
    rw [lexOps_lexSliceStepW, lexOps_lexSliceStep]
    have hs := slice_step ca cb slice taken hcr
    generalize runIA (Lexer.WRustPort.lexSliceStep (H := Answering C) (m := AnswerM)
      (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())
      slice.toByteArray.toByteSlice) ca taken = rW at hs ⊢
    generalize vRun C (VNaive.lexSliceStep (H := Answering C) false (fun _ => pure ())
      (fun _ => pure ()) slice.toByteArray.toByteSlice cb) taken = rV at hs ⊢
    obtain ⟨⟨r, c'⟩, t⟩ := rW
    obtain ⟨⟨r', n'⟩, t'⟩ := rV
    obtain ⟨e1, e2, e3, e4, e5⟩ := hs
    exact ⟨e1, e2, fun hok => ⟨hh, e3 hok⟩, e4, e5⟩
  · intro C a b taken ⟨hh, hcr⟩
    obtain ⟨ha, ca, hda⟩ := a
    obtain ⟨hb, cb, hdb⟩ := b
    rw [answering_eq' ha {}, answering_eq' hb {}]
    simp only at hh hcr
    rw [lexOps_lexEofStepW, lexOps_lexEofStep]
    have hs := eof_step ca cb taken hcr
    generalize runIA (Lexer.WRustPort.lexEofStep (H := Answering C) (m := AnswerM)
      (R := C.Result) (E := Option C.Error) (fun _ => pure ()) (fun _ => pure ())) ca taken = rW
      at hs ⊢
    generalize vEnd C cb taken = rV at hs ⊢
    obtain ⟨⟨r, c'⟩, t⟩ := rW
    obtain ⟨⟨r', n'⟩, t'⟩ := rV
    obtain ⟨e1, e2, e3, e4, e5⟩ := hs
    exact ⟨e1, e2, fun hok => ⟨hh, e3 hok⟩, e4, e5⟩
  · intro C a b h
    exact h.1
  · intro C a b held h
    exact ⟨rfl, h.2⟩
  · intro C a b h
    exact ⟨h.2.version, cr_weak h.2⟩
  · intro C a b h
    exact h.1
  · intro C a b h
    exact h.2

end BSmtLib.Proofs.Lexer.VNaiveWRustPort

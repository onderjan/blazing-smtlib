import BSmtLib.Proofs.VNaiveWRustPort.LexStep
import BSmtLib.Proofs.VNaiveWRustPort.NoStop

/-!
# The Rust port at the end of the input

`lexEofInner_run`: the end of the input, from a lexer state that is the naive lexer's pure
state at a location, hands over what the naive lexer's end of the input finishes (`endStep`):
the token in progress, by the state's own check, and then the end-of-file token; or it fails
if the naive lexer's end fails, having handed over nothing more, or the consumer fails on a
lexeme. Each state of the lexer is compared with the naive lexer's `finish` on the token in
progress (`finishLs`). The handler that the Rust port wraps the token's hand-over in passes on
every error (`wp_tryCatch`), as the adapter's consumer never stops a hand-over.
-/

namespace BSmtLib.Proofs.Lexer.VNaiveWRustPort

open BSmtLib.Proofs.Adapter VNaive BSmtLib.Proofs.Simulation

section

variable {floor : Option Nat} {low : Nat} {α β : Type}

/-- A step whose interruptions the handler throws again, as it does with every error. -/
theorem wp_tryCatch {x : M floor low α} {h : Intr floor → M floor low α} {s : BS floor low}
    {coll : Collector} {Q : α → BS floor low → Collector → Prop}
    {QE : Intr floor → BS floor low → Collector → Prop}
    (hx : WP x s coll Q QE) (hh : ∀ e, IsErr e → h e = throw e) :
    WP (tryCatch x h) s coll Q QE := by
  unfold WP at hx ⊢
  have e : runM (tryCatch x h) s coll =
      match runM x s coll with
      | ((.ok a, s'), coll') => ((.ok a, s'), coll')
      | ((.error e, s'), coll') => runM (h e) s' coll' := by
    simp only [runM, tryCatch, tryCatchThe, MonadExcept.tryCatch, StateT.run_bind,
      MonadExceptOf.tryCatch, ExceptT.tryCatch, ExceptT.run, ExceptT.mk]
    generalize (StateT.run x s).run coll = r
    obtain ⟨⟨r, s'⟩, coll'⟩ := r
    cases r <;> rfl
  rw [e]
  generalize runM x s coll = r at hx ⊢
  obtain ⟨⟨r, s'⟩, coll'⟩ := r
  cases r with
  | ok a => exact hx
  | error err =>
    dsimp only
    rw [hh err hx.1]
    exact hx

/-- Running a step inside the loop over a slice. -/
theorem run_step (x : M floor low α) (s : BS floor low)
    (k : Except (Intr floor) α × BS floor low → StateT Collector Id β) (coll : Collector) :
    (StateT.run (ExceptT.run x) s >>= k).run coll =
      (k (runM x s coll).1).run (runM x s coll).2 := rfl

end

/-! ## The naive lexer at the end of the input -/

/-- The lexemes that the end of the input finishes before the end-of-file one, or none on an
error. -/
def finishLs (st : St) (location : Location) : Option (List Lexeme) :=
  match st with
  | .idle => some []
  | .token p =>
    match finish false p location with
    | .none => some []
    | .token l => some [l]
    | .error _ => none

theorem endStep_eq (st : St) (location : Location) :
    endStep st location = (finishLs st location).map (· ++ [eofLexeme location]) := by
  cases st with
  | idle => rfl
  | token p =>
    simp only [endStep, finishLs]
    cases finish false p location <;> rfl

/-- What the lexer state says of the location at the end of the input: that of its offset, on
its line. -/
def EofLoc (c : WCore) (location : Location) : Prop :=
  location.offset = c.offset ∧ location.line = c.line ∧
    c.lineStart + location.column = location.offset

theorem eof_stepLocation {c c' : WCore} {location : Location} (h : EofLoc c location)
    (hl : c'.line = c.line) (hs : c'.lineStart = c.lineStart) :
    stepLocation c' c.offset 0 0 = location := by
  obtain ⟨h1, h2, h3⟩ := h
  cases location
  simp only [stepLocation, Location.mk.injEq] at h1 h2 h3 ⊢
  refine ⟨by omega, by rw [hl, h2], by rw [hs]; omega⟩

set_option hygiene false in
/-- The digits of a hexadecimal or binary literal at the end of the input, in the proof of
`lexEofInner_run`. -/
local macro "eof_digits" : tactic => `(tactic| (
  unfold Lexer.WRustPort.finishDigitRun
  apply wp_bind; apply wp_getCore
  dsimp only
  apply wp_ite
  · intro hbad
    unfold Lexer.WRustPort.error Lexer.WRustPort.errorWith
    wp_walk
    refine ⟨?_, fun _ => rfl⟩
    show Option.bind _ _ = none
    have he : (contentBytes c.tokenContent).isEmpty = true := by
      unfold ByteArray.isEmpty; rw [size_contentBytes (token_fits hagree)]; exact hbad
    simp [finishLs, finish, he]
  · intro hgood
    refine hsink _ _ (token_fits hagree) ?_
    have he : (contentBytes c.tokenContent).isEmpty = false := by
      unfold ByteArray.isEmpty; rw [size_contentBytes (token_fits hagree)]
      exact Bool.eq_false_iff.mpr hgood
    simp [finishLs, finish, he]
    rfl))

/-- The end of the input from the lexer state that is the naive lexer's pure state at
`location` hands over what the naive lexer's end of the input finishes, or fails if that fails
or the consumer fails on a lexeme. -/
theorem lexEofInner_run (v : Version) (c : WCore) (coll : Collector) (st : St)
    (location : Location) (hfix : Fixed v c) (hagree : StAgrees v st c)
    (hloc : EofLoc c location) :
    match ((Lexer.WRustPort.lexEofInner (H := Collector) (m := Id) (R := Empty) (E := Unit)) c).run
      coll with
    | ((res, _), coll') =>
      match (endStep st location).bind (handedAll v) with
      | some hs => res = .ok .continue ∧ coll'.handed = coll.handed ++ hs
      | none => (∃ f, res = .error f) ∧
        (endStep st location = none → coll'.handed = coll.handed) := by
  unfold Lexer.WRustPort.lexEofInner
  simp -zeta only [rust_eofBatch]
  extract_lets c1 tokenStart offset pend step
  have hp : ∀ s : BS none offset, s.val = c1 →
      WP pend s coll
        (fun _ s' coll' => s'.val.version = v ∧ s'.val.recovers = false ∧
          s'.val.offset = c.offset ∧ s'.val.line = c.line ∧ s'.val.lineStart = c.lineStart ∧
          ∃ ls, finishLs st location = some ls ∧ pending v coll' [] = pending v coll ls)
        (fun _ _ coll' => (finishLs st location).bind (pending v coll) = none ∧
          (finishLs st location = none → coll'.handed = coll.handed)) := by
    intro s hs
    obtain ⟨sv, sp⟩ := s
    simp only at hs
    subst hs
    -- a token handed over at the end of the input
    have hsink : ∀ (ty : TokenCategory) (h : Lexer.WRustPort.Started none offset tokenStart),
        Fits c.tokenContent →
        finishLs st location = some [⟨ty, contentBytes c.tokenContent, c.tokenStart, location⟩] →
        WP (Lexer.WRustPort.sinkStored (H := Collector) (m := Id) (R := Empty) (E := Unit) ty
          .EOF tokenStart 0 h) ⟨c1, sp⟩ coll
          (fun _ s' coll' => s'.val.version = v ∧ s'.val.recovers = false ∧
            s'.val.offset = c.offset ∧ s'.val.line = c.line ∧ s'.val.lineStart = c.lineStart ∧
            ∃ ls, finishLs st location = some ls ∧ pending v coll' [] = pending v coll ls)
          (fun _ _ coll' => (finishLs st location).bind (pending v coll) = none ∧
            (finishLs st location = none → coll'.handed = coll.handed)) := by
      intro ty h hfits hfin
      refine sinkStored_wp v ty .EOF tokenStart 0 h [] ⟨c1, sp⟩ (holds_clear _ _) coll
        hfix.recovers hfix.version hfits ?_ ?_
      · intro s' coll' hk hb hc
        obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11⟩ := key_fields hk
        refine ⟨k1.trans hfix.version, k4.trans hfix.recovers, k8, k10, k11, _, hfin, ?_⟩
        have e1 : stepLocation c1 c.offset 0 0 = location := eof_stepLocation hloc rfl rfl
        rw [hc]
        show pending v coll ([] ++ [⟨ty, contentBytes c.tokenContent, c.tokenStart,
          stepLocation c1 c.offset 0 0⟩]) = _
        rw [e1]
        rfl
      · intro hn e s' coll'
        refine ⟨?_, fun h => by rw [hfin] at h; cases h⟩
        show Option.bind _ _ = none
        rw [hfin]
        have e1 : stepLocation c1 c.offset 0 0 = location := eof_stepLocation hloc rfl rfl
        have hn' : pending v coll ([] ++ [⟨ty, contentBytes c.tokenContent, c.tokenStart,
          stepLocation c1 c.offset 0 0⟩]) = none := hn
        rw [e1] at hn'
        exact hn'
    unfold pend
    cases st with
    | idle =>
      split
      next => exact wp_pure _ ⟨hfix.version, hfix.recovers, rfl, rfl, rfl, [], rfl, rfl⟩
      all_goals
        exfalso
        have h := ‹c1.state = _›
        rw [show c1.state = c.state from rfl, show c.state = .normal from hagree] at h
        cases h
    | token p =>
      split
      next =>
        exfalso
        exact (token_agrees hagree ‹c1.state = _›).2
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        exact hsink _ _ (token_fits hagree) rfl
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.WRustPort.finishDecimal
        apply wp_bind; apply wp_getCore
        dsimp only
        apply wp_ite
        · intro hbad
          have hbad' : ((lastOf (contentBytes c.tokenContent)).isNone ||
              lastOf (contentBytes c.tokenContent) == some 46) = true := by
            rw [← last?_stored (token_fits hagree)]; exact hbad
          unfold Lexer.WRustPort.error Lexer.WRustPort.errorWith
          wp_walk
          refine ⟨?_, fun _ => rfl⟩
          show Option.bind _ _ = none
          simp only [finishLs, finish, hbad', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rfl
        · intro hgood
          have hgood' : ((lastOf (contentBytes c.tokenContent)).isNone ||
              lastOf (contentBytes c.tokenContent) == some 46) = false := by
            rw [← last?_stored (token_fits hagree)]; exact Bool.eq_false_iff.mpr hgood
          refine hsink _ _ (token_fits hagree) ?_
          simp only [finishLs, finish, hgood', Bool.not_false, ↓reduceIte]
      next =>
        obtain ⟨hps, hm, hcont, -⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        exact hsink _ _ (token_fits hagree) rfl
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        eof_digits
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        eof_digits
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.WRustPort.error Lexer.WRustPort.errorWith
        wp_walk
        refine ⟨?_, fun _ => rfl⟩
        rfl
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.WRustPort.error Lexer.WRustPort.errorWith
        wp_walk
        refine ⟨?_, fun _ => rfl⟩
        show Option.bind _ _ = none
        split <;> rfl
      next =>
        obtain ⟨hps, -, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.WRustPort.error Lexer.WRustPort.errorWith
        wp_walk
        refine ⟨?_, fun _ => rfl⟩
        rfl
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.WRustPort.finishStringLiteral
        exact hsink _ _ (token_fits hagree) (by show finishLs (.token ⟨_, _, _⟩) location = _; split
            <;> rfl)
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.WRustPort.finishSimpleSymbol
        exact hsink _ _ (token_fits hagree) rfl
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.WRustPort.finishKeyword
        apply wp_bind; apply wp_getCore
        dsimp only
        apply wp_ite
        · intro hbad
          unfold Lexer.WRustPort.error Lexer.WRustPort.errorWith
          wp_walk
          refine ⟨?_, fun _ => rfl⟩
          show Option.bind _ _ = none
          have he : (contentBytes c.tokenContent).isEmpty = true := by
            unfold ByteArray.isEmpty; rw [size_contentBytes (token_fits hagree)]; exact hbad
          simp [finishLs, finish, he]
        · intro hgood
          refine hsink _ _ (token_fits hagree) ?_
          have he : (contentBytes c.tokenContent).isEmpty = false := by
            unfold ByteArray.isEmpty; rw [size_contentBytes (token_fits hagree)]
            exact Bool.eq_false_iff.mpr hgood
          simp [finishLs, finish, he]
      next =>
        obtain ⟨hps, hm, hcont⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm hcont
        subst hm hps hcont
        unfold Lexer.WRustPort.error Lexer.WRustPort.errorWith
        wp_walk
        refine ⟨?_, fun _ => rfl⟩
        rfl
      next =>
        exfalso
        exact (token_agrees hagree ‹c1.state = _›).2
      next =>
        obtain ⟨hps, hm⟩ := token_agrees hagree ‹c1.state = _›
        obtain ⟨mode, pstart, pcontent⟩ := p
        simp only at hps hm
        subst hm hps
        unfold Lexer.WRustPort.consumesWhitespaceAndComments
        apply wp_bind; apply wp_pure
        simp only [collector_ws, Bool.false_eq_true, ↓reduceIte]
        exact wp_pure _ ⟨hfix.version, hfix.recovers, rfl, rfl, rfl, [], rfl, rfl⟩
  -- the end of the input: the token in progress, then the end-of-file token
  have hstep : ∀ s : BS none offset, s.val = c1 →
      WP step s coll
        (fun _ _ coll' => ∃ ls, finishLs st location = some ls ∧
          pending v coll' [] = pending v coll (ls ++ [eofLexeme location]))
        (fun _ _ coll' => (finishLs st location).bind
          (fun ls => pending v coll (ls ++ [eofLexeme location])) = none ∧
          (finishLs st location = none → coll'.handed = coll.handed)) := by
    intro s hs
    unfold step
    apply wp_bind
    refine wp_tryCatch (wp_mono (hp s hs) (fun _ s' coll' h => ?_) (fun _ _ _ h => ?_)) ?_
    · obtain ⟨hv', hr', ho', hl', hls', ls, hfin, hc⟩ := h
      unfold Lexer.WRustPort.startToken Lexer.WRustPort.modifyContent
      apply wp_bind
      apply wp_bind; apply wp_getCore
      apply wp_bind; apply wp_modifyCore
      apply wp_bind; apply wp_modifyCore
      apply wp_pure
      dsimp only
      have hl : (⟨offset + (0 - 0), s'.val.line, offset + (0 - 0) - s'.val.lineStart⟩ :
          Location) = location := by
        obtain ⟨h1, h2, h3⟩ := hloc
        cases location
        simp only [Location.mk.injEq] at h1 h2 h3 ⊢
        refine ⟨by show c.offset + 0 = _; omega, by rw [hl', h2], ?_⟩
        show c.offset + 0 - s'.val.lineStart = _
        rw [hls']
        omega
      refine sinkEof_wp v _ _ coll' ?_ ?_ ?_ ?_
      · exact hr'
      · exact hv'
      · intro coll3 hc3
        rw [hl] at hc3
        exact ⟨ls, hfin, hc3.trans (by
          have := pending_congr_append hc [eofLexeme location]
          rwa [List.nil_append] at this)⟩
      · intro hn e s3 coll3
        rw [hl] at hn
        refine ⟨?_, fun h => by rw [hfin] at h; cases h⟩
        show Option.bind _ _ = none
        rw [hfin]
        have := pending_congr_append hc [eofLexeme location]
        rw [List.nil_append] at this
        exact this.symm.trans hn
    · refine ⟨?_, h.2⟩
      show Option.bind _ _ = none
      cases hf : finishLs st location with
      | none => rfl
      | some ls =>
        rw [hf] at h
        exact pending_none_append h.1 _
    · intro e ⟨cause, hc⟩
      simp only [hc]
  rw [run_step]
  have hw := hstep ⟨c1, ⟨Nat.le_refl _, fun _ h => nomatch h⟩⟩ rfl
  unfold WP at hw
  generalize runM step ⟨c1, ⟨Nat.le_refl _, fun _ h => nomatch h⟩⟩ coll = r at hw ⊢
  obtain ⟨⟨res, s'⟩, coll'⟩ := r
  rw [endStep_eq]
  cases res with
  | ok u =>
    obtain ⟨ls, hfin, hc⟩ := hw
    rw [hfin]
    simp only [Option.map_some, Option.bind_some]
    rw [pending_nil] at hc
    cases hh : handedAll v (ls ++ [eofLexeme location]) with
    | none =>
      rw [pending_none hh] at hc
      cases hc
    | some hs =>
      rw [pending_some hh] at hc
      exact ⟨rfl, Option.some.inj hc⟩
  | error e =>
    obtain ⟨⟨cause, hc⟩, hf, hcoll⟩ := hw
    have hnone : ((finishLs st location).map (· ++ [eofLexeme location])).bind (handedAll v) =
        none := by
      cases hfl : finishLs st location with
      | none => rfl
      | some ls =>
        rw [hfl] at hf
        simp only [Option.bind_some] at hf
        simp only [Option.map_some, Option.bind_some]
        simpa [pending] using hf
    rw [hnone]
    simp only [hc]
    exact ⟨⟨_, rfl⟩, fun h => hcoll (Option.map_eq_none_iff.mp h)⟩

end BSmtLib.Proofs.Lexer.VNaiveWRustPort

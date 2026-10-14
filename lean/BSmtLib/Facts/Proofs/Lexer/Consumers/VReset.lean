module

public import BSmtLib.Facts.Proofs.Lexer.Consumers.VWalk
import all BSmtLib.Lexer.Internal.VNaive

@[expose] public section

/-!
# The end of the input resets the naive lexer

The naive lexer stays lexing or discarding under its initial version through every call
(`vBytes_iv`, `vEnd_inv`, `runInput_reset`), and the end of the input, when the lexer finishes,
leaves it as it was constructed (`resetsAtEnd_vNaive`).
-/

namespace BSmtLib.Facts.Proofs.Lexer.Consumers.VReset

open BSmtLib.Facts.Lexer.Adapters
open BSmtLibSpec.Lexer (Handed)
open BSmtLib.Facts.Proofs.Lexer.Consumers.Pure BSmtLib.Facts.Proofs.Lexer.Consumers.VEnd
open BSmtLib.Facts.Proofs.Lexer.Consumers.VHold BSmtLib.Facts.Proofs.Lexer.Consumers.VSession
open BSmtLib.Facts.Proofs.Lexer.Consumers.VSession.Core BSmtLib.Facts.Proofs.Lexer.Consumers.VSteps
open BSmtLib.Facts.Proofs.Lexer.Consumers.VWalk BSmtLib.Facts.Proofs.Lexer.VNaive.Run
open BSmtLib.Lexer.Error BSmtLib.Lexer.Internal.VNaive

section
variable (consumer : BSmtLibSpec.Lexer.Consumer)

theorem handOverAt_iv (X : Core) (l : Lexeme) (hl : l.Valid) (taken : List Handed) :
    (vRun consumer (handOverAt (H := Answering consumer) X l hl) taken).1.2.initialVersion =
      X.initialVersion := by
  cases hh : X.holding with
  | true => rw [handOverAt_holding consumer X l hl hh]
  | false =>
    rw [handOverAt_reply consumer X l hl hh]
    generalize reply consumer X.version taken l = r
    obtain ⟨answer, version, discards, taken'⟩ := r
    cases answer with
    | error e =>
      show (coreAfterError X l version discards).initialVersion = _
      unfold coreAfterError; split <;> rfl
    | ok flow => cases flow <;> exact (coreAfter_fields X l version discards).2.2.2.2

theorem lexStart_iv (core : Core) (b : UInt8) (taken : List Handed) :
    (vRun consumer (lexStart (H := Answering consumer) core b) taken).1.2.initialVersion =
      core.initialVersion := by
  cases hs : start core.version consumer.concrete core.location b with
  | idle =>
    obtain ⟨core', h, -, -, -, -, hi⟩ := lexStart_none consumer core b taken (st := .idle)
      (by simp [startStepW, hs])
    rw [h]; exact hi
  | pending p =>
    obtain ⟨core', h, -, -, -, -, hi⟩ := lexStart_none consumer core b taken (st := .token p)
      (by simp [startStepW, hs])
    rw [h]; exact hi
  | token l =>
    obtain ⟨hl, h⟩ := lexStart_token consumer core b taken hs
    rw [h, handOverAt_iv]; rfl
  | error f => rw [lexStart_error' consumer core b taken hs]

theorem vByte_iv (core : Core) (b : UInt8) (taken : List Handed) (hp : (Plain core)) :
    (vByte consumer core b taken).1.2.initialVersion = core.initialVersion := by
  unfold Core.Plain at hp
  split at hp
  · rename_i ha
    rw [lexByte_idle consumer core b taken ha, lexStart_iv]
  · rename_i p ha
    cases hadv : advance consumer.concrete p core.location b with
    | pending p' =>
      obtain ⟨core', h, -, -, -, -, hi⟩ := lexByte_pending consumer core b taken ha hadv
      rw [h]; exact hi
    | idle =>
      obtain ⟨core', h, -, -, -, -, hi⟩ := lexByte_advance_idle consumer core b taken ha hadv
      rw [h]; exact hi
    | tokenWith l =>
      obtain ⟨hl, h⟩ := lexByte_tokenWith consumer core b taken ha hadv
      rw [h, handOverAt_iv]; rfl
    | tokenBefore l =>
      obtain ⟨hl, h⟩ := lexByte_tokenBefore consumer core b taken ha hadv
      have hiv := handOverAt_iv consumer (idleAt core) l hl taken
      generalize hr : vRun consumer (handOverAt (H := Answering consumer) (idleAt core) l hl)
        taken = r at hiv
      obtain ⟨⟨res, core2⟩, taken2⟩ := r
      rw [h hr]
      simp only at hiv
      cases res with
      | error f => exact hiv
      | ok held =>
        cases held with
        | none =>
          dsimp only
          split
          · simp only [discardingAfter]; exact hiv
          · rw [lexStart_iv]; exact hiv
        | some located =>
          dsimp only
          split
          · simp only [discardingAfter]; exact hiv
          · have := lexStart_iv consumer core2 b taken2
            generalize vRun consumer (lexStart (H := Answering consumer) core2 b) taken2 = r3
              at this
            obtain ⟨⟨r3, core3⟩, taken3⟩ := r3
            exact this.trans hiv
    | error f =>
      rw [lexByte_advance_error consumer core b taken ha hadv]
  · rename_i s ha
    obtain ⟨core', h, -, -, -, -, hi⟩ := lexByte_discarding consumer core b taken ha
    rw [h]; exact hi
  · exact hp.elim

theorem vBytes_iv (bytes : List UInt8) :
    ∀ (core : Core) (held : Option (Span.Located consumer.Result)) (taken : List Handed),
      (Plain core) →
      (vBytes consumer core held bytes taken).1.2.initialVersion = core.initialVersion := by
  induction bytes with
  | nil => intro core held taken hp; rfl
  | cons c bytes ih =>
    intro core held taken hp
    have h := vByte_iv consumer core c taken hp
    have hp' := vByte_plain consumer core c taken hp
    simp only [vBytes]
    generalize vByte consumer core c taken = r at h hp'
    obtain ⟨⟨res, core'⟩, taken'⟩ := r
    simp only at h hp'
    cases res with
    | error f => exact h
    | ok held' => cases held' <;> exact (ih _ _ _ hp').trans h


theorem handOverAt_none_holding {X core2 : Core} {l : Lexeme} {hl : l.Valid}
    {taken taken2 : List Handed}
    (h : vRun consumer (handOverAt (H := Answering consumer) X l hl) taken =
      ((.ok none, core2), taken2)) : core2.holding = false := by
  cases hh : X.holding with
  | true => rw [handOverAt_holding consumer X l hl hh] at h; cases h
  | false =>
    rw [handOverAt_reply consumer X l hl hh] at h
    generalize reply consumer X.version taken l = r at h
    obtain ⟨answer, version, discards, taken'⟩ := r
    cases answer with
    | error e => cases h
    | ok flow =>
      cases flow with
      | «continue» =>
        simp only [Prod.mk.injEq] at h
        obtain ⟨⟨-, rfl⟩, -⟩ := h
        rw [(coreAfter_fields X l version discards).2.2.2.1, hh]
      | «break» v => cases h

theorem handOverAt_plain {X : Core} {l : Lexeme} {hl : l.Valid} {taken : List Handed}
    (hX : X.activity = .idle ∨ ∃ s, X.activity = .discarding s) :
    (Plain (vRun consumer (handOverAt (H := Answering consumer) X l hl) taken).1.2) := by
  rcases handOverAt_activity consumer X l hl taken with h | ⟨s, h⟩
  · unfold Core.Plain; rw [h]; rcases hX with hX | ⟨s, hX⟩ <;> rw [hX] <;> trivial
  · unfold Core.Plain; rw [h]; trivial

/-- What the end of the input leaves the lexer in: reset if it does not fail. -/
theorem vEnd_inv (core : Core) (taken : List Handed) (hp : (Plain core)) :
    match vEnd consumer core taken with
    | ((.ok _, core'), _) => core' = Core.initial core.initialVersion
    | ((.error _, core'), _) => (Plain core') ∧ core'.initialVersion = core.initialVersion := by
  -- the end-of-file token handed over from a lexer with nothing in progress, or discarding
  have eof : ∀ (X : Core) {t : List Handed} {r core2 taken2 : _},
      (X.activity = .idle ∨ ∃ s, X.activity = .discarding s) →
      X.initialVersion = core.initialVersion →
      vRun consumer (handOverAt (H := Answering consumer) X (eofAt core.location)
        (eofAt_valid _)) t = ((r, core2), taken2) →
      match (match r with
          | .ok none => ((.ok .continue, core2.reset), taken2)
          | .ok (some located) => ((.ok (.break located), core2.reset), taken2)
          | .error f => ((.error ⟨f.cause, f.span, none⟩, core2), taken2) :
          VRes (Except (LexError (Option consumer.Error))
              (ControlFlow (Span.Located consumer.Result))))
        with
      | ((.ok _, core'), _) => core' = Core.initial core.initialVersion
      | ((.error _, core'), _) => (Plain core') ∧ core'.initialVersion = core.initialVersion := by
    intro X t r core2 taken2 hX hiv hr
    have hiv2 := handOverAt_iv consumer X (eofAt core.location) (eofAt_valid _) t
    have hp2 := handOverAt_plain consumer (taken := t) (hl := eofAt_valid core.location) hX
    rw [hr] at hiv2 hp2
    simp only at hiv2 hp2
    cases r with
    | error f => exact ⟨hp2, hiv2.trans hiv⟩
    | ok held =>
      cases held <;> simp only [Core.reset] <;> rw [hiv2, hiv]
  unfold Core.Plain at hp
  split at hp
  · -- nothing in progress
    rename_i ha
    cases hh : core.holding with
    | true => rw [vEnd_held consumer core taken (.inl ha) hh]; rfl
    | false =>
      generalize hr : vRun consumer (handOverAt (H := Answering consumer) core
        (eofAt core.location) (eofAt_valid _)) taken = R
      obtain ⟨⟨r, core2⟩, taken2⟩ := R
      rw [vEnd_eof consumer core taken (.inl ha) hh hr]
      exact eof core (.inl ha) rfl hr
  · -- a token in progress
    rename_i p ha
    cases hf : finish consumer.concrete p core.location with
    | none =>
      cases hh : core.holding with
      | true => rw [(vEnd_finish_none consumer core taken ha hf).1 hh]; rfl
      | false =>
        generalize hr : vRun consumer (handOverAt (H := Answering consumer) (idleAt core)
          (eofAt core.location) (eofAt_valid _)) taken = R
        obtain ⟨⟨r, core2⟩, taken2⟩ := R
        rw [(vEnd_finish_none consumer core taken ha hf).2 hh hr]
        exact eof (idleAt core) (.inl rfl) rfl hr
    | token l =>
      obtain ⟨hl, h1, h2, h3⟩ := vEnd_finish_token consumer core taken ha hf
      have hiv := handOverAt_iv consumer (idleAt core) l hl taken
      have hp2 := handOverAt_plain consumer (taken := taken) (hl := hl)
        (X := idleAt core) (.inl rfl)
      generalize hr : vRun consumer (handOverAt (H := Answering consumer) (idleAt core) l hl)
        taken = R at hiv hp2
      obtain ⟨⟨r, core2⟩, taken2⟩ := R
      simp only at hiv hp2
      cases r with
      | error f => rw [h1 hr]; exact ⟨hp2, hiv⟩
      | ok held =>
        cases held with
        | some located => rw [h2 hr]; simp only [Core.reset]; rw [hiv]; rfl
        | none =>
          have hh2 := handOverAt_none_holding consumer hr
          generalize hr3 : vRun consumer (handOverAt (H := Answering consumer) core2
            (eofAt core.location) (eofAt_valid _)) taken2 = R3
          obtain ⟨⟨r3, core3⟩, taken3⟩ := R3
          rw [h3 hh2 hr hr3]
          have hiv3 := handOverAt_iv consumer core2 (eofAt core.location) (eofAt_valid _) taken2
          have hp3 : core2.activity = .idle ∨ ∃ s, core2.activity = .discarding s := by
            unfold Core.Plain at hp2
            split at hp2
            · exact .inl ‹_›
            · rename_i q hq
              exfalso
              rcases handOverAt_activity consumer (idleAt core) l hl taken with h' | ⟨s, h'⟩ <;>
                rw [hr] at h' <;> simp only at h' <;> rw [hq] at h' <;> cases h'
            · exact .inr ⟨_, ‹_›⟩
            · exact hp2.elim
          exact eof core2 hp3 hiv hr3
    | error f =>
      rw [vEnd_finish_error consumer core taken ha hf]
      exact ⟨by simp [Core.Plain, ha], rfl⟩
  · -- discarding
    rename_i s ha
    cases hh : core.holding with
    | true => rw [vEnd_held consumer core taken (.inr ⟨s, ha⟩) hh]; rfl
    | false =>
      generalize hr : vRun consumer (handOverAt (H := Answering consumer) core
        (eofAt core.location) (eofAt_valid _)) taken = R
      obtain ⟨⟨r, core2⟩, taken2⟩ := R
      rw [vEnd_eof consumer core taken (.inr ⟨s, ha⟩) hh hr]
      exact eof core (.inr ⟨s, ha⟩) rfl hr
  · exact hp.elim


/-- An input fed to the end keeps the lexer lexing or discarding, under its initial version, and
resets it when it finishes. -/
theorem runInput_reset (slices : List BSmtLibSpec.Regex.Chars) :
    ∀ (core : Core) (held : Option (Span.Located consumer.Result)) (taken : List Handed),
        (Plain core) →
      let r := (VNaive.lexOps.runInput (consumer := consumer) ⟨{}, core, held⟩ true slices).run
        taken
      (Plain r.1.2.core) ∧ r.1.2.core.initialVersion = core.initialVersion ∧
        (r.1.1.isFinished = true → r.1.2 = ⟨{}, Core.initial core.initialVersion, none⟩) := by
  induction slices with
  | nil =>
    intro core held taken hp
    have hv := vEnd_inv consumer core taken hp
    simp only [LexOps.runInput, ite_true, StateT.run_bind, lexOps_lexEofStep]
    generalize vEnd consumer core taken = R at hv
    obtain ⟨⟨res, core'⟩, taken'⟩ := R
    cases res with
    | error e =>
      obtain ⟨h1, h2⟩ := hv
      exact ⟨h1, h2, nofun⟩
    | ok flow =>
      simp only at hv
      subst hv
      simp only [id_bind]
      generalize eofResult _ flow = E
      cases E <;> exact ⟨trivial, rfl, fun _ => rfl⟩
  | cons slice slices ih =>
    intro core held taken hp
    simp only [LexOps.runInput, StateT.run_bind, lexOps_lexSliceStep]
    rw [lexSliceStep_vBytes consumer core hp slice taken]
    have hpl := vBytes_plain consumer slice core none taken hp
    have hiv := vBytes_iv consumer slice core none taken hp
    generalize vBytes consumer core none slice taken = R at hpl hiv
    obtain ⟨⟨res, core'⟩, taken'⟩ := R
    simp only at hpl hiv
    cases res with
    | error f => exact ⟨hpl, hiv, nofun⟩
    | ok h =>
      simp only [id_bind]
      obtain ⟨h1, h2, h3⟩ := ih core' (h.or held) taken' hpl
      exact ⟨h1, h2.trans hiv, fun hf => by have := h3 hf; rw [hiv] at this; exact this⟩

end

theorem vLexer_eta {consumer : BSmtLibSpec.Lexer.Consumer} (L : VNaive.lexOps.Lexer consumer) :
    L = ⟨{}, L.core, L.held⟩ := by
  obtain ⟨h, c, d⟩ := L
  rw [answering_eq h {}]

/-- The earlier inputs keep the lexer lexing or discarding, under the version it was constructed
with. -/
theorem foldl_inputs_inv {consumer : BSmtLibSpec.Lexer.Consumer} (version : Token.Version)
    (inputs : List (List BSmtLibSpec.Regex.Chars)) :
    ∀ (L : VNaive.lexOps.Lexer consumer), (Plain L.core) → L.core.initialVersion = version →
      (Plain (inputs.foldl (VNaive.lexOps.next consumer version) L).core) ∧
      (inputs.foldl (VNaive.lexOps.next consumer version) L).core.initialVersion = version := by
  induction inputs with
  | nil => intro L hp hv; exact ⟨hp, hv⟩
  | cons input inputs ih =>
    intro L hp hv
    simp only [List.foldl_cons]
    apply ih
    all_goals
      unfold LexOps.next
      rw [vLexer_eta L]
      obtain ⟨h1, h2, -⟩ := runInput_reset consumer input L.core L.held [] hp
      generalize ((VNaive.lexOps.runInput ⟨{}, L.core, L.held⟩ true input).run []).1 = r at h1 h2
      obtain ⟨o, L'⟩ := r
      cases o
    all_goals first | exact trivial | exact rfl | assumption | exact h2.trans hv

/-- The end of the input resets the naive lexer. -/
theorem resetsAtEnd_vNaive : BSmtLibSpec.Lexer.ResetsAtEnd (lexing VNaive.lexOps) := by
  intro consumer version earlier first slices ended hfin
  unfold lexing at hfin ⊢
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  generalize hL : earlier.foldl (VNaive.lexOps.next consumer (toVersion version))
    (VNaive.lexOps.new consumer {} (toVersion version)) = L at hfin ⊢
  obtain ⟨hp, hiv⟩ := foldl_inputs_inv (consumer := consumer) (toVersion version) earlier
    (VNaive.lexOps.new consumer {} (toVersion version)) trivial rfl
  rw [hL] at hp hiv
  rw [vLexer_eta L] at hfin ⊢
  obtain ⟨-, -, h3⟩ := runInput_reset consumer first L.core L.held [] hp
  simp only at hfin
  unfold LexOps.next
  generalize hr : (VNaive.lexOps.runInput ⟨{}, L.core, L.held⟩ true first).run [] = r at hfin h3
  obtain ⟨⟨o, L'⟩, t⟩ := r
  simp only at hfin h3 ⊢
  cases o with
  | finished value location =>
    simp only
    rw [h3 rfl, hiv]
    rfl
  | _ => simp [BSmtLibSpec.Lexer.Outcome.isFinished] at hfin

end BSmtLib.Facts.Proofs.Lexer.Consumers.VReset
